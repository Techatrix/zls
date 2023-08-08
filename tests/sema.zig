const std = @import("std");
const zls = @import("zls");
const builtin = @import("builtin");

const helper = @import("helper.zig");
const ErrorBuilder = @import("ErrorBuilder.zig");

const Module = zls.analyser.Module;
const Sema = zls.analyser.Sema;
const InternPool = zls.analyser.InternPool;
const Index = InternPool.Index;
const Key = InternPool.Key;
const Analyser = zls.Analyser;
const offsets = zls.offsets;

const allocator: std.mem.Allocator = std.testing.allocator;

test "semantic analysis" {
    const current_file_dir = comptime std.fs.path.dirname(@src().file).?;
    const path = try std.fs.path.join(allocator, &.{ current_file_dir, "sema" });
    defer allocator.free(path);

    var dir = try std.fs.cwd().openIterableDir(path, .{});
    defer dir.close();

    try testSemanticAnalysisRecursiveDir(dir, true);
}

test "semantic analysis - fuzz on ZLS codebase" {
    const current_file_path = comptime std.fs.path.dirname(@src().file).?;
    const path = try std.fs.path.resolve(allocator, &.{ current_file_path, "..", "src" });
    defer allocator.free(path);

    var dir = try std.fs.cwd().openIterableDir(path, .{});
    defer dir.close();

    try testSemanticAnalysisRecursiveDir(dir, false);
}

fn testSemanticAnalysisRecursiveDir(dir: std.fs.IterableDir, check_annotations: bool) !void {
    var iter = dir.iterateAssumeFirstIteration();
    while (try iter.next()) |entry| {
        switch (entry.kind) {
            .file => {
                if (!std.mem.eql(u8, std.fs.path.extension(entry.name), ".zig")) continue;
                if (std.mem.eql(u8, entry.name, "Module.zig")) continue; // TODO
                const file = try dir.dir.openFile(entry.name, .{});
                defer file.close();
                var file_content = try file.readToEndAlloc(allocator, std.math.maxInt(u32));
                defer allocator.free(file_content);

                // var out_buffer: [128]u8 = undefined;
                // std.debug.print("file: {s}\n", .{try dir.dir.realpath(entry.name, &out_buffer)});

                try testSemanticAnalysis(file_content, check_annotations);
            },
            .directory => {
                var sub_dir = try dir.dir.openIterableDir(entry.name, .{});
                defer sub_dir.close();
                try testSemanticAnalysisRecursiveDir(sub_dir, check_annotations);
            },
            else => {},
        }
    }
}

fn testSemanticAnalysis(source: []const u8, check_annotations: bool) !void {
    // a InternPool stores types and values
    var ip = try InternPool.init(allocator);
    defer ip.deinit(allocator);

    // create a Module that stores data which is used across multiple files like declarations
    var mod = Module.init(allocator, &ip, undefined);
    defer mod.deinit();

    var document_store = zls.DocumentStore{
        .allocator = allocator,
        .config = &zls.Config{
            .analysis_backend = .astgen_analyser,
            .enable_ast_check_diagnostics = true,
            .prefer_ast_check_as_child_process = false,
        },
        .runtime_zig_version = &@as(?zls.ZigVersionWrapper, null),
        .mod = &mod,
    };
    defer document_store.deinit();
    std.debug.assert(document_store.wantZir());

    const test_uri: []const u8 = switch (builtin.os.tag) {
        .windows => "file:///C:\\test.zig",
        else => "file:///test.zig",
    };

    mod.document_store = &document_store;

    // add the given source file to the document store
    // this will also analyse all declarations in the top-level/root scope
    _ = try document_store.openDocument(test_uri, source);
    const handle = document_store.handles.get(test_uri).?;
    std.debug.assert(handle.zir_status == .done);
    std.debug.assert(handle.tree.errors.len == 0);
    std.debug.assert(!handle.zir.hasCompileErrors());
    std.debug.assert(handle.root_decl != .none);

    // get the decl that represents the top-level/root scope
    const decl_index: InternPool.DeclIndex = handle.root_decl.unwrap().?;
    const decl: *InternPool.Decl = mod.declPtr(decl_index);

    // every zig file is also a struct
    const struct_index: InternPool.StructIndex = mod.ip.indexToKey(decl.index).struct_type;
    const struct_obj: *const InternPool.Struct = mod.ip.getStruct(struct_index);
    const namespace: *Module.Namespace = mod.namespacePtr(struct_obj.namespace);
    _ = namespace;

    // this will print all top-level declarations and their value
    // for (namespace.decls.keys()) |namespace_decl_index| {
    //     const namespace_decl = mod.declPtr(namespace_decl_index);
    //     std.debug.print("{s:<18} {}\n", .{ namespace_decl.name, namespace_decl.index.fmtDebug(mod.ip) });
    // }

    var arena = std.heap.ArenaAllocator.init(mod.gpa);
    defer arena.deinit();

    // `Sema` stores temporary information that is required during semantic analysis
    var sema = Sema{
        .mod = &mod,
        .gpa = allocator,
        .arena = arena.allocator(),
        .code = handle.zir,
    };
    defer sema.deinit();

    // this will resolve the types of all top-level container fields
    // try sema.resolveTypeFieldsStruct(struct_obj);

    if (!check_annotations) return;

    var error_builder = ErrorBuilder.init(allocator);
    defer error_builder.deinit();
    errdefer error_builder.writeDebug();

    try error_builder.addFile(test_uri, source);

    const annotations = try helper.collectAnnotatedSourceLocations(allocator, source);
    defer allocator.free(annotations);

    for (annotations) |annotation| {
        const identifier_loc = annotation.loc;
        const identifier = offsets.locToSlice(source, identifier_loc);
        const test_item = try parseAnnotatedSourceLoc(annotation);

        if (test_item.expected_error) |expected_error| {
            const actual_error: zls.DocumentStore.ErrorMessage = for (handle.analysis_errors.items) |actual_error| {
                if (std.meta.eql(actual_error.loc, annotation.loc)) break actual_error;
            } else return error.ErrorNotFound; // definetly not a confusing error name

            if (!std.mem.eql(u8, expected_error, actual_error.message)) {
                try error_builder.msgAtLoc("expected error message '{s}' but got '{s}'", test_uri, annotation.loc, .err, .{
                    expected_error,
                    actual_error.message,
                });
                return error.WrongError;
            }

            continue;
        }

        const found_decl_index = lookupDeclIndex(&mod, handle.*, identifier_loc) orelse {
            try error_builder.msgAtLoc("couldn't find identifier `{s}` here", test_uri, identifier_loc, .err, .{identifier});
            return error.IdentifierNotFound;
        };

        if (test_item.expected_type) |expected_type| {
            const val: InternPool.Index = found_decl_index;
            const ty: InternPool.Index = mod.ip.typeOf(val);
            const actual_type = try std.fmt.allocPrint(allocator, "{}", .{ty.fmt(mod.ip)});
            defer allocator.free(actual_type);
            if (!std.mem.eql(u8, expected_type, actual_type)) {
                try error_builder.msgAtLoc("expected type `{s}` but got `{s}`", test_uri, identifier_loc, .err, .{
                    expected_type,
                    actual_type,
                });
                return error.WrongType;
            }
        }

        if (test_item.expected_value) |expected_value| {
            const val: InternPool.Index = found_decl_index;
            const actual_value = try std.fmt.allocPrint(allocator, "{}", .{val.fmt(mod.ip)});
            defer allocator.free(actual_value);
            if (!std.mem.eql(u8, expected_value, actual_value)) {
                try error_builder.msgAtLoc("expected value `{s}` but got `{s}`", test_uri, identifier_loc, .err, .{
                    expected_value,
                    actual_value,
                });
                return error.WrongValue;
            }
        }
    }
}

fn lookupDeclIndex(mod: *Module, handle: zls.DocumentStore.Handle, identifier_loc: offsets.Loc) ?InternPool.Index {
    const identifier = offsets.locToSlice(handle.tree.source, identifier_loc);
    const symbol = Analyser.Declaration.Key{ .kind = .variable, .name = identifier };
    if (Analyser.lookupDeclaration(handle.document_scope, symbol, identifier_loc.start)) |decl| {
        switch (decl.*) {
            .intern_pool_index => |payload| {
                std.debug.assert(std.mem.eql(u8, identifier, offsets.tokenToSlice(handle.tree, payload.name)));
                return payload.index;
            },
            else => {},
        }
    }

    // this is not how you are supposed to lookup identifiers but its good enough for now
    var decl_it = mod.ip.decls.constIterator(0);
    var index: u32 = 0;
    while (decl_it.next()) |decl| : (index += 1) {
        if (!std.mem.eql(u8, decl.name, identifier)) continue;
        return decl.index;
    }
    return null;
}

const TestItem = struct {
    loc: offsets.Loc,
    expected_type: ?[]const u8 = null,
    expected_value: ?[]const u8 = null,
    expected_error: ?[]const u8 = null,
};

fn parseAnnotatedSourceLoc(annotation: helper.AnnotatedSourceLoc) error{InvalidTestItem}!TestItem {
    const str = annotation.content;

    if (std.mem.startsWith(u8, str, "error:")) {
        return .{
            .loc = annotation.loc,
            .expected_error = std.mem.trim(u8, str["error:".len..], &std.ascii.whitespace),
        };
    }

    if (!std.mem.startsWith(u8, str, "(")) return error.InvalidTestItem;
    const expected_type_start = 1;
    const expected_type_end = expected_type_start + (findClosingBrace(str[expected_type_start..]) orelse return error.InvalidTestItem);

    if (!std.mem.startsWith(u8, str[expected_type_end + 1 ..], "(")) return error.InvalidTestItem;
    const expected_value_start = expected_type_end + 2;
    const expected_value_end = expected_value_start + (findClosingBrace(str[expected_value_start..]) orelse return error.InvalidTestItem);

    const expected_type = std.mem.trim(
        u8,
        offsets.locToSlice(str, .{ .start = expected_type_start, .end = expected_type_end }),
        &std.ascii.whitespace,
    );
    const expected_value = std.mem.trim(
        u8,
        offsets.locToSlice(str, .{ .start = expected_value_start, .end = expected_value_end }),
        &std.ascii.whitespace,
    );

    return .{
        .loc = annotation.loc,
        .expected_type = if (expected_type.len != 0) expected_type else null,
        .expected_value = if (expected_value.len != 0) expected_value else null,
    };
}

fn findClosingBrace(source: []const u8) ?usize {
    var depth: usize = 0;
    for (source, 0..) |c, i| {
        switch (c) {
            '(' => depth += 1,
            ')' => {
                if (depth == 0) return i;
                depth -= 1;
            },
            else => continue,
        }
    }
    return null;
}
