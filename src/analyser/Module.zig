const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const log = std.log.scoped(.zls_module);
const Ast = std.zig.Ast;

const Module = @This();
pub const DocumentStore = @import("../DocumentStore.zig");
pub const Handle = DocumentStore.Handle;
const Zir = @import("../stage2/Zir.zig");
const AstGen = @import("../stage2/AstGen.zig");

const InternPool = @import("InternPool.zig");
const Decl = InternPool.Decl;
const DeclIndex = InternPool.DeclIndex;
const OptionalDeclIndex = InternPool.OptionalDeclIndex;
const Sema = @import("Sema.zig");

gpa: Allocator,
ip: *InternPool,
// allocated_decls: std.SegmentedList(Decl, 0) = .{},
allocated_namespaces: std.SegmentedList(Namespace, 0) = .{},
document_store: *DocumentStore,

pub fn init(allocator: Allocator, ip: *InternPool, document_store: *DocumentStore) Module {
    return .{
        .gpa = allocator,
        .ip = ip,
        .document_store = document_store,
    };
}

pub fn deinit(mod: *Module) void {
    // mod.allocated_decls.deinit(mod.gpa);
    mod.allocated_namespaces.deinit(mod.gpa);
    mod.* = undefined;
}

pub fn relativeToNodeIndex(decl: Decl, offset: i32) Ast.Node.Index {
    return @as(Ast.Node.Index, @bitCast(offset + @as(i32, @bitCast(decl.node_idx))));
}

pub fn zirBlockIndex(decl: *const Decl, mod: *Module) Zir.Inst.Index {
    assert(decl.zir_decl_index != 0);
    const zir = Module.getHandle(decl.*, mod).zir;
    return zir.extra[decl.zir_decl_index + 6];
}

pub fn getHandle(decl: Decl, mod: *Module) *Handle {
    return mod.namespacePtr(decl.src_namespace).handle;
}

pub const DeclAdapter = struct {
    mod: *Module,

    pub fn hash(self: @This(), s: []const u8) u32 {
        _ = self;
        return @as(u32, @truncate(std.hash.Wyhash.hash(0, s)));
    }

    pub fn eql(self: @This(), a: []const u8, b_decl_index: DeclIndex, b_index: usize) bool {
        _ = b_index;
        const b_decl = self.mod.declPtr(b_decl_index);
        return std.mem.eql(u8, a, std.mem.sliceTo(b_decl.name, 0));
    }
};

/// The container that structs, enums, unions, and opaques have.
pub const Namespace = struct {
    /// .none means root Namespace
    parent: InternPool.NamespaceIndex,
    handle: *Handle,
    /// Will be a struct, enum, union, or opaque.
    ty: InternPool.Index,
    decls: std.ArrayHashMapUnmanaged(DeclIndex, void, DeclContext, true) = .{},
    anon_decls: std.AutoArrayHashMapUnmanaged(DeclIndex, void) = .{},
    usingnamespace_set: std.AutoHashMapUnmanaged(DeclIndex, bool) = .{},

    pub const DeclContext = struct {
        module: *Module,

        pub fn hash(ctx: @This(), decl_index: DeclIndex) u32 {
            const decl = ctx.module.declPtr(decl_index);
            return @as(u32, @truncate(std.hash.Wyhash.hash(0, std.mem.sliceTo(decl.name, 0))));
        }

        pub fn eql(ctx: @This(), a_decl_index: DeclIndex, b_decl_index: DeclIndex, b_index: usize) bool {
            _ = b_index;
            const a_decl = ctx.module.declPtr(a_decl_index);
            const b_decl = ctx.module.declPtr(b_decl_index);
            return std.mem.eql(u8, a_decl.name, b_decl.name);
        }
    };

    // This renders e.g. "std.fs.Dir.OpenOptions"
    pub fn renderFullyQualifiedName(
        ns: Namespace,
        mod: *Module,
        name: []const u8,
        writer: anytype,
    ) @TypeOf(writer).Error!void {
        if (ns.parent) |parent| {
            const decl_index = ns.getDeclIndex();
            const decl = mod.declPtr(decl_index);
            try parent.renderFullyQualifiedName(mod, std.mem.sliceTo(decl.name, 0), writer);
        } else {
            try ns.handle.renderFullyQualifiedName(writer);
        }
        if (name.len != 0) {
            try writer.writeAll(".");
            try writer.writeAll(name);
        }
    }

    pub fn getDeclIndex(ns: Namespace, mod: *Module) DeclIndex {
        return mod.ip.getStruct(mod.ip.indexToKey(ns.ty).struct_type).owner_decl.unwrap().?;
    }
};

pub fn allocateNewDecl(
    mod: *Module,
    namespace: InternPool.NamespaceIndex,
    src_node: Ast.Node.Index,
) Allocator.Error!DeclIndex {
    const decl: *Decl = try mod.ip.decls.addOne(mod.gpa);
    const decl_index = @as(DeclIndex, @enumFromInt(mod.ip.decls.len - 1));

    decl.* = .{
        .name = undefined,
        .index = .none,
        .alignment = undefined,
        .address_space = .generic,
        .src_namespace = namespace,
        .node_idx = src_node,
        .src_line = undefined,
        .zir_decl_index = 0,
        .analysis = .unreferenced,
        .is_pub = false,
        .is_exported = false,
        .kind = .anon,
    };

    return decl_index;
}

pub fn createNamespace(mod: *Module, namespace: Namespace) Allocator.Error!InternPool.NamespaceIndex {
    try mod.allocated_namespaces.append(mod.gpa, namespace);
    const namespace_index = @as(InternPool.NamespaceIndex, @enumFromInt(mod.allocated_namespaces.len - 1));

    return namespace_index;
}

pub fn destroyNamespace(mod: *Module, namespace_index: InternPool.NamespaceIndex) void {
    const gpa = mod.gpa;

    const ns = mod.namespacePtr(namespace_index);

    var decls = ns.decls;
    ns.decls = .{};

    var anon_decls = ns.anon_decls;
    ns.anon_decls = .{};

    for (decls.keys()) |decl_index| {
        mod.destroyDecl(decl_index);
    }
    decls.deinit(gpa);

    for (anon_decls.keys()) |key| {
        mod.destroyDecl(key);
    }
    anon_decls.deinit(gpa);

    var usingnamespaces = ns.usingnamespace_set;
    ns.usingnamespace_set = .{};
    usingnamespaces.deinit(gpa);
}

pub fn destroyDecl(mod: *Module, decl_index: DeclIndex) void {
    const gpa = mod.gpa;
    const decl = mod.declPtr(decl_index);
    if (decl.index != .none) {
        const namespace = mod.ip.getNamespace(decl.index);
        if (namespace != .none) {
            mod.destroyNamespace(namespace);
        }
    }
    gpa.free(decl.name);
    decl.* = undefined;
}

pub fn declPtr(mod: *Module, decl_index: DeclIndex) *Decl {
    return mod.ip.getDeclMut(decl_index);
}

pub fn declIsRoot(mod: *Module, decl_index: DeclIndex) bool {
    const decl = mod.declPtr(decl_index);
    if (decl.src_namespace != .none)
        return false;
    const namespace = mod.namespacePtr(decl.src_namespace);
    return decl_index == namespace.getDeclIndex(mod);
}

pub fn namespacePtr(mod: *Module, namespace_index: InternPool.NamespaceIndex) *Namespace {
    return mod.allocated_namespaces.at(@intFromEnum(namespace_index));
}

pub fn get(mod: *Module, key: InternPool.Key) Allocator.Error!InternPool.Index {
    return mod.ip.get(mod.gpa, key);
}

pub fn semaFile(mod: *Module, handle: *Handle) Allocator.Error!void {
    // TODO also support .outdated which may required require storing the old Ast as well
    assert(handle.zir_status == .done);
    assert(handle.root_decl == .none);

    const struct_index = try mod.ip.createStruct(mod.gpa, .{
        .fields = .{},
        .owner_decl = undefined, // set below
        .zir_index = Zir.main_struct_inst,
        .namespace = undefined, // set below
        .layout = .Auto,
        .backing_int_ty = .none,
        .status = .none,
    });
    const struct_ty = try mod.get(.{ .struct_type = struct_index });

    const namespace_index = try mod.createNamespace(.{
        .parent = .none,
        .handle = handle,
        .ty = struct_ty,
    });

    const decl_index = try mod.allocateNewDecl(namespace_index, 0);
    const decl = mod.declPtr(decl_index);

    const struct_obj = mod.ip.getStructMut(struct_index);
    struct_obj.owner_decl = decl_index.toOptional();
    struct_obj.namespace = namespace_index;

    handle.root_decl = decl_index.toOptional();
    decl.name = try mod.gpa.dupe(u8, handle.uri); // TODO
    decl.index = struct_ty;
    decl.alignment = 0;
    decl.analysis = .in_progress;
    decl.is_pub = true;
    decl.is_exported = false;
    decl.src_line = 0;

    var arena = std.heap.ArenaAllocator.init(mod.gpa);
    defer arena.deinit();

    var sema = Sema{
        .mod = mod,
        .gpa = mod.gpa,
        .arena = arena.allocator(),
        .code = handle.zir,
    };
    defer sema.deinit();

    try sema.analyzeStructDecl(decl, Zir.main_struct_inst, struct_obj);
    decl.analysis = .complete;
}

pub fn semaDecl(mod: *Module, decl_index: DeclIndex) Allocator.Error!void {
    const decl = mod.declPtr(decl_index);
    decl.analysis = .in_progress;

    const namespace = mod.namespacePtr(decl.src_namespace);
    const handle = namespace.handle;
    const zir = handle.zir;
    const zir_datas = zir.instructions.items(.data);
    assert(handle.zir_status == .done);

    var arena = std.heap.ArenaAllocator.init(mod.gpa);
    defer arena.deinit();

    var sema = Sema{
        .mod = mod,
        .gpa = mod.gpa,
        .arena = arena.allocator(),
        .code = handle.zir,
    };
    defer sema.deinit();

    if (mod.declIsRoot(decl_index)) {
        log.debug("semaDecl root {d} ({s})", .{ @intFromEnum(decl_index), decl.name });
        const struct_ty = mod.ip.indexToKey(decl.index).struct_type;
        const struct_obj = mod.ip.getStructMut(struct_ty);
        try sema.analyzeStructDecl(decl, struct_obj.zir_index, struct_obj);
        decl.analysis = .complete;
        return;
    }
    log.debug("semaDecl {d} ({s})", .{ @intFromEnum(decl_index), decl.name });

    var block_scope: Sema.Block = .{
        .parent = null,
        .src_decl = decl_index,
        .namespace = decl.src_namespace,
        .is_comptime = true,
    };
    defer block_scope.params.deinit(mod.gpa);
    defer if (block_scope.label) |l| l.merges.deinit(sema.gpa);

    const zir_block_index = Module.zirBlockIndex(decl, mod);
    const inst_data = zir_datas[zir_block_index].pl_node;
    const extra = zir.extraData(Zir.Inst.Block, inst_data.payload_index);
    const body = zir.extra[extra.end..][0..extra.data.body_len];
    decl.index = if (try sema.analyzeBodyBreak(&block_scope, body)) |break_data| sema.resolveIndex(break_data.operand) else .none;
    decl.analysis = .complete;

    try sema.addDbgVar(&block_scope, decl.index, false, decl.name);
}
