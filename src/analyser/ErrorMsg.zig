const std = @import("std");
const types = @import("../lsp.zig");
const offsets = @import("../offsets.zig");

const InternPool = @import("InternPool.zig");
const Index = InternPool.Index;
const Key = InternPool.Key;

const ErrorMsg = @This();

pub const Data = union(enum) {
    /// zig: expected type 'type', found '{}'
    expected_type_type: struct {
        actual: Index,
    },
    /// zig: expected type '{}', found '{}'
    expected_type: struct {
        expected_type: Index,
        actual: Index,
    },
    /// zig: comparison of '{}' with null
    compare_eq_with_null: struct {
        non_null_type: Index,
    },
    /// zig: tried to unwrap optional of type `{}` which was '{}'
    invalid_optional_unwrap: struct {
        operand: Index,
    },
    /// zig: expected optional type, found '{}'
    expected_optional_type: struct {
        actual: Index,
    },
    /// zig: expected error set type, found '{}'
    expected_error_set_type: struct {
        actual: Index,
    },
    /// zig: expected pointer, found '{}'
    expected_pointer_type: struct {
        actual: Index,
    },
    /// zig: type '{}' does not support indexing
    /// zig: operand must be an array, slice, tuple, or vector
    expected_indexable_type: struct {
        actual: Index,
    },
    /// zig: `{}` has no member '{s}'
    /// zig: `{}` does not support field access
    unknown_field: struct {
        accessed_ty: Index,
        field_name: []const u8,
    },
};

loc: offsets.Loc,
data: Data,

pub fn message(
    self: ErrorMsg,
    allocator: std.mem.Allocator,
    ip: *const InternPool,
) error{OutOfMemory}![]u8 {
    return switch (self.data) {
        .expected_type_type => |info| std.fmt.allocPrint(
            allocator,
            "expected type 'type', found '{}'",
            .{ip.typeOf(info.actual).fmt(ip)},
        ),
        .expected_type => |info| std.fmt.allocPrint(
            allocator,
            "expected type '{}', found '{}'",
            .{ info.expected_type.fmt(ip), ip.typeOf(info.actual).fmt(ip) },
        ),
        .compare_eq_with_null => |info| std.fmt.allocPrint(
            allocator,
            "comparison of '{}' with null",
            .{info.non_null_type.fmt(ip)},
        ),
        .invalid_optional_unwrap => |info| blk: {
            const operand_ty = ip.typeOf(info.operand);
            const payload_ty = ip.indexToKey(operand_ty).optional_type.payload_type;
            break :blk std.fmt.allocPrint(
                allocator,
                "tried to unwrap optional of type `{}` which was {}",
                .{ payload_ty.fmt(ip), info.operand.fmt(ip) },
            );
        },
        .expected_optional_type => |info| std.fmt.allocPrint(
            allocator,
            "expected optional type, found '{}'",
            .{info.actual.fmt(ip)},
        ),
        .expected_error_set_type => |info| std.fmt.allocPrint(
            allocator,
            "expected error set type, found '{}'",
            .{info.actual.fmt(ip)},
        ),
        .expected_pointer_type => |info| std.fmt.allocPrint(
            allocator,
            "expected pointer, found '{}'",
            .{info.actual.fmt(ip)},
        ),
        .expected_indexable_type => |info| std.fmt.allocPrint(
            allocator,
            "type '{}' does not support indexing",
            .{info.actual.fmt(ip)},
        ),
        .unknown_field => |info| if (ip.canHaveFields(info.accessed_ty))
            std.fmt.allocPrint(
                allocator,
                "`{}` has no member '{s}'",
                .{ info.accessed_ty.fmt(ip), info.field_name },
            )
        else
            std.fmt.allocPrint(
                allocator,
                "`{}` does not support field access",
                .{info.accessed_ty.fmt(ip)},
            ),
    };
}
