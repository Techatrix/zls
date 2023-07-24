const std = @import("std");

const StringPool = @This();

bytes: std.ArrayListUnmanaged(u8) = .{},
map: std.HashMapUnmanaged(u32, void, std.hash_map.StringIndexContext, std.hash_map.default_max_load_percentage) = .{},

pub const String = enum(u32) {
    empty = 0,
    _,

    pub fn toString(self: String) String {
        return @enumFromInt(@intFromEnum(self));
    }

    pub fn toOptional(self: String) OptionalString {
        return @enumFromInt(@intFromEnum(self));
    }
};

pub const OptionalString = enum(u32) {
    empty = 0,
    none = std.math.maxInt(u32),
    _,

    pub fn unwrap(self: OptionalString) ?String {
        if (self == .none) return null;
        return @enumFromInt(@intFromEnum(self));
    }
};

pub fn deinit(pool: *StringPool, allocator: std.mem.Allocator) void {
    pool.bytes.deinit(allocator);
    pool.map.deinit(allocator);
    pool.* = undefined;
}

pub fn getOrPutString(pool: *StringPool, allocator: std.mem.Allocator, str: []const u8) error{OutOfMemory}!String {
    const start_index = @as(u32, @intCast(pool.bytes.items.len));
    if ((pool.bytes.items.len + 1) +| str.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    try pool.bytes.ensureUnusedCapacity(allocator, str.len + 1);
    pool.bytes.appendSliceAssumeCapacity(str);
    pool.bytes.appendAssumeCapacity(0);

    const key: []const u8 = pool.bytes.items[start_index..];
    const gop = try pool.map.getOrPutContextAdapted(allocator, key, std.hash_map.StringIndexAdapter{
        .bytes = &pool.bytes,
    }, std.hash_map.StringIndexContext{
        .bytes = &pool.bytes,
    });
    if (gop.found_existing) {
        pool.bytes.shrinkRetainingCapacity(start_index);
        return @enumFromInt(gop.key_ptr.*);
    } else {
        gop.key_ptr.* = start_index;
        return @enumFromInt(start_index);
    }
}

pub fn stringToSlice(pool: StringPool, index: String) [:0]const u8 {
    const string_bytes = pool.bytes.items;
    const start = @intFromEnum(index);
    var end: usize = start;
    while (string_bytes[end] != 0) end += 1;
    return string_bytes[start..end :0];
}

test StringPool {
    const gpa = std.testing.allocator;
    var pool = StringPool{};
    defer pool.deinit(gpa);

    const str = "All Your Codebase Are Belong To Us";
    const index = try pool.getOrPutString(gpa, str);
    try std.testing.expectEqualStrings(str, pool.stringToSlice(index));
}
