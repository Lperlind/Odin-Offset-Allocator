package offset_allocator

import "base:runtime"
import "base:intrinsics"
import "core:testing"

Allocator :: runtime.Allocator
Allocator_Error :: runtime.Allocator_Error

NUM_TOP_BINS :: 32
BINS_PER_LEAF :: 8
TOP_BINS_INDEX_SHIFT :: 3
LEAF_BINS_INDEX_MASK :: 0x7
NUM_LEAF_BINS :: NUM_TOP_BINS * BINS_PER_LEAF

SMALL_FLOAT_MANTISSA_BITS :: 3
SMALL_FLOAT_MANTISSA_VALUE :: 1 << SMALL_FLOAT_MANTISSA_BITS
SMALL_FLOAT_MANTISSA_MASK :: SMALL_FLOAT_MANTISSA_VALUE - 1

Node_Index :: distinct u32
NODE_UNUSED :: Node_Index(0xFFFFFFFF)

Offset_Allocator_Node :: struct {
    offset: u32,
    size: u32,
    bin_next: Node_Index,
    bin_prev: Node_Index,
    neighbour_next: Node_Index,
    neighbour_prev: Node_Index,
    used: bool,
}

Offset_Allocator_Allocation :: struct {
    offset: u32,
    meta_data: Node_Index,
}

Offset_Allocator_Storage_Report :: struct {
    total_free_space: u32,
    largest_free_space: u32,
}

Offset_Allocator :: struct {
    size: u32,
    max_allocs: u32,
    free_storage: u32,
    used_bins_top: u32,
    used_bins: [NUM_TOP_BINS]u8,
    bin_indices: [NUM_LEAF_BINS]Node_Index,

    nodes: []Offset_Allocator_Node,
    free_nodes: []Node_Index,
    free_offset: u32,

    allocator: Allocator,
}

offset_allocator_make :: proc(size: u32, max_allocs: u32, allocator: Allocator) -> (_result: Offset_Allocator, _err: Allocator_Error) {
    result: Offset_Allocator
    result.size = size
    result.max_allocs = max_allocs
    result.free_offset = max_allocs - 1
    data := make(#soa[]struct { node: Offset_Allocator_Node, index: Node_Index }, max_allocs) or_return
    result.nodes, result.free_nodes = soa_unzip(data)

    result.bin_indices = NODE_UNUSED

    for i in 0..<max_allocs {
        result.free_nodes[i] = Node_Index(max_allocs - i - 1)
    }


    _offset_allocator_insert_node_into_bin(&result, size, 0)
    result.allocator = allocator
    return result, nil
}

offset_allocator_delete :: proc(allocator: ^Offset_Allocator) {
    delete(soa_zip(allocator.nodes, allocator.free_nodes), allocator.allocator)
    allocator ^= {}
}

offset_allocator_storage_report :: proc(allocator: Offset_Allocator) -> (Offset_Allocator_Storage_Report) {
    result: Offset_Allocator_Storage_Report
    if allocator.free_offset > 0 {
        result.total_free_space = allocator.free_storage
        if allocator.used_bins_top != 0 {
            top_bin_index := u32(31) - intrinsics.count_leading_zeros(allocator.used_bins_top)
            leaf_bin_index := 31 - intrinsics.count_leading_zeros(u32(allocator.used_bins[top_bin_index]))
            result.largest_free_space = small_float_float_to_uint((top_bin_index << TOP_BINS_INDEX_SHIFT) | leaf_bin_index)
        }
    }
    return result
}

offset_allocator_allocate :: proc(allocator: ^Offset_Allocator, size: u32) -> (Offset_Allocator_Allocation, bool) {
    if allocator.free_offset == 0 {
        return {}, false
    }

    min_bin_index := small_float_uint_to_float_round_up(size)

    min_top_bin_index := min_bin_index >> TOP_BINS_INDEX_SHIFT
    min_leaf_bin_index := min_bin_index & LEAF_BINS_INDEX_MASK

    top_bin_index := min_top_bin_index
    leaf_bin_index := u32(0xFFFFFFFF)

    if (allocator.used_bins_top & (1 << top_bin_index)) != 0 {
        leaf_bin_index = _offset_allocator_find_lowest_set_bit_after(u32(allocator.used_bins[top_bin_index]), min_leaf_bin_index)
    }

    if leaf_bin_index == 0xFFFFFFFF {
        top_bin_index = _offset_allocator_find_lowest_set_bit_after(allocator.used_bins_top, min_top_bin_index + 1)

        if top_bin_index == 0xFFFFFFFF {
            return {}, false
        }
        leaf_bin_index = intrinsics.count_trailing_zeros(u32(allocator.used_bins[top_bin_index]))
    }

    bin_index := (top_bin_index << TOP_BINS_INDEX_SHIFT) | leaf_bin_index

    node_index := allocator.bin_indices[bin_index]
    node := &allocator.nodes[node_index]
    node_total_size := node.size
    node.size = size
    node.used = true
    allocator.bin_indices[bin_index] = node.bin_next
    if node.bin_next != NODE_UNUSED {
        allocator.nodes[node.bin_next].bin_prev = NODE_UNUSED
    }
    allocator.free_storage -= node_total_size

    if allocator.bin_indices[bin_index] == NODE_UNUSED {
        allocator.used_bins[top_bin_index] &= ~(1 << leaf_bin_index)
        if allocator.used_bins[top_bin_index] == 0 {
                allocator.used_bins_top &= ~(1 << top_bin_index)
        }
    }

    remainder_size := node_total_size - size
    if remainder_size > 0 {
        new_node_index := _offset_allocator_insert_node_into_bin(allocator, remainder_size, node.offset + size)
        if node.neighbour_next != NODE_UNUSED {
            allocator.nodes[node.neighbour_next].neighbour_prev = new_node_index
        }
        allocator.nodes[new_node_index].neighbour_prev = node_index
        allocator.nodes[new_node_index].neighbour_next = node.neighbour_next
        node.neighbour_next = new_node_index
    }

    return { node.offset, node_index }, true
}


offset_allocator_free :: proc(allocator: ^Offset_Allocator, node_index: Node_Index) {
    node := &allocator.nodes[node_index]
    assert(node.used)

    offset := node.offset
    size := node.size

    if node.neighbour_prev != NODE_UNUSED && ! allocator.nodes[node.neighbour_prev].used {
        prev_node := &allocator.nodes[node.neighbour_prev]
        offset = prev_node.offset
        size += prev_node.size

        _offset_allocator_remove_node_from_bin(allocator, node.neighbour_prev)

        assert(prev_node.neighbour_next == node_index)
        node.neighbour_prev = prev_node.neighbour_prev
    }

    if node.neighbour_next != NODE_UNUSED && ! allocator.nodes[node.neighbour_next].used {
        next_node := &allocator.nodes[node.neighbour_next]
        size += next_node.size

        _offset_allocator_remove_node_from_bin(allocator, node.neighbour_next)

        assert(next_node.neighbour_prev == node_index)
        node.neighbour_next = next_node.neighbour_next
    }

    neighbour_prev := node.neighbour_prev
    neighbour_next := node.neighbour_next

    allocator.free_offset += 1
    allocator.free_nodes[allocator.free_offset] = node_index

    combined_node_index := _offset_allocator_insert_node_into_bin(allocator, size, offset)

    if neighbour_next != NODE_UNUSED {
        allocator.nodes[combined_node_index].neighbour_next = neighbour_next
        allocator.nodes[neighbour_next].neighbour_prev = combined_node_index
    }

    if neighbour_prev != NODE_UNUSED {
        allocator.nodes[combined_node_index].neighbour_prev = neighbour_prev
        allocator.nodes[neighbour_prev].neighbour_next = combined_node_index
    }
}

_offset_allocator_find_lowest_set_bit_after :: proc(bit_mask: u32, start_bit_index: u32) -> u32 {
    mask_before_start_index := u32((1 << start_bit_index) - 1)
    mask_after_start_index := ~mask_before_start_index
    bits_after := bit_mask & mask_after_start_index
    if bits_after == 0 {
        return 0xFFFFFFFF
    }
    return intrinsics.count_trailing_zeros(bits_after)
}

_offset_allocator_insert_node_into_bin :: proc(allocator: ^Offset_Allocator, size: u32, data_offset: u32) -> Node_Index {
    bin_index := small_float_uint_to_float_round_down(size)
    top_bin_index := bin_index >> TOP_BINS_INDEX_SHIFT
    leaf_bin_index := bin_index & LEAF_BINS_INDEX_MASK

    if allocator.bin_indices[bin_index] == NODE_UNUSED {
        allocator.used_bins[top_bin_index] |= u8(1 << leaf_bin_index)
        allocator.used_bins_top |= 1 << top_bin_index
    }

    top_node_index := allocator.bin_indices[bin_index]
    node_index := allocator.free_nodes[allocator.free_offset]
    allocator.free_offset -= 1

    allocator.nodes[node_index] = { data_offset, size, top_node_index, NODE_UNUSED, NODE_UNUSED, NODE_UNUSED, false }
    if top_node_index != NODE_UNUSED {
        allocator.nodes[top_node_index].bin_prev = node_index
    }
    allocator.bin_indices[bin_index] = node_index
    allocator.free_storage += size
    return node_index
}

_offset_allocator_remove_node_from_bin :: proc(allocator: ^Offset_Allocator, node_index: Node_Index) {
    node := &allocator.nodes[node_index]
    if node.bin_prev != NODE_UNUSED {
        allocator.nodes[node.bin_prev].bin_next = node.bin_next
        if node.bin_next != NODE_UNUSED {
            allocator.nodes[node.bin_next].bin_prev = node.bin_prev
        }
    } else {
        bin_index := small_float_uint_to_float_round_down(node.size)

        top_bin_index := bin_index >> TOP_BINS_INDEX_SHIFT
        leaf_bin_index := bin_index & LEAF_BINS_INDEX_MASK

        allocator.bin_indices[bin_index] = node.bin_next
        if node.bin_next != NODE_UNUSED {
            allocator.nodes[node.bin_next].bin_prev = NODE_UNUSED
        }

        if allocator.bin_indices[bin_index] == NODE_UNUSED {
            allocator.used_bins[top_bin_index] &= ~(1 << leaf_bin_index)
            if allocator.used_bins[top_bin_index] == 0 {
                allocator.used_bins_top &= ~(1 << top_bin_index)
            }
        }
    }

    allocator.free_offset += 1
    allocator.free_nodes[allocator.free_offset] = node_index
    allocator.free_storage -= node.size
}

small_float_uint_to_float_round_up :: proc(size: u32) -> u32 {
    exp := u32(0)
    mantissa := u32(0)
    if size < SMALL_FLOAT_MANTISSA_VALUE {
        mantissa = size
    } else {
        leading_zeros := intrinsics.count_leading_zeros(size)
        highest_bit_set := 31 - leading_zeros
        mantissa_start_bit := highest_bit_set - SMALL_FLOAT_MANTISSA_BITS
        exp = mantissa_start_bit + 1
        mantissa = (size >> mantissa_start_bit) & SMALL_FLOAT_MANTISSA_MASK
        low_bits_mask := u32(1 << mantissa_start_bit) - 1
        if size & low_bits_mask != 0 {
            mantissa += 1
        }
    }
    return (exp << SMALL_FLOAT_MANTISSA_BITS) + mantissa
}

small_float_uint_to_float_round_down :: proc(size: u32) -> u32 {
    exp := u32(0)
    mantissa := u32(0)
    if size < SMALL_FLOAT_MANTISSA_VALUE {
        mantissa = size
    } else {
        leading_zeros := intrinsics.count_leading_zeros(size)
        highest_bit_set := 31 - leading_zeros
        mantissa_start_bit := highest_bit_set - SMALL_FLOAT_MANTISSA_BITS
        exp = mantissa_start_bit + 1
        mantissa = (size >> mantissa_start_bit) & SMALL_FLOAT_MANTISSA_MASK
    }
    return (exp << SMALL_FLOAT_MANTISSA_BITS) | mantissa
}

small_float_float_to_uint :: proc(value: u32) -> u32 {
    exp := value >> SMALL_FLOAT_MANTISSA_BITS
    mantissa := value & SMALL_FLOAT_MANTISSA_MASK
    if exp == 0 {
        return mantissa
    } else {
        return (mantissa | SMALL_FLOAT_MANTISSA_VALUE) << (exp - 1)
    }
}

@(test)
small_float_uint_to_float_test :: proc(t: ^testing.T) {
    precise_count := u32(17)
    for i in 0..<precise_count {
        round_up := small_float_uint_to_float_round_up(i)
        round_down := small_float_uint_to_float_round_down(i)
        testing.expect(t, round_up == i)
        testing.expect(t, round_down == i)
    }

    Number_Float_Up_Down :: struct {
        number, up, down: u32,
    }

    test_data := []Number_Float_Up_Down {
        { number = 17,      up = 17,  down = 16  },
        { number = 118,     up = 39,  down = 38  },
        { number = 1024,    up = 64,  down = 64  },
        { number = 65536,   up = 112, down = 112 },
        { number = 529445,  up = 137, down = 136 },
        { number = 1048575, up = 144, down = 143 },
    }

    for v in test_data {
        round_up := small_float_uint_to_float_round_up(v.number)
        round_down := small_float_uint_to_float_round_down(v.number)
        testing.expect(t, round_up == v.up)
        testing.expect(t, round_down == v.down)
    }
}

@(test)
small_float_float_to_uint_test :: proc(t: ^testing.T) {
    precise_count := u32(17)
    for i in 0..<precise_count {
        v := small_float_uint_to_float_round_up(i)
        testing.expect(t, v == i)
    }

    for i in 0..<u32(240) {
        v := small_float_float_to_uint(i)
        up := small_float_uint_to_float_round_up(v)
        down := small_float_uint_to_float_round_down(v)
        testing.expect(t, i == up)
        testing.expect(t, i == down)
    }
}

OFFSET_ALLOCATOR_TEST_SIZE :: 1024 * 1024 * 256
OFFSET_ALLOCATOR_MAX_ALLOCS :: 128 * 1024
@(test)
offset_allocator_simple_test :: proc(t: ^testing.T) {
    allocator, err := offset_allocator_make(OFFSET_ALLOCATOR_TEST_SIZE, OFFSET_ALLOCATOR_MAX_ALLOCS, context.allocator)
    testing.expect(t, err == nil)
    defer offset_allocator_delete(&allocator)

    a, a_ok := offset_allocator_allocate(&allocator, 0)
    b, b_ok := offset_allocator_allocate(&allocator, 1)
    c, c_ok := offset_allocator_allocate(&allocator, 123)
    d, d_ok := offset_allocator_allocate(&allocator, 1234)

    testing.expect(t, a_ok)
    testing.expect(t, b_ok)
    testing.expect(t, c_ok)
    testing.expect(t, d_ok)

    testing.expect(t, a.offset == 0)
    testing.expect(t, b.offset == 0)
    testing.expect(t, c.offset == 1)
    testing.expect(t, d.offset == 124)

    offset_allocator_free(&allocator, a.meta_data)
    offset_allocator_free(&allocator, b.meta_data)
    offset_allocator_free(&allocator, c.meta_data)
    offset_allocator_free(&allocator, d.meta_data)

    validate_all, validate_all_ok := offset_allocator_allocate(&allocator, OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, validate_all_ok)
    testing.expect(t, validate_all.offset == 0)
}

@(test)
offset_allocator_merge_trivial_test :: proc(t: ^testing.T) {
    allocator, err := offset_allocator_make(OFFSET_ALLOCATOR_TEST_SIZE, OFFSET_ALLOCATOR_MAX_ALLOCS, context.allocator)
    testing.expect(t, err == nil)
    defer offset_allocator_delete(&allocator)

    a, a_ok := offset_allocator_allocate(&allocator, 1337)
    testing.expect(t, a_ok)
    testing.expect(t, a.offset == 0)
    offset_allocator_free(&allocator, a.meta_data)

    a, a_ok = offset_allocator_allocate(&allocator, 1337)
    testing.expect(t, a_ok)
    testing.expect(t, a.offset == 0)
    offset_allocator_free(&allocator, a.meta_data)

    validate_all, validate_all_ok := offset_allocator_allocate(&allocator, OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, validate_all_ok)
    testing.expect(t, validate_all.offset == 0)
}

@(test)
offset_allocator_reuse_trivial_test :: proc(t: ^testing.T) {
    allocator, err := offset_allocator_make(OFFSET_ALLOCATOR_TEST_SIZE, OFFSET_ALLOCATOR_MAX_ALLOCS, context.allocator)
    testing.expect(t, err == nil)
    defer offset_allocator_delete(&allocator)

    a, a_ok := offset_allocator_allocate(&allocator, 1024)
    testing.expect(t, a_ok)
    testing.expect(t, a.offset == 0)

    b, b_ok := offset_allocator_allocate(&allocator, 3456)
    testing.expect(t, b_ok)
    testing.expect(t, b.offset == 1024)

    offset_allocator_free(&allocator, a.meta_data)

    c, c_ok := offset_allocator_allocate(&allocator, 1024)
    testing.expect(t, c_ok)
    testing.expect(t, c.offset == 0)

    offset_allocator_free(&allocator, b.meta_data)
    offset_allocator_free(&allocator, c.meta_data)

    validate_all, validate_all_ok := offset_allocator_allocate(&allocator, OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, validate_all_ok)
    testing.expect(t, validate_all.offset == 0)
}

@(test)
offset_allocator_reuse_complex_test :: proc(t: ^testing.T) {
    allocator, err := offset_allocator_make(OFFSET_ALLOCATOR_TEST_SIZE, OFFSET_ALLOCATOR_MAX_ALLOCS, context.allocator)
    testing.expect(t, err == nil)
    defer offset_allocator_delete(&allocator)

    a, a_ok := offset_allocator_allocate(&allocator, 1024)
    testing.expect(t, a_ok)
    testing.expect(t, a.offset == 0)

    b, b_ok := offset_allocator_allocate(&allocator, 3456)
    testing.expect(t, b_ok)
    testing.expect(t, b.offset == 1024)

    offset_allocator_free(&allocator, a.meta_data)

    c, c_ok := offset_allocator_allocate(&allocator, 2345)
    testing.expect(t, c_ok)
    testing.expect(t, c.offset == 1024 + 3456)

    d, d_ok := offset_allocator_allocate(&allocator, 456)
    testing.expect(t, d_ok)
    testing.expect(t, d.offset == 0)

    e, e_ok := offset_allocator_allocate(&allocator, 512)
    testing.expect(t, e_ok)
    testing.expect(t, e.offset == 456)

    report := offset_allocator_storage_report(allocator)
    testing.expect(t, report.total_free_space == OFFSET_ALLOCATOR_TEST_SIZE - 3456 - 2345 - 456 - 512)
    testing.expect(t, report.largest_free_space != report.total_free_space)

    offset_allocator_free(&allocator, b.meta_data)
    offset_allocator_free(&allocator, c.meta_data)
    offset_allocator_free(&allocator, d.meta_data)
    offset_allocator_free(&allocator, e.meta_data)


    validate_all, validate_all_ok := offset_allocator_allocate(&allocator, OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, validate_all_ok)
    testing.expect(t, validate_all.offset == 0)
}

@(test)
offset_allocator_zero_fragmentation_test :: proc(t: ^testing.T) {
    allocator, err := offset_allocator_make(OFFSET_ALLOCATOR_TEST_SIZE, OFFSET_ALLOCATOR_MAX_ALLOCS, context.allocator)
    testing.expect(t, err == nil)
    defer offset_allocator_delete(&allocator)

    allocations: [256]Offset_Allocator_Allocation
    for &a, i in allocations {
        ok: bool
        a, ok = offset_allocator_allocate(&allocator, 1024 * 1024)
        testing.expect(t, ok)
        testing.expect(t, a.offset == u32(i) * 1024 * 1024)
    }

    report := offset_allocator_storage_report(allocator)
    testing.expect(t, report.total_free_space == 0)
    testing.expect(t, report.largest_free_space == 0)

    offset_allocator_free(&allocator, allocations[243].meta_data)
    offset_allocator_free(&allocator, allocations[5].meta_data)
    offset_allocator_free(&allocator, allocations[123].meta_data)
    offset_allocator_free(&allocator, allocations[95].meta_data)

    offset_allocator_free(&allocator, allocations[151].meta_data)
    offset_allocator_free(&allocator, allocations[152].meta_data)
    offset_allocator_free(&allocator, allocations[153].meta_data)
    offset_allocator_free(&allocator, allocations[154].meta_data)

    ok := false
    allocations[243], ok = offset_allocator_allocate(&allocator, 1024 * 1024)
    testing.expect(t, ok)
    allocations[5], ok = offset_allocator_allocate(&allocator, 1024 * 1024)
    testing.expect(t, ok)
    allocations[123], ok = offset_allocator_allocate(&allocator, 1024 * 1024)
    testing.expect(t, ok)
    allocations[95], ok = offset_allocator_allocate(&allocator, 1024 * 1024)
    testing.expect(t, ok)
    allocations[151], ok = offset_allocator_allocate(&allocator, 1024 * 1024 * 4)
    testing.expect(t, ok)

    for a, i in allocations {
        if i < 152 || i > 154 {
            offset_allocator_free(&allocator, a.meta_data)
        }
    }

    report = offset_allocator_storage_report(allocator)
    testing.expect(t, report.total_free_space == OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, report.largest_free_space == OFFSET_ALLOCATOR_TEST_SIZE)

    validate_all, validate_all_ok := offset_allocator_allocate(&allocator, OFFSET_ALLOCATOR_TEST_SIZE)
    testing.expect(t, validate_all_ok)
    testing.expect(t, validate_all.offset == 0)
}
