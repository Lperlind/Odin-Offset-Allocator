# Odin Offset Allocator
A straight port of https://github.com/sebbbi/OffsetAllocator/tree/main in odin

usage
```odin
// create allocator
allocator, alloc_err := offset_allocator_make(max_size, max_allocs, context.allocator)

// allocate 32 bytes and get the offset
allocation, ok := offset_allocator_allocate(&allocator, 32)
my_offset := allocation.offset
handle := allocation.meta_data

// release the allocation
offset_allocator_free(&allocator, handle)

// delete the allocator itself
offset_allocator_delete(&allocator)
```
