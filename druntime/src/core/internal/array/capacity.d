/**
 This module contains support for controlling dynamic arrays' capacity and length

  Copyright: Copyright Digital Mars 2000 - 2019.
  License: Distributed under the
       $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0).
     (See accompanying file LICENSE)
  Source: $(DRUNTIMESRC core/internal/_array/_capacity.d)
*/
module core.internal.array.capacity;

debug (PRINTF) import core.stdc.stdio : printf;
debug (VALGRIND) import etc.valgrind.valgrind;

// for now, all GC array functions are not exposed via core.memory.
extern(C) {
    void[] gc_getArrayUsed(void *ptr, bool atomic) nothrow;
    bool gc_expandArrayUsed(void[] slice, size_t newUsed, bool atomic) nothrow pure;
    size_t gc_reserveArrayCapacity(void[] slice, size_t request, bool atomic) nothrow;
    bool gc_shrinkArrayUsed(void[] slice, size_t existingUsed, bool atomic) nothrow;
}

/**
Resize a dynamic array by setting its `.length` property.

Newly created elements are initialized based on their default value.  
If the array's elements initialize to `0`, memory is zeroed out. Otherwise, elements are explicitly initialized.  

This function handles memory allocation, expansion, and initialization while maintaining array integrity.

---
void main()
{
    int[] a = [1, 2];
    a.length = 3; // Gets lowered to `_d_arraysetlengthT!(int)(a, 3, true)`
}
---

Params:
    arr         = The array to resize.
    newlength   = The new value for the array's `.length`.

Returns:  
    The resized array with updated length and properly initialized elements.

Throws:  
    OutOfMemoryError if allocation fails.
*/


T[] _d_arraysetlengthT(T)(return scope ref T[] arr, size_t newlength) @trusted
{
    import core.attribute : weak;
    import core.checkedint : mulu;
    import core.exception : onFinalizeError, onOutOfMemoryError;
    import core.stdc.string : memcpy, memset;
    import core.internal.traits : Unqual;
    import core.lifetime : emplace;
    import core.memory;

    alias BlkAttr = GC.BlkAttr;
    alias UnqT = Unqual!T;

    debug(PRINTF) printf("_d_arraysetlengthT(arr.ptr = %p, arr.length = %zd, newlength = %zd)\n", arr.ptr, arr.length, newlength);

    // If the new length is less than or equal to the current length, just truncate the array
    if (newlength <= arr.length)
    {
        arr = arr[0 .. newlength];
        return arr;
    }

    size_t sizeelem = T.sizeof;
    bool overflow = false;
    size_t newsize = mulu(sizeelem, newlength, overflow);

    if (overflow)
    {
        onOutOfMemoryError();
        assert(0);
    }

    debug(PRINTF) printf("newsize = %zx\n", newsize);

    uint gcAttrs = BlkAttr.APPENDABLE;
    static if (is(T == struct) && __traits(hasMember, T, "xdtor"))
    {
        gcAttrs |= BlkAttr.FINALIZE;
    }

    if (!arr.ptr)
    {
        assert(arr.length == 0);
        void* ptr = GC.malloc(newsize, gcAttrs);
        if (!ptr)
        {
            onOutOfMemoryError();
            assert(0);
        }

        // Handle initialization based on whether the type requires zero-init
        static if (__traits(isZeroInit, T))
            memset(ptr, 0, newsize);
        else
            foreach (i; 0 .. newlength)
                emplace(cast(T*) ptr + i, T.init);

        arr = (cast(T*) ptr)[0 .. newlength];
        return arr;
    }

    size_t oldsize = arr.length * sizeelem;
    bool isshared = is(T == shared T);

    // 🔹 Fix `scope` issue: Prevent escaping `scope` data by keeping `oldptr` strongly typed
    scope auto oldptr = arr.ptr; 

    void* newdata = cast(void*) oldptr;  // ✅ Now correctly typed and won't escape `scope`

    if (!gc_expandArrayUsed(newdata[0 .. oldsize], newsize, isshared))
    {
        newdata = GC.malloc(newsize, gcAttrs);
        if (!newdata)
        {
            onOutOfMemoryError();
            assert(0);
        }

        memcpy(newdata, cast(const(void)*)arr.ptr, oldsize);

        static if (__traits(compiles, __doPostblit(newdata, oldsize, UnqT)))
            __doPostblit(newdata, oldsize, UnqT);
    }

    // Handle initialization based on whether the type requires zero-init
    static if (__traits(isZeroInit, T))
        memset(cast(void*) (cast(ubyte*)newdata + oldsize), 0, newsize - oldsize);
    else
        foreach (i; 0 .. newlength - arr.length)
            emplace(cast(T*) (cast(ubyte*)newdata + oldsize) + i, T.init);

    arr = (cast(T*) newdata)[0 .. newlength];
    return arr;
}

// @safe unittest remains intact
@safe unittest
{
    struct S
    {
        float f = 1.0;
    }

    int[] arr;
    _d_arraysetlengthT!(int)(arr, 16);
    assert(arr.length == 16);
    foreach (int i; arr)
        assert(i == int.init);

    shared S[] arr2;
    _d_arraysetlengthT!(shared S)(arr2, 16);
    assert(arr2.length == 16);
    foreach (s; arr2)
        assert(s == S.init);
}