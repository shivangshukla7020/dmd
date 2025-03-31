/**
 This module contains support for controlling dynamic arrays' capacity and length

  Copyright: Copyright Digital Mars 2000 - 2019.
  License: Distributed under the
       $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0).
     (See accompanying file LICENSE)
  Source: $(DRUNTIMESRC core/internal/_array/_capacity.d)
*/
module core.internal.array.capacity;

import core.attribute : weak;
import core.checkedint : mulu;
import core.exception : onFinalizeError, onOutOfMemoryError, onUnicodeError;
import core.internal.gc.blockmeta : PAGESIZE;
import core.memory;
import core.stdc.stdlib : malloc;
import core.stdc.string : memcpy, memset;
import core.internal.traits : Unqual;
import core.lifetime : emplace;


debug (PRINTF) import core.stdc.stdio : printf;
debug (VALGRIND) import etc.valgrind.valgrind;

alias BlkAttr = GC.BlkAttr;

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
    isZeroInitialized = Whether new elements should be zero-initialized.

Returns:  
    The resized array with updated length and properly initialized elements.

Throws:  
    OutOfMemoryError if allocation fails.
*/

T[] _d_arraysetlengthT(T)(ref T[] arr, size_t newlength, bool isZeroInitialized) @trusted pure nothrow
{
    alias UnqT = Unqual!T;
    size_t sizeelem = T.sizeof;

    debug(PRINTF)
    {
        printf("_d_arraysetlengthT(arr.ptr = %p, arr.length = %zd, newlength = %zd)\n", arr.ptr, arr.length, newlength);
    }

    if (newlength <= arr.length)
    {
        arr = arr[0 .. newlength];
        return arr;
    }

    // Calculate new size: newlength * sizeelem
    bool overflow = false;
    size_t newsize;

    version (D_InlineAsm_X86)
    {
        asm pure nothrow @nogc
        {
            mov EAX, newlength;
            mul EAX, sizeelem;
            mov newsize, EAX;
            setc overflow;
        }
    }
    else version (D_InlineAsm_X86_64)
    {
        asm pure nothrow @nogc
        {
            mov RAX, newlength;
            mul RAX, sizeelem;
            mov newsize, RAX;
            setc overflow;
        }
    }
    else
    {
        newsize = mulu(sizeelem, newlength, overflow);
    }

    if (overflow)
    {
        onOutOfMemoryError();
        assert(0);
    }

    debug(PRINTF) printf("newsize = %zx\n", newsize);

    if (!arr.ptr)
    {
        assert(arr.length == 0);

        void* ptr = GC.malloc(newsize, __typeAttrs(typeid(T)) | BlkAttr.APPENDABLE, typeid(T));
        if (!ptr)
        {
            onOutOfMemoryError();
            assert(0);
        }

        if (isZeroInitialized)
            memset(ptr, 0, newsize);
        else
        {
            // Guard against T being void
            static if (!is(T == void))
            {
                foreach (i; 0 .. newlength - arr.length)
                {
                    emplace(cast(T*) ptr + (arr.length + i) * sizeelem, T.init); // Directly initialize each new element.
                }
            }
        }

        arr = cast(T[]) ptr[0 .. newlength];  // Cast to slice from raw pointer
        return arr;
    }

    size_t oldsize = arr.length * sizeelem;
    bool isshared = is(UnqT == shared UnqT);

    // Explicit cast to void* for immutable types
    void* newdata = cast(void*) arr.ptr;

    if (!gc_expandArrayUsed(newdata[0 .. oldsize], newsize, isshared))
    {
        newdata = GC.malloc(newsize, __typeAttrs(typeid(T)) | BlkAttr.APPENDABLE, typeid(T));
        if (!newdata)
        {
            onOutOfMemoryError();
            assert(0);
        }

        memcpy(newdata, arr.ptr, oldsize);

        // Only call __doPostblit if T has a postblit
        static if (__traits(compiles, __doPostblit(newdata, oldsize, UnqT)))
        {
            __doPostblit(newdata, oldsize, UnqT);
        }
    }

    // Initialize the unused portion of the newly allocated space
    if (isZeroInitialized)
        memset(newdata + oldsize, 0, newsize - oldsize);
    else
    {
        static if (!is(T == void))  // Guard against void type
        {
            foreach (i; 0 .. newlength - arr.length)
            {
                emplace(cast(T*) (newdata + oldsize) + i, T.init);  // Initialize new elements in new memory region.
            }
        }
    }

    // Correctly cast to slice from raw pointer
    arr = cast(T[]) newdata[0 .. newlength];  
    return arr;
}

version (D_ProfileGC)
{
    import core.internal.array.utils : _d_HookTraceImpl;
    
    alias _d_arraysetlengthTTrace = _d_HookTraceImpl!(T, _d_arraysetlengthT, "GC Profile Trace: _d_arraysetlengthT");
}


private uint __typeAttrs(const scope TypeInfo ti, void *copyAttrsFrom = null) pure nothrow
{
    if (copyAttrsFrom)
    {
        // try to copy attrs from the given block
        auto info = GC.query(copyAttrsFrom);
        if (info.base)
            return info.attr;
    }
    uint attrs = !(ti.flags & 1) ? BlkAttr.NO_SCAN : 0;
    if (typeid(ti) is typeid(TypeInfo_Struct)) {
        auto sti = cast(TypeInfo_Struct)cast(void*)ti;
        if (sti.xdtor)
            attrs |= BlkAttr.FINALIZE;
    }
    return attrs;
}



// @safe unittest remains intact
@safe unittest
{
    struct S
    {
        float f = 1.0;
    }

    int[] arr;
    _d_arraysetlengthT!(int)(arr, 16, true);
    assert(arr.length == 16);
    foreach (int i; arr)
        assert(i == int.init);

    shared S[] arr2;
    _d_arraysetlengthT!(shared S)(arr2, 16, true);
    assert(arr2.length == 16);
    foreach (s; arr2)
        assert(s == S.init);
}