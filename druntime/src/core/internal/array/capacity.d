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
import core.internal.array.construction : _d_newarrayU;

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

// Overload for shared arrays
T[] _d_arraysetlengthT(T)(ref shared T[] arr, size_t newlength) @trusted
{
    // Cast the shared array to a non-shared array
    return _d_arraysetlengthT!(T)(cast(T[])arr, newlength);
}

T[] _d_arraysetlengthT(T)(ref string arr, size_t newlength) @trusted
{
    // Handle string resizing specifically
    // Use _d_newarrayU to allocate a new array of `char` type
    auto newArr = _d_newarrayU!char(newlength);
    
    // Cast to immutable(char)[] since `string` is immutable in D
    arr = cast(immutable(char)[]) newArr[0 .. newlength];
    
    // Return the array in the expected form
    return [arr];
}

// General case
T[] _d_arraysetlengthT(T)(ref T[] arr, size_t newlength) @trusted
{
    alias UnqT = Unqual!T;

    debug(PRINTF)
    {
        printf("_d_arraysetlengthT(arr.ptr = %p, arr.length = %zd, newlength = %zd)\n", arr.ptr, arr.length, newlength);
    }

    if (newlength <= arr.length)
    {
        arr = arr[0 .. newlength];
        return arr;
    }

    static if (is(T == void))
    {
        size_t newsize = newlength;

        if (!arr.ptr)
        {
            assert(arr.length == 0);
            void* ptr = GC.malloc(newsize, BlkAttr.NO_SCAN | BlkAttr.APPENDABLE);
            if (!ptr)
            {
                onOutOfMemoryError();
                assert(0);
            }
            memset(ptr, 0, newsize);
            arr = (cast(void*) ptr)[0 .. newlength];
            return arr;
        }

        size_t oldsize = arr.length;
        void* newdata = arr.ptr;

        if (!gc_expandArrayUsed(newdata[0 .. oldsize], newsize, false))
        {
            newdata = GC.malloc(newsize, BlkAttr.NO_SCAN | BlkAttr.APPENDABLE);
            if (!newdata)
            {
                onOutOfMemoryError();
                assert(0);
            }
            memcpy(newdata, arr.ptr, oldsize);
        }
        memset(newdata + oldsize, 0, newsize - oldsize);
        arr = (cast(void*) newdata)[0 .. newlength];
        return arr;
    }
    else static if (is(T == char)) // Special handling for strings
    {
        // Use _d_newarrayU for string allocation
        auto newarr = _d_newarrayU!char(newlength);
        arr = newarr[0 .. newlength];
        return arr;
    }
    else
    {
        size_t sizeelem = T.sizeof;
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
            {
                memset(ptr, 0, newsize);
            }
            else
            {
                foreach (i; 0 .. newlength)
                {
                    emplace(cast(T*) ptr + i, T.init);
                }
            }

            arr = (cast(T*) ptr)[0 .. newlength];
            return arr;
        }

        size_t oldsize = arr.length * sizeelem;
        bool isshared = is(UnqT == shared UnqT);
        void* newdata = cast(void*) arr.ptr;

        if (!gc_expandArrayUsed(newdata[0 .. oldsize], newsize, isshared))
        {
            newdata = GC.malloc(newsize, gcAttrs);
            if (!newdata)
            {
                onOutOfMemoryError();
                assert(0);
            }
            memcpy(newdata, cast(void*) arr.ptr, oldsize);
            static if (__traits(compiles, __doPostblit(newdata, oldsize, UnqT)))
            {
                __doPostblit(newdata, oldsize, UnqT);
            }
        }

        // Handle initialization based on whether the type requires zero-init
        static if (__traits(isZeroInit, T))
        {
            memset(newdata + oldsize, 0, newsize - oldsize);
        }
        else
        {
            foreach (i; 0 .. newlength - arr.length)
            {
                emplace(cast(T*) (newdata + oldsize) + i, T.init);
            }
        }

        arr = (cast(T*) newdata)[0 .. newlength];
        return arr;
    }
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