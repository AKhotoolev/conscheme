// Copyright (C) 2011 Göran Weinholt <goran@weinholt.se>
// All rights reserved.

// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. Neither the name of the University nor the names of its contributors
//    may be used to endorse or promote products derived from this software
//    without specific prior written permission.

// THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
// OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
// LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
// OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.

// Some simple test code to iron out a memory model

// All Scheme objects have type Obj. The two low bits in pointers are
// used to get limited type tagging. Normally one would want the tag
// '00' for fixnums, because it simplies arithmetic, but we have to
// use '00' for heap-allocated objects, or else the GC will deallocate
// all our objects.

// bits         purpose
// x....x00     heap-allocated object
// x....x01     fixnum
//       10     (unused)
//     x011     boolean
// x..x0111     character
//   001111     empty list
//   011111     end of file object
//   101111     void

// Heap-allocated objects have these dynamic interface{} types:
// []Obj        vector
// []int        string
// *[2]Obj      pair
// *big.Int     bignum
// string       symbol

package main

import "big"
import "fmt"
import "io"
import "os"
import "sync"
import "unsafe"

// Tags
const heap_tag = 0
const heap_mask = 0x3

const fixnum_tag = 1
const fixnum_mask = 0x3
const fixnum_shift = 2

const bool_shift = 3
const bool_tag = 0x3
const bool_mask = 0x7

const char_tag = 7
const char_mask = 0xf
const char_shift = 4

// The type of all Scheme objects.
type Obj *interface{}

// Constants.
const False = Obj(unsafe.Pointer(uintptr((0 << bool_shift) | bool_tag)))
const True = Obj(unsafe.Pointer(uintptr((1 << bool_shift) | bool_tag)))
const Eol = Obj(unsafe.Pointer(uintptr(0x0f))) // empty list
const Eof = Obj(unsafe.Pointer(uintptr(0x1f))) // end of file object
const Void = Obj(unsafe.Pointer(uintptr(0x2f)))	// the unspecified value

// Fixnums

func fixnum_p(x Obj) Obj {
	return make_boolean((uintptr(unsafe.Pointer(x)) & fixnum_mask) == fixnum_tag)
}

func make_fixnum(x int) Obj {
	// XXX: assumes x fits in a fixnum
	return Obj(unsafe.Pointer((uintptr((x << fixnum_shift) | fixnum_tag))))
}

func fixnum_to_int(x Obj) int {
	return int(uintptr(unsafe.Pointer(x))) >> fixnum_shift
}

// func fixnum_add(fx1,fx2 Obj) Obj {
// 	i1 := uintptr(unsafe.Pointer(fx1))
// 	i2 := uintptr(unsafe.Pointer(fx2))
// 	r := i1 + i2
// 	...
// }

// Chars

func char_p(x Obj) Obj {
	return make_boolean((uintptr(unsafe.Pointer(x)) & char_mask) == char_tag)
}

func make_char(x int) Obj {
	return Obj(unsafe.Pointer((uintptr((x << char_shift) | char_tag))))
}

func char_to_int(x Obj) int {
	return int(uintptr(unsafe.Pointer(x))) >> char_shift
}

// Booleans

func boolean_p(x Obj) Obj {
	return make_boolean((uintptr(unsafe.Pointer(x)) & bool_mask) == bool_tag)
}

func make_boolean(x bool) Obj {
	if x { return True }
	return False
}

func not(x Obj) Obj {
	if x == False {	return True }
	return False
}

// Pairs

func pair_p(x Obj) Obj {
	if (uintptr(unsafe.Pointer(x)) & heap_mask) != heap_tag { return False }

	switch v := (*x).(type) {
	case *[2]Obj:
		return True
	}
	return False
}

func cons(x,y Obj) Obj {
	var v [2]Obj
	v[0] = x
	v[1] = y

	var vi interface{} = &v
	return Obj(&vi)
}

func car(x Obj) Obj {
	if pair_p(x) == False {
		// Error
		return Void
	}

	v := (*x).(*[2]Obj)
	return v[0]
}

func cdr(x Obj) Obj {
	if pair_p(x) == False {
		// Error
		return Void
	}
	v := (*x).(*[2]Obj)
	return v[1]
}

func set_car_ex(x,value Obj) Obj {
	if pair_p(x) == False {
		// Error
		return Void
	}
	v := (*x).(*[2]Obj)
	v[0] = value
	return Void
}

func set_cdr_ex(x,value Obj) Obj {
	if pair_p(x) == False {
		// Error
		return Void
	}
	v := (*x).(*[2]Obj)
	v[1] = value
	return Void
}

func list(v ...Obj) Obj {
	ret := Eol
	for i := len(v) - 1; i >= 0; i-- {
		ret = cons(v[i], ret)
	}
	return ret
}


// Vectors

func vector_p(x Obj) Obj {
	if (uintptr(unsafe.Pointer(x)) & heap_mask) != heap_tag { return False }

	switch v := (*x).(type) {
	case []Obj:
		return True
	}
	return False
}

func vector(v ...Obj) Obj {
	var vi interface{} = v
	return Obj(&vi)
}

func make_vector(length,init Obj) Obj {
	if fixnum_p(length) == False {
		// XXX: should be an error
		length = make_fixnum(0)
	}
	l := fixnum_to_int(length)
	v := make([]Obj, fixnum_to_int(length))

	for i := 0; i < l; i++ {
		v[i] = init
	}

	var vi interface{} = v

	return Obj(&vi)
}

func vector_length(x Obj) Obj {
	if vector_p(x) == False {
		// Error
		return Void
	}
	v := (*x).([]Obj)
	return make_number(len(v))
}


func vector_ref(x,idx Obj) Obj {
	if vector_p(x) == False || fixnum_p(idx) == False {
		// error
		return Void
	}
	v := (*x).([]Obj)
	return v[fixnum_to_int(idx)]
}

func vector_set_ex(x,idx,value Obj) Obj {
	if vector_p(x) == False || fixnum_p(idx) == False {
		// error
		return Void
	}
	v := (*x).([]Obj)
	v[fixnum_to_int(idx)] = value
	return Void
}

// Strings

func string_p(x Obj) Obj {
	if (uintptr(unsafe.Pointer(x)) & heap_mask) != heap_tag { return False }

	switch v := (*x).(type) {
	case []int:
		return True
	}
	return False
}

func make_string(length,init Obj) Obj {
	if fixnum_p(length) == False || char_p(init) == False {
		// XXX: should be an error
		length = make_fixnum(0)
		init = make_char(' ')
	}
	l := fixnum_to_int(length)
	v := make([]int, fixnum_to_int(length))
	init_c := char_to_int(init)

	for i := 0; i < l; i++ {
		v[i] = init_c
	}

	var vi interface{} = v

	return Obj(&vi)
}

func string_length(x Obj) Obj {
	if string_p(x) == False {
		// error
		return Void
	}
	v := (*x).([]int)
	return make_number(len(v))
}

func string_ref(x, idx Obj) Obj {
	if string_p(x) == False || fixnum_p(idx) == False {
		// error
		return Void
	}
	v := (*x).([]int)
	return make_char(v[fixnum_to_int(idx)])
}


// Bignums

func make_bignum(x int64) Obj {
	var vv interface{} = big.NewInt(x)
	return Obj(&vv)
}

func bignum_p(x Obj) Obj {
	if (uintptr(unsafe.Pointer(x)) & heap_mask) != heap_tag { return False }

	switch v := (*x).(type) {
	case *big.Int:
		return True
	}
	return False
}

// Numbers

func make_number(x int) Obj {
	v := make_fixnum(x)
	if fixnum_to_int(v) != x {
		return make_bignum(int64(x))
	}
	return v
}

// Symbols

// It would be better to use a weak hashset here, if one was available
var symtab map[string]Obj = make(map[string]Obj)
var symlock sync.Mutex

func symbol_p(x Obj) Obj {
	if (uintptr(unsafe.Pointer(x)) & heap_mask) != heap_tag { return False }

	switch v := (*x).(type) {
	case string:
		return True
	}
	return False
}

func string_to_symbol(x Obj) Obj {
	if string_p(x) == False {
		// error
		return Void
	}
	v := (*x).([]int)
	str := string(v)
	symlock.Lock();	defer symlock.Unlock()
	sym, is_interned := symtab[str]
	if is_interned {
		// string->symbol has already interned this symbol
		return sym
	}
	// Intern the new symbol
	var stri interface{} = str
	sym = Obj(&stri)
	symtab[str] = sym
	return sym
}

func symbol_to_string(x Obj) Obj {
	if symbol_p(x) == False {
		// error
		return Void
	}
	v := (*x).(string)
	str := ([]int)(v)
	var stri interface{} = str
	return Obj(&stri)
}

// Object printer (for debugging)

func obj_display(x Obj, p io.Writer, write Obj) {
	switch {
	case fixnum_p(x) != False:
		fmt.Fprintf(p, "%d", fixnum_to_int(x))
	case bignum_p(x) != False:
		fmt.Fprintf(p, "%d", *x)
	case char_p(x) != False:
		if write != False {
			fmt.Fprintf(p, "#\\")
			// XXX: doesn't handle #\newline, etc
		}
		fmt.Fprintf(p, "%c", char_to_int(x))
	case boolean_p(x) != False:
		if x == False {
			fmt.Fprintf(p, "#f")
		} else {
			fmt.Fprintf(p, "#t")
		}
	case vector_p(x) != False:
		fmt.Fprintf(p, "#(")
		length := fixnum_to_int(vector_length(x))
		for i := 0; i < length - 1; i++ {
			obj_display(vector_ref(x,make_fixnum(i)), p, write)
			fmt.Fprintf(p, " ")
		}
		if length > 0 {
			obj_display(vector_ref(x,make_fixnum(length-1)), p, write)
		}
		fmt.Fprintf(p, ")")
	case string_p(x) != False:
		// XXX: doesn't handle \n, etc
		if write != False { fmt.Fprintf(p, "\"") }
		length := fixnum_to_int(string_length(x))
		s := (*x).([]int)
		for i := 0; i < length; i++ {
			fmt.Fprintf(p, "%c", s[i])
		}
		if write != False { fmt.Fprintf(p, "\"") }
	case symbol_p(x) != False:
		// XXX: doesn't handle escapes
		obj_display(symbol_to_string(x), p, False)
	case pair_p(x) != False:
		fmt.Fprintf(p, "(")
		for i := x; i != Eol; {
			obj_display(car(i), p, write)
			i = cdr(i)
			switch {
			case i == Eol:
			case pair_p(i) != False:
				fmt.Fprintf(p, " ")
			default:
				fmt.Fprintf(p, " . ")
				obj_display(i, p, write)
				i = Eol
			}
		}
		fmt.Fprintf(p, ")")
	case x == Eol:
		fmt.Fprintf(p, "()")
	case x == Eof:
		fmt.Fprintf(p, "#<eof>")
	case x == Void:
		fmt.Fprintf(p, "#<void>")
	// Unknown types
	case uintptr(unsafe.Pointer(x)) & heap_mask == heap_tag:
		fmt.Fprintf(p, "#<heapobj %d>", *x)
	default:
		fmt.Fprintf(p, "#<immobj %x>", x)
	}
}

func display(x Obj) { obj_display(x, os.Stdout, False) }
func write(x Obj) { obj_display(x, os.Stdout, True) }

func main() {
	vec := make_vector(make_fixnum(6), make_fixnum(42))
	vector_set_ex(vec, make_fixnum(0), make_boolean(true))
	vector_set_ex(vec, make_fixnum(1),
		make_vector(make_fixnum(5), make_fixnum(123)))
	vector_set_ex(vec, make_fixnum(2),
		vector_ref(vec,make_fixnum(1)))
	vector_set_ex(vec, make_fixnum(3),
		make_boolean(false))
	vector_set_ex(vec, make_fixnum(4),
		vector(True,list(make_char('å'),make_char('ä'),make_char('ö')),
		make_fixnum(1234),
		list(make_fixnum(42),False,True),
		make_string(make_fixnum(3), make_char('X')),
		string_to_symbol(make_string(make_fixnum(2), make_char('X')))))

	// Force the GC to run
	for i := 1; i < 0xfffff; i++ {
		vector_set_ex(vec, make_fixnum(1), list(make_fixnum(1), make_fixnum(2)))
	}

	write(vec)
	fmt.Printf("\n")
	fmt.Printf("(eq? 'X 'X) => ")
	write(make_boolean(string_to_symbol(make_string(make_fixnum(1), make_char('X'))) ==
		string_to_symbol(make_string(make_fixnum(1), make_char('X')))))
	fmt.Printf("\n")
}