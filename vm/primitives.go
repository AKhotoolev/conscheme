// This file is part of conscheme
// Automatically generated by compiler/primitives.scm
package conscheme
import "fmt"
import "os"
func evprim(primop string, code Obj, lexenv map[string]Obj) Obj {
	switch primop {
	case "$write/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return write(arg0, arg1)
	case "$display/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return display(arg0, arg1)
	case "lookahead-u8/1":
		arg0 := ev(car(code), false, lexenv)
		return lookahead_u8(arg0)
	case "put-u8/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return put_u8(arg0, arg1)
	case "get-u8/1":
		arg0 := ev(car(code), false, lexenv)
		return get_u8(arg0)
	case "$write-char/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return _write_char(arg0, arg1)
	case "$read-char/1":
		arg0 := ev(car(code), false, lexenv)
		return _read_char(arg0)
	case "open-input-file/1":
		arg0 := ev(car(code), false, lexenv)
		return open_input_file(arg0)
	case "current-output-port/0":
		return current_output_port()
	case "current-input-port/0":
		return current_input_port()
	case "output-port?/1":
		arg0 := ev(car(code), false, lexenv)
		return output_port_p(arg0)
	case "input-port?/1":
		arg0 := ev(car(code), false, lexenv)
		return input_port_p(arg0)
	case "port?/1":
		arg0 := ev(car(code), false, lexenv)
		return port_p(arg0)
	case "bytevector?/1":
		arg0 := ev(car(code), false, lexenv)
		return bytevector_p(arg0)
	case "$cell-set!/2":
		v := ev(car(code), false, lexenv)
		vv := (*v).(*[1]Obj)
		vv[0] = ev(car(cdr(code)), false, lexenv)
		return Void
	case "$cell-ref/1":
		v := ev(car(code), false, lexenv)
		vv := (*v).(*[1]Obj)
		return vv[0]
	case "$make-cell/1":
		var v [1]Obj
		v[0] = ev(car(code), false, lexenv)
		var vv interface{} = &v
		return Obj(&vv)
	case "command-line/0":
		return Command_line()
	case "exit/1":
		os.Exit(number_to_int(ev(car(code), false, lexenv)))
	case "eq?/2":
		if ev(car(code), false, lexenv) == ev(car(cdr(code)), false, lexenv) {
			return True
		} else {
			return False
		}
	case "eof-object/0":
		return Eof
	case "unspecified/0":
		return Void
	case "apply/n":
		return apply(code,lexenv)
	case "make-string/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return Make_string(arg0, arg1)
	case "make-string/1":
		return Make_string(ev(car(code), false, lexenv),Make_char(32))
	case "string-set!/3":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv);code = cdr(code)
		arg2 := ev(car(code), false, lexenv)
		return String_set_ex(arg0, arg1, arg2)
	case "string-ref/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return String_ref(arg0, arg1)
	case "string-length/1":
		arg0 := ev(car(code), false, lexenv)
		return String_length(arg0)
	case "string?/1":
		arg0 := ev(car(code), false, lexenv)
		return string_p(arg0)
	case "greatest-fixnum/0":
		return Make_fixnum(fixnum_max)
	case "least-fixnum/0":
		return Make_fixnum(fixnum_min)
	case "$cmp/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return number_cmp(arg0, arg1)
	case "$-/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return number_subtract(arg0, arg1)
	case "$//2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return number_divide(arg0, arg1)
	case "$+/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return number_add(arg0, arg1)
	case "$number->string/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return _number_to_string(arg0, arg1)
	case "number?/1":
		arg0 := ev(car(code), false, lexenv)
		return number_p(arg0)
	case "vector-set!/3":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv);code = cdr(code)
		arg2 := ev(car(code), false, lexenv)
		return Vector_set_ex(arg0, arg1, arg2)
	case "vector-ref/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return Vector_ref(arg0, arg1)
	case "vector-length/1":
		arg0 := ev(car(code), false, lexenv)
		return vector_length(arg0)
	case "make-vector/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return Make_vector(arg0, arg1)
	case "vector?/1":
		arg0 := ev(car(code), false, lexenv)
		return vector_p(arg0)
	case "integer->char/1":
		arg0 := ev(car(code), false, lexenv)
		return integer_to_char(arg0)
	case "char->integer/1":
		arg0 := ev(car(code), false, lexenv)
		return char_to_integer(arg0)
	case "char?/1":
		arg0 := ev(car(code), false, lexenv)
		return char_p(arg0)
	case "string->symbol/1":
		arg0 := ev(car(code), false, lexenv)
		return String_to_symbol(arg0)
	case "symbol->string/1":
		arg0 := ev(car(code), false, lexenv)
		return Symbol_to_string(arg0)
	case "symbol?/1":
		arg0 := ev(car(code), false, lexenv)
		return symbol_p(arg0)
	case "set-cdr!/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return set_cdr_ex(arg0, arg1)
	case "set-car!/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return set_car_ex(arg0, arg1)
	case "length/1":
		arg0 := ev(car(code), false, lexenv)
		return Length(arg0)
	case "floyd/1":
		arg0 := ev(car(code), false, lexenv)
		return Floyd(arg0)
	case "cdr/1":
		arg0 := ev(car(code), false, lexenv)
		return cdr(arg0)
	case "car/1":
		arg0 := ev(car(code), false, lexenv)
		return car(arg0)
	case "cons/2":
		arg0 := ev(car(code), false, lexenv);code = cdr(code)
		arg1 := ev(car(code), false, lexenv)
		return Cons(arg0, arg1)
	case "pair?/1":
		arg0 := ev(car(code), false, lexenv)
		return pair_p(arg0)
	case "not/1":
		arg0 := ev(car(code), false, lexenv)
		return not(arg0)
	case "boolean?/1":
		arg0 := ev(car(code), false, lexenv)
		return boolean_p(arg0)
	default:
		fmt.Fprintf(os.Stderr, "Please regenerate primitives.go\n")
		panic(fmt.Sprintf("Unimplemented primitive: %s",primop))
	}
	panic(fmt.Sprintf("Fell off the edge in evprim(): %s",primop))
}
