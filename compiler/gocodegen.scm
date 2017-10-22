;; -*- mode: scheme; coding: utf-8 -*-
;; Copyright (C) 2017 Göran Weinholt <goran@weinholt.se>

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
;; THE SOFTWARE.

;; Generates golang code from bytecode.

;;; XXX: This is not operational and is not even fully sketched out.
;;; The general idea is to generate go code from the bytecode, compile
;;; it as a plugin and load it, and have the vm call the compiled
;;; code. A limitation is that we can't use the Go stack, so for all
;;; things that manipulate the stack (calls, the stack instructions)
;;; we need to return to the vm and tell it where control should go. A
;;; complicating factor is how to handle goto's across these borders.

(define (make-conscheme-deserializer in)
  (define magic "conscheme serialized object format\n")
  (define tag-Integer    0)
  (define tag-Pair       1)
  (define tag-Vector     2)
  (define tag-Null       3)
  (define tag-String     4)
  (define tag-Symbol     5)
  (define tag-Boolean    6)
  (define tag-Char       7)
  (define tag-Rational   8)
  (define tag-Float64    9)
  (define tag-Complex128 10)
  (define tag-Bytevector 12)
  (define (reader msg . rest)
    (case msg
      ((int)
       (let ((sign (get-u8 in)))
         (let lp ((v 0) (i 0))
           (let ((b (get-u8 in)))
             (let ((v (bitwise-ior v (bitwise-arithmetic-shift-left (bitwise-and b #x7f) i))))
               (cond ((zero? (bitwise-and b #x80))
                      (if (= sign 1) (- v) v))
                     (else
                      (lp v (+ i 7)))))))))
      ((string)
       (utf8->string (get-bytevector-n in (car rest))))
      ((obj)
       (let* ((tag (reader 'int))
              (len (reader 'int)))
         (cond
           ((= tag tag-Integer)
            len)
           ((= tag tag-Rational)
            (/ len (reader 'int)))
           ;; XXX: missing Float64, Complex128
           ((= tag tag-Pair)
            (cons (reader 'obj) (reader 'obj)))
           ((= tag tag-Vector)
            (let ((v (make-vector len 0)))
              (do ((i 0 (+ i 1)))
                  ((= i len) v)
                (vector-set! v i (reader 'obj)))))
           ((= tag tag-Null)
            '())
           ((= tag tag-String)
            (reader 'string len))
           ((= tag tag-Symbol)
            (string->symbol (reader 'string len)))
           ((= tag tag-Bytevector)
            (get-bytevector-n in len))
           ((= tag tag-Boolean)
            (not (zero? len)))
           ((= tag tag-Char)
            (integer->char len))
           (else
            (error 'make-deserializer "Unimplemented tag" tag len)))))
      (else
       (error 'make-deserializer "Bad message" msg))))
  (let ((header-magic (utf8->string (get-bytevector-n in (string-length magic)))))
    (unless (string=? magic header-magic)
      (error 'make-deserializer "Not a conscheme image" magic header-magic)))
  (let ((version (get-u8 in)))
    (unless (equal? version 1)
      (error 'make-deserializer "Wrong conscheme image version" version)))
  reader)

(define (gocodegen in out)
  ;; Opcode numbers
  (define FRAME         #b00001)          ; reg
  (define RETURN        #b00010)          ; reg
  (define PUSH          #b00011)          ; reg
  (define MAKE-VOID     #b00100)          ; reg
  (define MOVE          #b00101)          ; reg1 reg2
  (define CLOSURE.NAME  #b00110)          ; reg1 reg2
  (define CLOSURE-REF   #b00111)          ; reg n
  (define CLOSURE       #b01010)          ; reg n
  (define TAILCALL      #b01011)          ; reg n
  (define CONSARGS      #b01100)          ; n
  (define CLOSURE.VAR   #b01101)          ; reg1 n reg2
  (define FUNCALL       #b01110)          ; reg1 reg2 n
  (define APPLYCALL     #b10011)          ; reg1 reg2 n
  (define TAILAPPLY     #b10100)          ; reg n
  (define STACK-CTRL    #b10101)          ; reg1 reg2 n
  (define JUMP          #b00000)          ; label
  (define CONST-REF     #b01001)          ; reg n
  (define BF            #b01111)          ; reg label
  (define CLOSURE.LABEL #b10000)          ; reg label
  ;; Instruction fields
  (define I_SHIFT      27)
  (define OP1_N        #x7f00000)
  (define OP1_N_SHIFT  20)
  (define OP1_R1       #xFFC00)
  (define OP1_R1_SHIFT 10)
  (define OP1_R2       #x3ff)
  (define OP2_N        #x7FFFC00)
  (define OP2_N_SHIFT  10)
  (define OP2_R        #x3ff)
  (define OP3_N1       #x7FC0000)
  (define OP3_N1_SHIFT 18)
  (define OP3_N2       #x3FC00)
  (define OP3_N2_SHIFT 10)
  (define OP3_R        #x3ff)
  (define (instr-I instr)
    (bitwise-arithmetic-shift-right instr I_SHIFT))
  (define (instr-OP1-N instr)
    (bitwise-arithmetic-shift-right (bitwise-and instr OP1_N) OP1_N_SHIFT))
  (define (instr-OP1-R1 instr)
    (bitwise-arithmetic-shift-right (bitwise-and instr OP1_R1) OP1_R1_SHIFT))
  (define (instr-OP1-R2 instr)
    (bitwise-and instr OP1_R2))
  (define (instr-OP2-N instr)
    (bitwise-arithmetic-shift-right (bitwise-and instr OP2_N) OP2_N_SHIFT))
  (define (instr-OP2-R instr)
    (bitwise-and instr OP2_R))
  (define (instr-OP3-N1 instr)
    (bitwise-arithmetic-shift-right (bitwise-and instr OP3_N1) OP3_N1_SHIFT))
  (define (instr-OP3-N2 instr)
    (bitwise-arithmetic-shift-right (bitwise-and instr OP3_N2) OP3_N2_SHIFT))
  (define (instr-OP3-R instr)
    (bitwise-and instr OP3_R))
  (define (int17 n)
    (if (<= n #xffff) n (- n #x20000)))
  (define (emit . x*)
    (for-each (lambda (x)
                (display x out))
              x*)
    (newline out))
  (define (emit-label labels pc)
    (when (vector-binary-search labels pc (lambda (x y)
                                            (cond ((< x y) -1) ((= x y) 0) (else 1))) )
      (emit "l" pc ":")))
  (define (scan-labels bytecode)
    (let lp ((pc 0) (labels '()))
      (if (= pc (/ (bytevector-length bytecode) 4))
          (list->vector (reverse labels))
          (let* ((instr (bytevector-u32-ref bytecode (* pc 4) (endianness little)))
                 (opcode (instr-I instr)))
            (cond ((or (= opcode JUMP) (= opcode BF))
                   (lp (+ pc 1) (cons (+ (- pc 1) (int17 (instr-OP2-N instr))) labels)))
                  (else
                   (lp (+ pc 1) labels)))))))
  (let ((d (make-conscheme-deserializer in)))
    (let ((options (d 'obj)))
      (let ((version (cond ((and (list? options) (assq 'bytecode options)) => cdr)
                           (else #f))))
        (unless (eqv? version 1)
          (error 'gocodegen "Unsupported bytecode version" version))))
    (let ((image (d 'obj)))
      (let* ((bytecode (vector-ref image 0))
             (constants (vector-ref image 1))
             (total-instrs (/ (bytevector-length bytecode) 4))
             (labels (scan-labels bytecode)))
        (emit "var constants []Obj")
        (emit "func init_constants() {")
        (emit #\tab "// TODO")
        (emit "}")
        (emit)
        (do ((pc 0 (+ pc 1)))
            ((= pc total-instrs))
          (emit-label labels pc)
          (let* ((instr (bytevector-u32-ref bytecode (* pc 4) (endianness little)))
                 (opcode (instr-I instr)))
            (cond
              ;; op1 format
              ((= opcode FRAME)
               ;; TODO: Assign from args to registers. Or may need to
               ;; update the bytecode so that it knows what regs are
               ;; arguments.
               (emit "func proc" pc "(ct Obj, argstack *Argstack, stack *Frame, args []Obj) Obj {")
               (emit #\tab "Obj "
                     (string-join (map (lambda (r)
                                         (string-append "r" (number->string r)))
                                       (iota (instr-OP1-R2 instr)))
                                  ", " 'infix)))

              ((= opcode RETURN)
               (emit #\tab "return r" (instr-OP1-R2 instr))
               (emit "}")
               (emit))

              ((= opcode PUSH)
               (emit #\tab "argstack.Push(r" (instr-OP1-R2 instr) ")"))

              ((= opcode MOVE)
               (emit #\tab "r" (instr-OP1-R2 instr) " = r" (instr-OP1-R1 instr)))

              ((= opcode MAKE-VOID)
               (emit #\tab "r" (instr-OP1-R2 instr) " = Void"))

              ((= opcode CLOSURE)
               (emit #\tab "r" (instr-OP1-R2 instr) " = "
                     "&Procedure{apply: apply_gocode, free: make([]Obj, "
                     (instr-OP1-N instr)
                     "), code: stack.code}"))

              ((= opcode CLOSURE.NAME)
               (emit #\tab "mustProcedure(r" (instr-OP1-R2 instr)
                     ").name = scm2str(r" (instr-OP1-R1 instr) ")"))

              ((= opcode CLOSURE.VAR)
               (emit #\tab "mustProcedure(r" (instr-OP1-R2 instr)
                     ").free[" (instr-OP1-N instr) "]"
                     " = r" (instr-OP1-R1 instr)))

              ((= opcode CLOSURE-REF)
               (emit #\tab "r" (instr-OP1-R2 instr) " = "
                     "stack.cc.free[" (instr-OP1-N instr) "]"))

              ((= opcode FUNCALL)
               ;; TODO: This needs to return to the caller (the vm)
               ;; and tell it to call the function, but then it must
               ;; be possible to go back to this execution flow.
               (emit #\tab "r" (instr-OP1-R2 instr) " = vm_funcall("
                     "mustProcedure(r" (instr-OP1-R1 instr) "), argstack, "
                     (instr-OP1-N instr) ")"))

              ((= opcode TAILCALL)
               ;; TODO: Same as above, except without the return problem.
               (emit #\tab "return vm_tailcall("
                     "mustProcedure(r" (instr-OP1-R2 instr) "), argstack, "
                     (instr-OP1-N instr) ")"))

              ((= opcode CONSARGS)
               (emit #\tab "r" (- (instr-OP1-N instr) 1)
                     " = consargs(args, " (instr-OP1-N instr) ")"))

              ((= opcode APPLYCALL)
               ;; TODO: Same problem as FUNCALL
               (emit #\tab "r" (instr-OP1-R2 instr) " = vm_applycall("
                     "mustProcedure(r" (instr-OP1-R1 instr) "), argstack, "
                     (instr-OP1-N instr) ")"))

              ((= opcode TAILAPPLY)
               ;; TODO: Same problem as TAILCALL
               (emit #\tab "return vm_tailapply("
                     "mustProcedure(r" (instr-OP1-R2 instr) "), argstack, "
                     (instr-OP1-N instr) ")"))

              ((= opcode STACK-CTRL)
               ;; TODO: Same problem as FUNCALL, but slightly worse.
               (let ((subop (instr-OP1-N instr)))
                 (cond
                   ((= subop 0)
                    (emit #\tab "r" (instr-OP1-R2 instr) " = vm_copy_stack(stack)"))
                   ((= subop 1)
                    (emit #\tab "return vm_restore_stack(r" (instr-OP1-R2 instr) ", "
                          "r" (instr-OP1-R1 instr) ")"))
                   (else
                    (emit #\tab "panic(\"Unimplemented stack subop: #b" (number->string subop 2)
                          " (in #x" (number->string instr 16) ")\")")))))

              ;; op2 format
              ((= opcode JUMP)
               (emit #\tab "goto l" (+ (- pc 1) (int17 (instr-OP2-N instr)))))

              ((= opcode CONST-REF)
               (emit #\tab "r" (instr-OP2-R instr) " = constants[" (instr-OP2-N instr) "]"))

              ((= opcode CLOSURE.LABEL)
               (emit #\tab "mustProcedure(r" (instr-OP2-R instr) ").label = proc"
                     (+ (- pc 1) (int17 (instr-OP2-N instr)))))

              ((= opcode BF)
               (emit #\tab "if r" (instr-OP2-R instr) " != False {" )
               (emit #\tab #\tab "goto l" (+ (- pc 1) (int17 (instr-OP2-N instr))))
               (emit #\tab "}"))

              ;; op3 format
              ((= opcode PRIMCALL)
               (emit #\tab "r" (instr-OP3-R instr) " = evprimn(" (instr-OP3-N2 instr)
                     ", argstack[len(argstack)-" (instr-OP3-N1 instr) ":], ct)")
               (emit #\tab "argstack = argstack[:len(argstack)-" (instr-OP3-N1 instr) "]"))

              ((= opcode PRIMREF)
               (emit #\tab "r" (instr-OP3-R instr) " = primitive[" (instr-OP3-N2 instr) "]"))

              (else
               (emit #\tab "panic(\"Unimplemented opcode: #b" (number->string opcode 2)
                     " (in #x" (number->string instr 16) ")\")")))))))))

(gocodegen (open-file-input-port "compiler/conscheme.image.pre-built")
           (current-output-port))
