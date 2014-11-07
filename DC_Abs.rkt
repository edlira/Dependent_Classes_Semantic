#lang racket

(require redex)
(require rackunit)

(define-language DC
  (p    ::= (e (c ...)))
  (c    ::= (class cx (f : T) ... : T extends (CT ...) e))
  (e    ::= v this (e ! f) (new cx (f = e) ...))
  (v    ::= (obj cx (f = v) ...))
  
  (CT   ::= (cx (f : T) ...))    ; regular class types
  (P    ::= this (P ! f))        ; paths
  (DT   ::= v P)                 ; value-dependent and path-dependent types
  (T    ::= DT CT)               ; all types
  (NT   ::= v (cx (f : NT) ...)) ; normalized types
  (Ctx  ::= empty NT)
  
  (C    ::= hole (C ! f) (new cx (f = v) ... (f = C) (f = e) ...))
  
  (cx   ::= x)
  (f    ::= x)
  (x    ::= (variable-except class obj : = ! new this extends))
)

(define (p-pretty-printer v port width text)
  (default-pretty-printer (car v) port width text))

(define red (reduction-relation DC #:domain p
   (--> ((in-hole C ((obj cx (f = v) ...)  !  f_0))        (c ...))
        ((in-hole C v_0) (c ...))
        (judgment-holds (lookup f_0 ((f v) ...) v_0))
        "field lookup")

   (--> ((in-hole C (new cx (f = v) ...))                       (c_1 ... c c_2 ...))
        ((in-hole C (subst-this (obj cx (f = v) ...) e))        (c_1 ... c c_2 ...))
        
        (where (class cx (f : T) ... : T_cres extends (CT ...) e) c)
        (judgment-holds (type-norms (cx (f : v) ...) (T ...) (NT ...)))
        (judgment-holds (sub-types ((v NT) ...) (c_1 ... c c_2 ...)))
        "object creation")
))

(define-metafunction DC
  subst-this : v e -> e
  [(subst-this v v_2) v_2]
  [(subst-this v this) v]
  [(subst-this v (e ! f)) ((subst-this v e) ! f)]
  [(subst-this v (new cx (f = e) ...)) (new cx (f = (subst-this v e)) ...)]
)

(define-judgment-form DC
  #:mode (lookup I I O)
  #:contract (lookup x ((x any) ...) any)
  [----------------------------------------
   (lookup x ((x any) (x_r any_r) ...) any)]
  
  [(lookup x ((x_r any_r) ...) any_res)
   ----------------------------------------------
   (lookup x ((x_1 any) (x_r any_r) ...) any_res)]
)

(define (DC-traces p)
  (traces red p #:pp p-pretty-printer))

;; ******************
;; typing judgments
;; ******************

;(define-metafunction DC
;  tsubst-this : CT T -> T
;  [(tsubst-this CT v) v]
;  [(tsubst-this CT this) CT]
;  [(tsubst-this CT (P ! f)) ((tsubst-this CT P) ! f)]
;  [(tsubst-this CT (cx (f : T) ...)) (cx (f : (tsubst-this CT T)) ...)]
;)

(define-judgment-form DC
  #:mode (type-norm I I O)
  #:contract (type-norm NT T NT)
  
  [---------------------- "type-norm val"
   (type-norm NT_ctx v v)]
  
  [------------------------------ "type-norm this"
   (type-norm NT_ctx this NT_ctx)]

  [(type-norm NT_ctx P (obj cx (f = v) ...))
   (lookup f_0 ((f v) ...) v_0)
   ------------------------------------------ "type-norm field of val"
   (type-norm NT_ctx (P ! f_0) v_0)]

  [(type-norm NT_ctx P (cx (f : NT) ...))
   (lookup f_0 ((f NT) ...) NT_0)
   -------------------------------------- "type-norm field of class"
   (type-norm NT_ctx (P ! f_0) NT_0)]
  
  [(type-norm NT_ctx T NT) ...
   ----------------------------------------------------- "type-norm class"
   (type-norm NT_ctx (cx (f : T) ...) (cx (f : NT) ...))]
)

(define-judgment-form DC 
  #:mode (type-norms I I O)
  #:contract (type-norms NT (T ...) (NT ...))
  
  [--------------
   (type-norms NT_ctx () ())]

  [(type-norm NT_ctx T_1 NT_1)
   (type-norms NT_ctx (T_r ...) (NT_r ...))
   ---------------------------------------------------
   (type-norms NT_ctx (T_1 T_r ...) (NT_1 NT_r ...))]
)


(define-judgment-form DC 
  #:mode (sub-type I I I)
  #:contract (sub-type NT NT (c ...))
  
;  [(where #t ,(printf "~a ~n    |- ~a <: ~a~n" (term Ctx) (term T_1) (term T_2)))
;  -----------
;  (sub-type Ctx T_1 T_2 (c ...))]

  [-------------------------- "sub-type val refl"
   (sub-type v v (c ...))]
  
  [(sub-type (cx (f : v) ...) NT (c ...))
   -------------- "sub-type val as type"
   (sub-type (obj cx (f = v) ...) NT (c ...))
  ]
  
  [(lookup f_2 ((f_1 NT_1) ...) NT_12) ...
   (sub-type NT_12 NT_2 (c ...)) ...
   ---------------------------------------------------- "sub-type equal classes"
   (sub-type (cx (f_1 : NT_1) ...) (cx (f_2 : NT_2) ...) (c ...))
  ]
  
  [(where (class cx (f : T_c) ... : T_res extends (CT_1 ... CT_ext CT_2 ...) e_c) c)
   (sub-type NT_1 T_c (c_1 ... c c_2 ...)) ...
   (type-norm (cx (f : NT_1) ...) CT_ext CT_extnorm)
   (sub-type CT_extnorm NT_2 (c_1 ... c c_2 ...))
   -------------------------- "sub-type inheritance"
   (sub-type (cx (f : NT_1) ...) NT_2 (c_1 ... c c_2 ...))
  ]
)

(define-judgment-form DC 
  #:mode (sub-types I I)
  #:contract (sub-types ((T T) ...) (c ...))
  
  [--------------
   (sub-types () (c ...))]

  [(sub-type T_1 T_2 (c ...))
   (sub-types ((T_1r T_2r) ...) (c ...))
   ---------------------------------------------------
   (sub-types ((T_1 T_2) (T_1r T_2r) ...) (c ...))]
)

(define-judgment-form DC
  #:mode (type I I O I)
  #:contract (type Ctx e NT (c ...))
  
  [;(type-ok Ctx v) -- values are always ok
   ---------------------- "type val"
   (type Ctx v v (c ...))]
  
  [;(type-ok Ctx CT) -- context should be checked when installed
   --------------------------- "type this this"
   (type NT_ctx this NT_ctx (c ...))]
  
  [(type Ctx e (obj (f_0 = v_0) ...) (c ...))
   (lookup f ((f_0 v_0) ...) v)
   ------------------------------------------ "type field of val"
   (type Ctx (e ! f) v (c ...))]

  [(type Ctx e (cx (f_0 : NT_0) ...) (c ...))
   (lookup f ((f_0 NT_0) ...) NT)
   ----------------------------------------- "type field of class"
   (type Ctx (e ! f) NT (c ...))]

  [(where (class cx (f : T_f) ... : T_res extends (CT_c ...) e_c)  c)
   (type Ctx e NT_e (c_1 ... c c_2 ...)) ...    ; type argument expressions in current context
   (type-norm (cx (f : NT_e) ...) T_f T_fnorm) ... ; normalize declared field types
   (sub-type NT_e T_fnorm (c_1 ... c c_2 ...)) ... ; check argument expressions are subtype of parameter (field) types
   (type-norm (cx (f : NT_e) ...) T_res NT_res)    ; normalize return type
   --------------------------------------------------------------- "type new"
   (type Ctx (new cx (f = e) ...) NT_res (c_1 ... c c_2 ...))]
  
)

(define-judgment-form DC
  #:mode (type-norm-fix I I O)
  #:contract (type-norm-fix CT ((f : NT) ...) ((f : NT) ...))

  [--------------------
   (type-norm-fix 
    (cx)
    ((f_n : NT_n) ...)
    ((f_n : NT_n) ...))]
  
  [(type-norm (cx (f_n : NT_n) ...) T NT)
   (type-norm-fix 
     (cx (f_1 : T_1) ... (f_2 : T_2) ...)
     ((f_n : NT_n) ... (f : NT))
     ((f_r : NT_r) ...))
   ----------------------------------------------
   (type-norm-fix 
     (cx (f_1 : T_1) ... (f : T) (f_2 : T_2) ...)
     ((f_n : NT_n) ...)
     ((f_r : NT_r) ...))]
)

(define-judgment-form DC
  #:mode (class-ok I I)
  #:contract (class-ok c (c ...))
  
  [(type-norm-fix (cx (f : T) ...) () ((f_1 : NT) ...))
   (where NT_c (cx (f_1 : NT) ...))
   (type-norm NT_c T_r NT_r)
   (type NT_c e NT_e (c ...))
   (sub-type NT_e NT_r (c ...))
   (extend-ok NT_c CT_ext (c ...)) ...
   ------------------------------------------------------------------- "class-ok"
   (class-ok (class cx (f : T) ... : T_r extends (CT_ext ...) e) (c ...))]
)

(define-judgment-form DC
  #:mode (extend-ok I I I)
  #:contract (extend-ok NT CT (c ...))
  
  [(type-norm NT_sub CT_ext (cx_ext (f_ext : NT_ext) ...))
   
   (where (class cx_ext (f_cdecl : T_fdecl) ... : T_ext extends (c_ext ...) e_ext)  c)
   (type-norm-fix (cx_ext (f_cdecl : T_fdecl) ...) () ((f_decl : NT_fdecl) ...))
   
   (lookup f_decl ((f_ext NT_ext) ...) NT_f_ext) ...
   (sub-type NT_f_ext NT_fdecl (c_1 ... c c_2 ...)) ...
   ------------------------------------------------------------------- "class-ok"
   (extend-ok NT_sub CT_ext (c_1 ... c c_2 ...))]
)

(define (tc-class c cs)
  (judgment-holds (class-ok ,c ,cs)))

;; ******************
;; test with naturals
;; ******************

(define t-Nat
  (term (class Nat
          : this
          extends ()
          this)))
(test-true "Nat is a class" (redex-match? DC c t-Nat))
(test-true "Nat class is ok" (judgment-holds (class-ok ,t-Nat (,t-Nat))))

(define t-Zero
  (term (class Zero
          : this
          extends ((Nat))
          this)))
(test-true "Zero is a class" (redex-match? DC c t-Zero))
(test-true "Zero class is ok" (judgment-holds (class-ok ,t-Zero (,t-Nat ,t-Zero))))

(define t-new-Zero
  (term (new Zero)))
(test-true "new-Zero is an expression" (redex-match? DC e t-new-Zero))
(test-true "is prog" (redex-match? DC p (term (,t-new-Zero (,t-Zero)))))
(test--> red (term (,t-new-Zero (,t-Zero))) (term ((obj Zero) (,t-Zero))))

(define t-Succ
  (term (class Succ(pred : (Nat))
          : this
          extends ((Nat))
          this)))
(test-true "Succ is a class" (redex-match? DC c t-Succ))
(test-true "Succ class is ok" (judgment-holds (class-ok ,t-Succ (,t-Nat ,t-Succ))))

(define t-new-Succ
  (term (new Succ (pred = (new Zero)))))
(test-true "new-Succ is an expression" (redex-match? DC e t-new-Succ))
(test-true "is prog" (redex-match? DC p (term (,t-new-Succ (,t-Zero ,t-Succ)))))
(test-->> red (term (,t-new-Succ (,t-Zero ,t-Succ))) (term ((obj Succ (pred = (obj Zero))) (,t-Zero ,t-Succ))))

(define t-add
  (term (class add(n1 : (Nat))(n2 : (Nat))
          : (Nat)
          extends ()
          (new Zero)))) ; dummy implementation, never used at run time
(test-true "abstract add class is ok" (judgment-holds (class-ok ,t-add (,t-Nat ,t-Zero ,t-add))))

(define t-addZero
  (term (class add(n1 : (Zero))(n2 : (Nat))
          : (Nat)
          extends ()
          (this ! n2))))
(test-true "addZero is a class" (redex-match? DC c t-addZero))
(test-true "add Zero class is ok" (judgment-holds (class-ok ,t-addZero (,t-Nat ,t-Zero ,t-addZero))))

; TODO: how does the type checker know that `n1` has field `pred`?
(define t-addSucc
  (term (class add(n1 : (Succ(pred : (Nat))))(n2 : (Nat))
          : (Nat)
          extends ()
          (new Succ (pred = (new add (n1 = ((this ! n1) ! pred)) (n2 = (this ! n2))))))))
(test-true "addSucc is a class" (redex-match? DC c t-addSucc))
(test-true "add Succ class is ok" (judgment-holds (class-ok ,t-addSucc (,t-Nat ,t-Succ ,t-add ,t-addSucc))))

(define (make-nat n)
  (if (equal? n 0)
      (term (new Zero))
      (term (new Succ (pred = ,(make-nat (- n 1)))))))
(define (make-nat-val n)
  (if (equal? n 0)
      (term (obj Zero))
      (term (obj Succ (pred = ,(make-nat-val (- n 1)))))))
(define (make-nat-add m n)
  (term (new add (n1 = ,(make-nat m)) (n2 = ,(make-nat n)))))

(define nat-classes (term (,t-Nat ,t-Zero ,t-Succ ,t-addZero ,t-addSucc)))
(define (make-nat-prog e) (term (,e ,nat-classes)))

(define ex-nat-0 (make-nat-prog (make-nat-add 0 0)))

(test-->> red (make-nat-prog (make-nat-add 0 0)) (make-nat-prog (make-nat-val 0)))
(test-->> red (make-nat-prog (make-nat-add 0 1)) (make-nat-prog (make-nat-val 1)))
(test-->> red (make-nat-prog (make-nat-add 1 0)) (make-nat-prog (make-nat-val 1)))
(test-->> red (make-nat-prog (make-nat-add 1 1)) (make-nat-prog (make-nat-val 2)))
(test-->> red (make-nat-prog (make-nat-add 3 2)) (make-nat-prog (make-nat-val 5)))


;; ******************
;; test with points
;; ******************

(define t-Space
  (term (class Space 
          : this
          extends () 
          this)))
(test-true "Space is a class" (redex-match? DC c t-Space))
(test-true "Space class is ok" (judgment-holds (class-ok ,t-Space (,t-Space))))

(define t-2DSpace
  (term (class 2DSpace
          : this
          extends ((Space))
          this)))
(test-true "2DSpace is a class" (redex-match? DC c t-2DSpace))
(test-true "2DSpace class is ok" (judgment-holds (class-ok ,t-2DSpace (,t-2DSpace ,t-Space))))

(define t-Point
  (term (class Point(s : (Space))
          : this
          extends ()
          this)))
(test-true "Point is a class" (redex-match? DC c t-Point))
(test-true "Point class is ok" (judgment-holds (class-ok ,t-Point (,t-Point ,t-Space))))

(define t-2DPoint
  (term (class Point(s : (2DSpace))
                      (x : (Nat))
                      (y : (Nat))
          : this
          extends ((Point(s : (this ! s)))) 
          this)))
(test-true "2DPoint is a class" (redex-match? DC c t-2DPoint))
(test-true "2DPoint class is ok" (judgment-holds (class-ok ,t-2DPoint (,t-2DPoint ,t-Point ,t-2DSpace ,t-Space))))

(define t-new-2DPoint
  (term (new Point (s = (new 2DSpace))(x = (new Zero))(y = (new Zero)))))
(test-true "new-2DPoint is an expression" (redex-match? DC e t-new-2DPoint))
(test-true "is prog" (redex-match? DC p (term (,t-new-2DPoint (,t-Space ,t-2DSpace ,t-Point ,t-2DPoint)))))
(test-->> red (term (,t-new-2DPoint (,t-Space ,t-2DSpace ,t-Point ,t-2DPoint ,t-Zero))) 
              (term ((obj Point (s = (obj 2DSpace))(x = (obj Zero))(y = (obj Zero))) (,t-Space ,t-2DSpace ,t-Point ,t-2DPoint ,t-Zero))))

(define t-add2D
  (term (class add  (s : (2DSpace))
                    (p1 : (Point(s : (this ! s))(x : (Nat))(y : (Nat))))
                    (p2 : (Point(s : (this ! s))(x : (Nat))(y : (Nat))))
          : (Point(s : (this ! s)))
          extends ()
          (new Point (s = (this ! s))
                       (x = (new add (n1 = ((this ! p1) ! x)) (n2 = ((this ! p2) ! x))))
                       (y = (new add (n1 = ((this ! p1) ! y)) (n2 = ((this ! p2) ! y))))))))
(test-true "add2D is a class" (redex-match? DC c t-add2D))
(test-true "add 2DPoint class is ok" (judgment-holds (class-ok ,t-add2D (,t-add2D ,t-2DPoint ,t-Point ,t-2DSpace ,t-Space ,t-Nat ,t-add))))

 
(define 2DPoint-classes (term (,t-Space ,t-2DSpace ,t-Point ,t-2DPoint ,t-add2D)))
(define (make-point-prog e) (term (,e ,(append nat-classes 2DPoint-classes))))
(test-true "is prog" (redex-match? DC p (make-point-prog (term (new Space)))))

(test-true "is prog" (redex-match? DC p (make-point-prog
               (term (new add  (s = (new 2DSpace))
                               (p1 = (new Point(s = (this ! s))(x = ,(make-nat 0))(y = ,(make-nat 1))))
                               (p2 = (new Point(s = (this ! s))(x = ,(make-nat 1))(y = ,(make-nat 0)))))))))
(test-->> red (make-point-prog
               (term (new add  (s = (new 2DSpace))
                               (p1 = (new Point(s = (new 2DSpace))(x = ,(make-nat 0))(y = ,(make-nat 1))))
                               (p2 = (new Point(s = (new 2DSpace))(x = ,(make-nat 1))(y = ,(make-nat 0)))))))
              (make-point-prog
               (term (obj Point(s = (obj 2DSpace))(x = ,(make-nat-val 1))(y = ,(make-nat-val 1))))))


(define t-3DSpace
  (term (class 3DSpace
          : this
          extends ((Space))
          this)))
(test-true "3DSpace is a class" (redex-match? DC c t-3DSpace))
(test-true "3DSpace class is ok" (judgment-holds (class-ok ,t-3DSpace (,t-3DSpace ,t-Space))))

(define t-3DPoint
  (term (class Point(s : (3DSpace))
                      (x : (Nat))
                      (y : (Nat))
                      (z : (Nat))
          : this
          extends ((Point(s : (this ! s)))) 
          this)))
(test-true "3DPoint is a class" (redex-match? DC c t-3DPoint))
(test-true "3DPoint class is ok" (judgment-holds (class-ok ,t-3DPoint (,t-3DPoint ,t-Point ,t-3DSpace ,t-Space))))

(define t-add3D
  (term (class add(s : (3DSpace))
                    (p1 : (Point(s : (this ! s))(x : (Nat))(y : (Nat))(z : (Nat))))
                    (p2 : (Point(s : (this ! s))(x : (Nat))(y : (Nat))(z : (Nat))))
          : (Point(s : (this ! s)))
          extends ()
          (new Point (s = (this ! s))
                       (x = (new add (n1 = ((this ! p1) ! x)) (n2 = ((this  ! p2) ! x))))
                       (y = (new add (n1 = ((this ! p1) ! y)) (n2 = ((this ! p2) ! y))))
                       (z = (new add (n1 = ((this ! p1) ! z)) (n2 = ((this ! p2) ! z))))))))
(test-true "add3D is a class" (redex-match? DC c t-add2D))
(test-true "add 3DPoint class is ok" (judgment-holds (class-ok ,t-add3D (,t-add3D ,t-3DPoint ,t-Point ,t-3DSpace ,t-Space ,t-Nat ,t-add))))

(define 3Dpoint-classes (term (,t-Space ,t-2DSpace ,t-Point ,t-2DPoint ,t-add2D ,t-3DSpace ,t-3DPoint ,t-add3D)))
(define (make-3DPoint-prog e) (term (,e ,(append nat-classes 3Dpoint-classes))))
(test-true "is prog" (redex-match? DC p (make-point-prog (term (new Space)))))

(define add-3D-points
  (term (new add  (s =  (new 3DSpace))
                               (p1 = (new Point(s = (this ! s))(x = ,(make-nat 0))(y = ,(make-nat 1))(z = ,(make-nat 2))))
                               (p2 = (new Point(s = (this ! s))(x = ,(make-nat 2))(y = ,(make-nat 1))(z = ,(make-nat 0)))))))

(test-true "is prog" (redex-match? DC p (make-3DPoint-prog add-3D-points)))
(test-->> red (make-3DPoint-prog add-3D-points)
              (make-3DPoint-prog
               (term (obj Point(s = (obj 3DSpace))(x = ,(make-nat-val 2))(y = ,(make-nat-val 2))(z = ,(make-nat-val 2))))))
(test-true "add 3D points is well-typed"
  (judgment-holds (type empty ,add-3D-points NT ,(append nat-classes (list t-add) 3Dpoint-classes))))

; Cannot add 2D point to 3D point -> program gets stucks
(define add-2D-3D-points
  (term (new add  (s =  (new 3DSpace))
                               (p1 = (new Point(s = (new 2DSpace))(x = ,(make-nat 0))(y = ,(make-nat 1))))
                               (p2 = (new Point(s = (new 3DSpace))(x = ,(make-nat 2))(y = ,(make-nat 1))(z = ,(make-nat 0)))))))
(test-true "is prog" (redex-match? DC p (make-3DPoint-prog add-2D-3D-points)))
(test-->> red (make-3DPoint-prog add-2D-3D-points)
              (make-3DPoint-prog
               (term (new add  (s =  (obj 3DSpace))
                               (p1 = (obj Point(s = (obj 2DSpace))(x = ,(make-nat-val 0))(y = ,(make-nat-val 1))))
                               (p2 = (obj Point(s = (obj 3DSpace))(x = ,(make-nat-val 2))(y = ,(make-nat-val 1))(z = ,(make-nat-val 0))))))))
(test-false "add 2D and 3D points is ill-typed"
  (judgment-holds (type empty ,add-2D-3D-points NT ,(append nat-classes (list t-add) 3Dpoint-classes))))

