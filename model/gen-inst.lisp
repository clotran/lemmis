; gen-inst: g-fn-sem (gen-fn.lisp) for clotran's own functions. The
; constants are what ACL2 hands acl2-fortran for the functions check-gen
; compares (check-gen.bb checks they are still what clotran's certified books
; hand over). For each call-free, loop-free function, the procedure g-module
; makes (found by its Fortran name, as fsem's call finds it) answers, on int64
; arguments, what a-ev says the body means, whenever a-ev answers without an
; error (in particular without :range: int64 range is a hypothesis, GEN.md).

(in-package "ACL2")

(include-book "gen-fn")

(defconst *heapgn-raw* '(
(hpg-add (n k)
         (nil)
         t
         ((lambda (s)
            (if (< s '1099511627776)
                s
              '1099511627776))
          (binary-+ (nfix n) (nfix k))))
(hpg-text-tag (tag)
              (nil)
              t
              (if (equal tag '5)
                  (equal tag '5)
                (if (equal tag '6)
                    (equal tag '6)
                  (if (equal tag '7)
                      (equal tag '7)
                    (if (equal tag '11)
                        (equal tag '11)
                      (if (equal tag '12)
                          (equal tag '12)
                        (if (equal tag '13)
                            (equal tag '13)
                          (equal tag '15))))))))
(hpg-s64 (x)
         (nil)
         t
         (if (if (integerp x)
                 (if (not (< x '-9223372036854775808))
                     (< x '9223372036854775808)
                   'nil)
               'nil)
             x
           '0))
(hpg-n40 (x) (nil) t (if (if (natp x) (not (< '1099511627776 x)) 'nil) x '0))
(hpg-size-class (n c p)
                (nil)
                t
                (if (if (not (natp p))
                        (not (natp p))
                      (if (< p '1)
                          (< p '1)
                        (if (not (< p n))
                            (not (< p n))
                          (if (< '1099511627776 p)
                              (< '1099511627776 p)
                            (if (not (natp c))
                                (not (natp c))
                              (not (< c '64)))))))
                    c
                  (hpg-size-class n (binary-+ '1 c)
                                  (binary-* '2 p))))
(hpg-class-len (c k p)
               (nil)
               t
               (if (if (not (natp c))
                       (not (natp c))
                     (if (not (natp k))
                         (not (natp k))
                       (if (not (< k c))
                           (not (< k c))
                         (< '64 c))))
                   (hpg-n40 p)
                 (hpg-class-len c (binary-+ '1 k)
                                (hpg-n40 (binary-* '2 (hpg-n40 p))))))))

(defconst *vmfg-raw* '(
(bnd40p (x)
        (nil)
        t
        (if (integerp x)
            (if (not (< x '0))
                (not (< '1099511627776 x))
              'nil)
          'nil))
(sk-step (kd i cnt)
         (nil)
         t
         (if (equal kd '1)
             '1
           (if (equal kd '2)
               (if (if (integerp i)
                       (if (integerp cnt)
                           (if (not (< i '0)) (< i cnt) 'nil)
                         'nil)
                     'nil)
                   '2
                 '0)
             (if (equal kd '3)
                 '3
               (if (equal kd '5)
                   '5
                 (if (equal kd '0) '0 '4))))))
(sk-more (d)
         (nil)
         t
         (if (equal d '1)
             (equal d '1)
           (if (equal d '2)
               (equal d '2)
             (equal d '5))))
(ex-aplook (req k)
           (nil)
           t
           (if (if (integerp req)
                   (if (not (< req '0))
                       (if (integerp k)
                           (not (< (binary-+ req '1) k))
                         'nil)
                     'nil)
                 'nil)
               '1
             '0))
(ex-apstep (req k more)
           (nil)
           t
           (if (not (if (integerp req)
                        (if (not (< req '0)) (integerp k) 'nil)
                      'nil))
               '3
             (if (if (< k req) (equal more '1) 'nil)
                 '1
               (if (if (< req k) (< req k) (equal more '1))
                   '2
                 '3))))))

(defconst *vmicg-raw* '(
(vmicg-sat (x) (nil) t (if (< x '1099511627776) x '1099511627776))))

(defconst *heapgn-bools* '(hpg-text-tag))
(defconst *vmfg-bools* '(bnd40p sk-more))
(defconst *vmicg-bools* nil)

(defmacro gen-fn-thm (name fn fname raw bools)
  (let ((defs `(g-defs ,raw)) (sigs `(g-sigs ,raw ,bools)))
    `(defthm ,name
       (let ((d (lkp ',fn ,defs)) (p (find-proc ,fname (mv-nth 1 (g-module ,raw ,bools)))))
         (implies (and (int64-listp args) (equal (len args) (len (kadr d)))
                       (not (mv-nth 0 (a-ev (kaddr d) (pairlis$ (kadr d) args) ,defs n)))
                       (integerp fuel) (< (+ 6 (len args) (acl2-count p)) fuel))
                  (equal (f-invoke p (g-lits args) caller heap procs fuel)
                         (mv nil (mv-nth 1 (a-ev (kaddr d) (pairlis$ (kadr d) args) ,defs n)) heap))))
       :hints (("Goal" :in-theory (disable a-ev f-invoke int64-listp g-lits pairlis$ len)
                :use (:instance g-fn-sem (fn ',fn) (defs ,defs) (sigs ,sigs)))))))

(gen-fn-thm hpg-add-gen hpg-add "hpg_add" *heapgn-raw* *heapgn-bools*)
(gen-fn-thm hpg-text-tag-gen hpg-text-tag "hpg_text_tag" *heapgn-raw* *heapgn-bools*)
(gen-fn-thm hpg-s64-gen hpg-s64 "hpg_s64" *heapgn-raw* *heapgn-bools*)
(gen-fn-thm hpg-n40-gen hpg-n40 "hpg_n40" *heapgn-raw* *heapgn-bools*)
(gen-fn-thm bnd40p-gen bnd40p "bnd40p" *vmfg-raw* *vmfg-bools*)
(gen-fn-thm sk-step-gen sk-step "sk_step" *vmfg-raw* *vmfg-bools*)
(gen-fn-thm sk-more-gen sk-more "sk_more" *vmfg-raw* *vmfg-bools*)
(gen-fn-thm ex-aplook-gen ex-aplook "ex_aplook" *vmfg-raw* *vmfg-bools*)
(gen-fn-thm ex-apstep-gen ex-apstep "ex_apstep" *vmfg-raw* *vmfg-bools*)
(gen-fn-thm vmicg-sat-gen vmicg-sat "vmicg_sat" *vmicg-raw* *vmicg-bools*)
