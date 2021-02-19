(set-logic LIA)
(set-feature :fwd-decls true)
(set-feature :recursion true)
(define-fun x_plus_one ((x Int)) Int (+ x 1))
(synth-fun f ((x Int)) Int
    ((I Int))
    ((I Int (0 1 x (x_plus_one I)))))
(define-fun fx_plus_one ((x Int)) Int (+ (f x) 1))
(synth-fun g ((x Int)) Int
    ((I Int))
    ((I Int (0 1 x (fx_plus_one I)))))
(synth-fun h ((x Int)) Int
    ((I Int) (B Bool))
    ((I Int (0 1 x (- I 1) (+ I I) (h I) (ite B I I)))
    (B Bool ((= I I) (> I I)))))
(declare-var y Int)
(constraint (= (h y) (- (g y) (f y))))
(check-synth)