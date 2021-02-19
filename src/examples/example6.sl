(set-logic INV_LIA)
(synth-inv inv-f ((x Int) (y Int)))
(define-fun pre-f ((x Int) (y Int)) Bool
    (and (>= x 5) (<= x 9) (>= y 1) (<= y 3)))
(define-fun trans-f ((x Int) (y Int) (xp Int) (yp Int)) Bool
    (and (= xp (+ x 2)) (= yp (+ y 1))))
(define-fun post-f ((x Int) (y Int)) Bool (< y x))
(inv-constraint inv-f pre-f trans-f post-f)
(check-synth)