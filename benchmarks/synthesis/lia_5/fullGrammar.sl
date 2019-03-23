(set-logic SLIA)

(define-fun i ((x Int)) Int (+ x (- x 2)))
(define-fun h ((x Int)) Int (* (+ x 2) x))
(define-fun g ((x Int) (y Int)) Int (- (* x y) (h y)))

; cvc4 has a really hard time with this as the grammar grows
; takes 40 sec with this grammar on my machine
(synth-fun f ((x Int) (y Int)) Int
     ((Start Int (ntInt))
      (ntInt Int (0 x y
                  (g ntInt ntInt)
                  (h ntInt)
                  (i ntInt)
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (* ntInt ntInt)))))


(constraint (= (f 3 2) -6))
(constraint (= (f 4 7) -41))
 
(check-synth)

