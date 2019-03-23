(set-logic SLIA)

(define-fun h ((x Int)) Int (* (+ x 2) x))
(define-fun g ((x Int) (y Int)) Int (- (* x y) (h y)))


(synth-fun f ((x Int) (y Int)) Int
     ((Start Int (ntInt))
      (ntString String (" "
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntInt)
                       (str.substr ntString ntInt ntInt)))
      (ntInt Int (0 1 2 x y
                  (g ntInt ntInt)
                  (h ntInt)
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (* ntInt ntInt)
                  (str.len ntString)
                  (str.to.int ntString)
                  (str.indexof ntString ntString ntInt)))
      (ntBool Bool (true false
                    (str.prefixof ntString ntString)
                    (str.suffixof ntString ntString)
                    (str.contains ntString ntString)))))


(constraint (= (f 3 2) -5))
(constraint (= (f 4 7) -39))
 
(check-synth)

