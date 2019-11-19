(set-logic SLIA)

(define-fun g ((x Int) (y Int)) Int (- (* x y) y))


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


(constraint (= (f 3 2) 12))
(constraint (= (f 4 5) 60))
 
(check-synth)

