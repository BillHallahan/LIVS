(set-logic SLIA)

(define-fun g ((x Int)) Int (* (* x x) 3))
(define-fun h ((x Int)) Int (+ x 3))


(synth-fun f ((x Int)) Int
     ((Start Int (ntInt))
      (ntString String (" "
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntInt)
                       (str.substr ntString ntInt ntInt)))
      (ntInt Int (0 1 2 3 x 
                  (g ntInt)
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


(constraint (= (f 3) 30))
(constraint (= (f 4) 51))
 
(check-synth)

