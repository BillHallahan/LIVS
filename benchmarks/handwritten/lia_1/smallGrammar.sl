(set-logic LIA)

(synth-fun f ((x Int)) Int
     ((Start Int (ntInt))
      (ntInt Int (0 1 2 x
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (* ntInt ntInt)
       ))))


(declare-var x Int)
 
(constraint (= (f 3) 20))
(constraint (= (f 4) 34))
 
(check-synth)

