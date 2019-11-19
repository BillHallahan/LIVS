(set-logic LIA)

(synth-fun f ((x Int)) Int
     ((Start Int (ntInt))
      (ntInt Int ((Constant Int) x
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (* ntInt ntInt)
       ))))


(declare-var x Int)
 
(constraint (> (f 3) 20))
(constraint (= (f 4) (f (f 4))))
 
(check-synth)

