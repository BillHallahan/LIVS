(set-logic SLIA)


(synth-fun f ((s String) (o String) (n String)) String
    ((Start String (ntString))
     (ntString String (s o n
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntInt)
                       (str.substr ntString ntInt ntInt)))
      (ntInt Int (0 1
                  (+ ntInt ntInt)
                  (- ntInt ntInt)
                  (str.len ntString)
                  (str.to.int ntString)
                  (str.indexof ntString ntString ntInt)))
      (ntBool Bool (true false
                    (str.prefixof ntString ntString)
                    (str.suffixof ntString ntString)
                    (str.contains ntString ntString)))))


(declare-var name String)
 
(constraint (= (f "Hello" "Hey" "Hello World Hello") "Hey World Hey"))
(constraint (= (f "Hello" "Hey" "Hello Moon") "Hey Moon"))
 
(check-synth)

