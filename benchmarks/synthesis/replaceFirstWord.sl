(set-logic SLIA)

(define-fun firstWord  ((s String)) String (str.substr s 0 (str.indexof s " " 1)))

(synth-fun f ((name String)) String
    ((Start String (ntString))
     (ntString String (name "Hey"
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntInt)
                       (firstWord ntString)
                       (replaceAll ntString ntString ntString)
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
 
(constraint (= (f "Hello World") "Hey World"))
(constraint (= (f "Hello Moon") "Hey Moon"))
 
(check-synth)

