(set-logic SLIA)

(define-fun usedBefore ((user String) (password String)) Bool (= password "mark1"))
(define-fun containsNums ((password String)) Bool (str.contains password (int.to.str 1)))

(synth-fun checkBadPassword ((user String) (password String)) String
     ((Start String (ntString))
      (ntString String (user password "Your password must contain numbers" "You alreay used a version of that password"
                       (ite ntBool ntString ntString)
                       (str.substr ntString ntInt ntInt)))
      (ntInt Int (0 
                  (str.to.int ntString)
                  (str.indexof ntString ntString ntInt)))
      (ntBool Bool (
  ;                  (usedBefore ntString ntString)
                    (containsNums ntString)
                    ))))


(declare-var name String)
 
(constraint (= (checkBadPassword "mark" "mark") "Your password must contain numbers"))
(constraint (= (checkBadPassword "mark" "jack") "jack"))
; (constraint (= (checkBadPassword "mark" "mark1") "You already used a version of that password"))

 
(check-synth)

