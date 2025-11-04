(set-logic UF) ; Uninterpreted Functions

; There are 4 states; the invalid state is a convenience mechanism to make
; send1/recv1 be partial functions.
; Remove `Other` to confirm unsat.
(declare-datatypes () ((State Init SndPending RcvPending SR Other Invalid)))

; chan send = send1; send2, chan recv = recv1; recv2
(declare-fun send1 (State) State)
(declare-fun recv1 (State) State)
(declare-fun send2 (State State) State)
(declare-fun recv2 (State State) State)

; WOLOG:
(assert (= (send1 Init) SndPending))
(assert (= (recv1 Init) RcvPending))

; Valid interleavings
(define-fun srsr () State
  (let ((st1 (send1 Init)))
  (let ((st2 (recv1 st1)))
  (let ((st3 (send2 st1 st2)))
    (recv2 st2 st3)))))

(define-fun srrs () State
  (let ((st1 (send1 Init)))
  (let ((st2 (recv1 st1)))
  (let ((st3 (recv2 st2 st2)))
    (send2 st1 st3)))))

(define-fun rsrs () State
  (let ((st1 (recv1 Init)))
  (let ((st2 (send1 st1)))
  (let ((st3 (recv2 st1 st2)))
    (send2 st2 st3)))))

(define-fun rssr () State
  (let ((st1 (recv1 Init)))
  (let ((st2 (send1 st1)))
  (let ((st3 (send2 st2 st2)))
    (recv2 st1 st3)))))

; The final state is always valid
(assert (not (= srsr Invalid)))
(assert (not (= srrs Invalid)))
(assert (not (= rsrs Invalid)))
(assert (not (= rssr Invalid)))

; All interleavings result in the same final state
(assert (= srsr Init))
(assert (= srsr srrs))
(assert (= srrs rsrs))
(assert (= rsrs rssr))
(assert (= rssr srsr))

; The Invalid state is like "None"
(assert (= (send1 Invalid) Invalid))
(assert (= (recv1 Invalid) Invalid))
(assert (forall ((st State)) (= (send2 st Invalid) Invalid)))
(assert (forall ((st State)) (= (recv2 st Invalid) Invalid)))

; Invalid sequences.
; s1 s1
(assert (= (send1 (send1 Init)) Invalid))
; r1 r1
(assert (= (recv1 (recv1 Init)) Invalid))
; s2(Init)
(assert (forall ((st State)) (= (send2 st Init) Invalid)))
; r2(Init)
(assert (forall ((st State)) (= (recv2 st Init) Invalid)))
; r1;s2
(assert (forall ((st State)) (= (send2 st (recv1 Init)) Invalid)))
; s1;r2
(assert (forall ((st State)) (= (recv2 st (send1 Init)) Invalid)))

; send1 and recv1 are not identity functions for any state
(assert (forall ((st State)) (=> (not (= st Invalid)) (not (= (send1 st) st)))))
(assert (forall ((st State)) (=> (not (= st Invalid)) (not (= (recv1 st) st)))))

; srss invalid
(define-fun srss () State
  (let ((st1 (send1 Init)))
  (let ((st2 (recv1 st1)))
  (let ((st3 (send2 st1 st2)))
    (send1 st3)))))
(assert (= srss Invalid))

; rsrr invalid
(define-fun rsrr () State
  (let ((st1 (recv1 Init)))
  (let ((st2 (send1 st1)))
  (let ((st3 (recv2 st1 st2)))
    (recv1 st3)))))
(assert (= rsrr Invalid))

; rsss invalid
(define-fun rsss () State
  (let ((st1 (recv1 Init)))
  (let ((st2 (send1 st1)))
  (let ((st3 (send2 st2 st2)))
    (send1 st3)))))
(assert (= rsss Invalid))

; srrr invalid
(define-fun srrr () State
  (let ((st1 (send1 Init)))
  (let ((st2 (recv1 st1)))
  (let ((st3 (recv2 st2 st2)))
    (recv1 st3)))))
(assert (= srrr Invalid))

(check-sat)
(get-model)
