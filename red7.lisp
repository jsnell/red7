(defpackage #:red7
  (:use #:CL))

(in-package #:red7)

(declaim (optimize (debug 2)))

(eval-when (:load-toplevel :compile-toplevel)
  (defparameter *colors* '(red orange yellow green blue indigo violet))
  (loop for color in *colors*
        for value from 7 downto 1
        do (setf (symbol-value color) value)))

;; A card is an integer between 0 and 55 (inclusive). The low 3 bits
;; are the color, with a "0" being a dummy color that's not used in
;; any way. The next 3 bits are the card's numeric value - 1 (0-6).
(deftype card () '(mod 56))

;; An unordered collection of cards is represented as a 56-bit integer.
(deftype card-set () '(unsigned-byte 56))

(defun card-color (card)
  (ldb (byte 3 0) card))

(defun card-value (card)
  (1+ (ash card -3)))

(defstruct (deck (:constructor %make-deck))
  (cards (make-array 49 :element-type 'card)
         :type (simple-array card (49)))
  (size 0 :type (integer 0 49)))

(defstruct (player)
  id
  eliminated
  (hand nil :type card-set)
  (canvas nil :type card-set)
  (next-player nil :type (or null player)))

(defstruct (game)
  (players nil :type list)
  (current nil :type (or null player))
  (deck (make-deck) :type deck)
  (discard nil :type list))

(defmethod print-object ((player player) stream)
  (print-unreadable-object (player stream :type 'player)
    (format stream ":ID ~A :HAND ~A :CANVAS ~A :NEXT-PLAYER ~A"
            (player-id player)
            (cards-to-list (player-hand player))
            (cards-to-list (player-canvas player))
            (let ((next (player-next-player player)))
              (if next
                  (player-id next)
                  nil)))))

(defun card-label (card)
  (format nil "~A-~A"
          (nth (- 7 (card-color card)) *colors*)
          (card-value card)))

(defun make-deck ()
  (let ((deck (%make-deck)))
    (dotimes (value 7)
      (dolist (color *colors*)
        (setf (aref (deck-cards deck) (deck-size deck))
              (logior (symbol-value color)
                      (ash value 3)))
        (incf (deck-size deck))))
    (shuffle-deck deck)
    deck))

(defun shuffle-deck (deck)
  (let ((size (deck-size deck)))
    (dotimes (i size)
      (rotatef (aref (deck-cards deck) i)
               (aref (deck-cards deck) (random size))))))

(defun draw-from-deck (deck)
  (aref (deck-cards deck) (decf (deck-size deck))))

(defun undo-draw (deck)
  (incf (deck-size deck)))

(defun card-score (card)
  card)

(defun remove-card (card card-set)
  (declare (type card card)
           (type card-set card-set))
  (logand card-set (lognot (ash 1 card))))

(defun add-card (card card-set)
  (declare (type card card)
           (type card-set card-set))
  (logior card-set (ash 1 card)))

(defun cards-to-list (card-set)
  (loop for i from 0 below 55
        when (logbitp i card-set)
        collect (card-label i)))

(defun make-card-set (cards)
  (let ((set 0))
    (dolist (card cards)
      (setf set (logior set (ash 1 card))))
    set))

(defmacro do-cards ((card card-set) &body body)
  `(loop for ,card from 55 downto 0
         when (logbitp ,card ,card-set)
         do ,@body))

(defun player-score (player type)
  (labels ((score-for-condition (condition)
             (let ((matching-cards 0)
                   (best-matching-card 0))
               (do-cards (card (player-canvas player))
                 (when (funcall condition card)
                   (incf matching-cards)
                   (when (zerop best-matching-card)
                     (setf best-matching-card (card-score card)))))
               (+ best-matching-card (* 100 matching-cards)))))
    (ecase type
      (#.red
       (do-cards (card (player-canvas player))
         ;; Score of first card.
         (return (card-score card))))
      (#.orange
       (loop for value from 1 to 7
             maximize (score-for-condition
                       (lambda (card)
                         (eq value (card-value card))))))
      (#.yellow
       (loop for color in *colors*
             maximize (score-for-condition
                       (lambda (card)
                         (eq color (card-color card))))))
      (#.green
       (score-for-condition (lambda (card)
                              (evenp (card-value card)))))
      (#.blue
       (let ((colors-seen (make-array 7 :initial-element nil))
             (color-count 0)
             (best-card nil))
         (do-cards (card (player-canvas player))
           (let ((index (1- (card-color card))))
             (unless (aref colors-seen index)
               (setf (aref colors-seen index) t)
               (incf color-count)
               (unless best-card
                 (setf best-card (card-score card))))))
         (+ (* 100 color-count) best-card)))
      (#.indigo
       (let ((prev nil)
             (current-run-score 0)
             (best-score 0))
         (do-cards (card (player-canvas player))
           (cond ((not prev)
                  (setf current-run-score (card-score card))
                  (setf prev card))
                 ((= (card-value card) (card-value prev)))
                 ((= (card-value card) (1- (card-value prev)))
                  (incf current-run-score 100)
                  (setf prev card))
                 (t
                  (setf current-run-score (card-score card))
                  (setf prev card)))
           (setf best-score (max best-score current-run-score)))
         best-score))
      (#.violet
       (score-for-condition (lambda (card)
                              (< (card-value card) 4)))))))

(defun who-is-winning (game)
  (let ((type (if (game-discard game)
                  (card-color (first (game-discard game)))
                  #.red))
        ;; Note: all scoring types must score 0 when the canvas doesn't match
        ;; at all.
        (best-score 0)
        best-player)
    (dolist (player (game-players game))
      (unless (player-eliminated player)
        (let ((score (player-score player type)))
          (when (> score best-score)
            (setf best-score score
                  best-player player)))))
    best-player))

(defun valid-moves (game player)
  (let (valid-moves)
    (labels ((check-discards (play-card)
               (do-cards (discard-card (player-hand player))
                 (unless (eq play-card discard-card)
                   (push discard-card (game-discard game))
                   (when (eq player (who-is-winning game))
                     (push (list (cons :play play-card)
                                 (cons :discard discard-card))
                           valid-moves))
                   (pop (game-discard game)))))
             (check-plays (check-discards)
               (do-cards (play-card (player-hand player))
                 (when play-card
                   (setf (player-canvas player)
                         (add-card play-card (player-canvas player)))
                   (when (eq player (who-is-winning game))
                     (push (list (cons :play play-card)) valid-moves)))
                 (when check-discards
                   (check-discards play-card))
                 (when play-card
                   (setf (player-canvas player)
                         (remove-card play-card (player-canvas player)))))))
      (check-plays nil)
      (check-plays t)
      (check-discards nil))
    valid-moves))

(defun execute-move (game player move)
  (format t "  executing move ~a~%" move)
  (dolist (submove move)
    (let ((kind (car submove))
          (card (cdr submove)))
      (when (and (eq kind :play) card)
        (setf (player-canvas player)
              (add-card card (player-canvas player)))
        (setf (player-hand player)
              (remove-card card (player-hand player))))
      (when (and (eq kind :discard) card)
        (push card (game-discard game))
        (setf (player-hand player)
              (remove-card card (player-hand player)))
        (when (> (card-value card) (logcount (player-canvas player)))
          (let ((draw (draw-from-deck (game-deck game))))
            (format t "  gain ~a from discard~%" (card-label draw))
            (add-card draw (player-hand player)))))))
  (assert (eq player (who-is-winning game))))

(defun play (player-count)
  (let* ((game (make-game))
         (deck (game-deck game)))
    ;; (push (draw-from-deck deck)
    ;;       (game-discard game))
    (dotimes (i player-count)
      (let ((player (make-player :id i
                                 :canvas (make-card-set (list
                                                         (draw-from-deck deck)))
                                 :hand (make-card-set (loop repeat 5
                                                            collect (draw-from-deck deck))))))
        (push player (game-players game))))
    (mapcar (lambda (player next)
              (setf (player-next-player player) next))
            (game-players game)
            (cdr (append (game-players game) (game-players game))))
    (let ((leader (who-is-winning game))
          (players-left player-count)
          (turns 0))
      (loop
         (when (= players-left 1)
           (return-from play (list :gameover :turns turns)))
         (dotimes (p (1- player-count))
           (setf leader (player-next-player leader))
           (unless (player-eliminated leader)
             (return)))
         (let* ((moves (valid-moves game leader))
                (move-count (length moves))
                (move (unless (zerop move-count)
                        (nth (random move-count) moves))))
           (format t "player ~a has ~d moves~%"
                   leader move-count)
           (cond ((not move)
                  (format t "player ~a eliminated~%~a" leader game)
                  (decf players-left)
                  (setf (player-eliminated leader) t))
                 (t
                  (incf turns)
                  (execute-move game leader move))))))))
