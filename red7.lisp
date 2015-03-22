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

(deftype card-index () '(mod 56))

(declaim (inline card-color))
(defun card-color (card)
  (declare (type card card))
  (ldb (byte 3 0) card))

(declaim (inline card-value))
(defun card-value (card)
  (declare (type card card))
  (1+ (ash card -3)))

(defstruct (deck (:constructor %make-deck))
  (cards (make-array 49 :element-type 'card)
         :type (simple-array card (49)))
  (size 0 :type (integer 0 49)))

(defstruct (player)
  id
  eliminated
  (hand nil :type card-set)
  (palette nil :type card-set)
  (next-player nil :type (or null player)))

(defstruct (game)
  (players nil :type list)
  (current nil :type (or null player))
  (deck (make-deck) :type deck)
  (canvas nil :type list))

(defmethod print-object ((player player) stream)
  (print-unreadable-object (player stream :type 'player)
    (format stream ":ID ~A :HAND ~A :PALETTE ~A :NEXT-PLAYER ~A"
            (player-id player)
            (cards-to-list (player-hand player))
            (cards-to-list (player-palette player))
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
  (prog1
      (aref (deck-cards deck) (deck-size deck))
    (incf (deck-size deck))))

(declaim (inline card-score))
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
  (loop for i from 55 downto 0
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
  (declare (optimize speed))
  (labels ((score-for-mask (mask)
             (let ((matching-cards (logand (player-palette player)
                                           mask)))
               (let ((matching-cards (logcount matching-cards))
                     (best-matching-card (integer-length matching-cards)))
                 (declare (type (mod 64) matching-cards best-matching-card))
                 (+ best-matching-card (* 64 matching-cards)))))
           (red ()
             (card-score (integer-length (player-palette player))))
           (orange ()
             (loop for mask of-type card-set = #xff000000000000 then (ash mask -8)
                   repeat 7
                   maximize (score-for-mask mask)))
           (yellow ()
             (loop for mask of-type card-set = #x80808080808080 then (ash mask -1)
                   repeat 7
                   maximize (score-for-mask mask)))
           (green ()
             (score-for-mask #x00ff00ff00ff00))
           (blue ()
             (let* ((palette (player-palette player))
                    (best-card (card-score (integer-length palette)))
                    (colors 0))
               (declare (type (mod 64) best-card)
                        (type card-set colors))
               ;; Collapse all the card values out together, leaving
               ;; only one bit per color that's present.
               (loop with mask of-type card-set = #xff
                     for value of-type card-set = palette then (ash value -8)
                     repeat 7
                     do (setf colors (logior colors (logand mask value))))
               (+ best-card (* 64 (the (mod 64)
                                       (logcount colors))))))
           (indigo ()
             (let ((prev nil)
                   (current-run-score 0)
                   (best-score 0))
               (declare (type (unsigned-byte 16) current-run-score best-score))
               (do-cards (card (player-palette player))
                 (cond ((not prev)
                        (setf current-run-score (card-score card))
                        (setf prev card))
                       ((= (card-value card) (card-value prev)))
                       ((= (card-value card) (1- (card-value prev)))
                        (incf current-run-score 64)
                        (setf prev card))
                       (t
                        (setf current-run-score (card-score card))
                        (setf prev card)))
                 (setf best-score (max best-score current-run-score)))
               best-score))
           (violet ()
             (score-for-mask #x00000000ffffff)))
    (declare (inline score-for-mask)
             (notinline red orange yellow green blue indigo violet))
    (ecase type
      (#.red (red))
      (#.orange (orange))
      (#.yellow (yellow))
      (#.green (green))
      (#.blue (blue))
      (#.indigo (indigo))
      (#.violet (violet)))))

(defun who-is-winning (game)
  (declare (optimize speed))
  (let ((type (if (game-canvas game)
                  (card-color (first (game-canvas game)))
                  #.red))
        ;; Note: all scoring types must score 0 when the palette doesn't match
        ;; at all.
        (best-score 0)
        best-player)
    ;; (format t "---~%canvas ~a~%" (when (game-canvas game)
    ;;                                (card-label (first (game-canvas game)))))
    (dolist (player (game-players game))
      (unless (player-eliminated player)
        (let ((score (player-score player type)))
          ;; (format t "player ~a, palette ~a, score ~a~%"
          ;;         (player-id player)
          ;;         (cards-to-list (player-palette player))
          ;;         score)
          (when (> score best-score)
            (setf best-score score
                  best-player player)))))
    best-player))

(defun valid-moves (game player)
  (declare (optimize speed))
  (let (valid-moves)
    (labels ((check-discard (play-card)
               (do-cards (canvas-card (player-hand player))
                 (unless (eq play-card canvas-card)
                   (push canvas-card (game-canvas game))
                   (when (eq player (who-is-winning game))
                     (push (list (cons :play play-card)
                                 (cons :discard canvas-card))
                           valid-moves))
                   (pop (game-canvas game)))))
             (check-plays (check-discard)
               (do-cards (play-card (player-hand player))
                 (when play-card
                   (setf (player-palette player)
                         (add-card play-card (player-palette player)))
                   (when (eq player (who-is-winning game))
                     (push (list (cons :play play-card)) valid-moves)))
                 (when check-discard
                   (check-discard play-card))
                 (when play-card
                   (setf (player-palette player)
                         (remove-card play-card (player-palette player)))))))
      (check-plays nil)
      (check-plays t)
      (check-discard nil))
    valid-moves))

(defun execute-move (game player move)
  (dolist (submove move)
    (let ((kind (car submove))
          (card (cdr submove)))
      ;; (when card
      ;;   (format t "  executing ~a ~a~%" kind (card-label card)))
      (when (and (eq kind :play) card)
        (setf (player-palette player)
              (add-card card (player-palette player)))
        (setf (player-hand player)
              (remove-card card (player-hand player))))
      (when (and (eq kind :discard) card)
        (push card (game-canvas game))
        (setf (player-hand player)
              (remove-card card (player-hand player)))
        (when (> (card-value card) (logcount (player-palette player)))
          (let ((draw (draw-from-deck (game-deck game))))
            ;; (format t "  gain ~a from discard~%" (card-label draw))
            (setf (player-hand player)
                  (add-card draw (player-hand player))))))))
  (assert (eq player (who-is-winning game))))

(defun undo-move (game player move)
  (dolist (submove (reverse move))
    (let ((kind (car submove))
          (card (cdr submove)))
      ;; (when card
      ;;   (format t "  undoing ~a ~a~%" kind (card-label card)))
      (when (and (eq kind :play) card)
        (setf (player-palette player)
              (remove-card card (player-palette player)))
        (setf (player-hand player)
              (add-card card (player-hand player))))
      (when (and (eq kind :discard) card)
        (assert (= card (pop (game-canvas game))))
        (setf (player-hand player)
              (add-card card (player-hand player)))
        (when (> (card-value card) (logcount (player-palette player)))
          (let ((draw (undo-draw (game-deck game))))
            ;; (format t "  return ~a to deck~%" (card-label draw))
            (setf (player-hand player)
                  (remove-card draw (player-hand player)))))))))

(defun play (player-count)
  (let* ((game (make-game))
         (deck (game-deck game)))
    (dotimes (i player-count)
      (let ((player (make-player :id i
                                 :palette (make-card-set (list
                                                          (draw-from-deck deck)))
                                 :hand (make-card-set (loop repeat 7
                                                            collect (draw-from-deck deck))))))
        (push player (game-players game))))
    (mapcar (lambda (player next)
              (setf (player-next-player player) next))
            (game-players game)
            (cdr (append (game-players game) (game-players game))))
    (let ((outcomes (make-array (* 50 player-count) :initial-element 0))
          (depth (make-array 50
                             :element-type '(unsigned-byte 32)
                             :initial-element 0))
          (actions 0)
          (*leader* (who-is-winning game))
          (*players-left* player-count)
          (*turns* 0))
      (declare (special *leader* *players-left* *turns*)
               (fixnum actions))
      (labels ((advance-to-next-player ()
                 (declare (optimize (speed 1)))
                 (when (= *players-left* 1)
                   (let ((winner
                          (player-id (find-if-not #'player-eliminated
                                                  (game-players game)))))
                     (incf (aref outcomes (+ winner (* *turns* player-count))))
                     (when (zerop (mod actions 100000))
                       (format t "winners: ~a~%actions: ~a~%turns: ~a~%"
                               outcomes actions depth)))
                   (return-from advance-to-next-player)
                   #+nil
                   (return-from play (list :gameover :turns turns)))
                 (let ((*leader* *leader*))
                   (declare (special *leader*))
                   (dotimes (p (1- player-count))
                     (unless (player-eliminated *leader*)
                       (setf *leader* (player-next-player *leader*))
                       (return)))
                   (select-move)))
               (eliminate-leader ()
                 ;; (format t "player ~a eliminated (canvas ~a)~%~a~%" *leader*
                 ;;         (card-label (first (game-canvas game)))
                 ;;         game)
                 (let ((*players-left* (1- *players-left*)))
                   (declare (special *players-left*))
                   (setf (player-eliminated *leader*) t)
                   (advance-to-next-player)
                   (setf (player-eliminated *leader*) nil)))
               (select-move ()
                 (let* ((moves (valid-moves game *leader*))
                        (move-count (length moves)))
                   ;; (format t "player ~a has ~d moves~%"
                   ;;         *leader* move-count)
                   (if (not moves)
                       (eliminate-leader)
                       (dolist (move moves)
                        ;; let ((move (nth (random move-count) moves)))
                         (execute-selected-move move)))))
               (execute-selected-move (move)
                 (incf actions)
                 (let ((*turns* (1+ *turns*)))
                   (declare (special *turns*))
                   (incf (aref depth *turns*))
                   (execute-move game *leader* move)
                   (advance-to-next-player)
                   (undo-move game *leader* move))))
        (advance-to-next-player))
      outcomes)))
