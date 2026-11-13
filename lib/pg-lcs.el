;;; pg-lcs.el --- Longest common subsequence of two vectors  -*- lexical-binding: t; -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Author:    Pierre Courtieu

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; The longest common subsequence of two vectors, as pairs of indices,
;; and the gaps between the pairs.  Independent of any prover.

;;; Code:

(require 'seq)

(defun pg-lcs-common-subsequence (a b &optional max-differences)
  "Pairs (I . J) of a longest common subsequence of vectors A and B.
In increasing order: A[I] and B[J] are `equal'.  The common beginning
and end are paired first, the middle part with the algorithm of Myers.
If the middle parts differ by more than MAX-DIFFERENCES elements, they
are not paired; nil means no limit."
  (let* ((n (length a)) (m (length b))
         (prefix 0) (suffix 0) (pairs nil))
    (while (and (< prefix n) (< prefix m)
                (equal (aref a prefix) (aref b prefix)))
      (push (cons prefix prefix) pairs)
      (setq prefix (1+ prefix)))
    (while (and (< (+ prefix suffix) n) (< (+ prefix suffix) m)
                (equal (aref a (- n suffix 1)) (aref b (- m suffix 1))))
      (setq suffix (1+ suffix)))
    (let ((middle (pg-lcs--myers
                   (substring a prefix (- n suffix))
                   (substring b prefix (- m suffix))
                   max-differences)))
      (dolist (pair middle)
        (push (cons (+ prefix (car pair)) (+ prefix (cdr pair))) pairs)))
    (dotimes (i suffix)
      (push (cons (- n suffix (- i)) (- m suffix (- i))) pairs))
    (nreverse pairs)))

(defun pg-lcs--myers (a b max-differences)
  "Pairs (I . J) of a longest common subsequence of vectors A and B.
In increasing order.  The algorithm of Myers, in O((N+M)D) for D
differences.  Nil if D exceeds MAX-DIFFERENCES, if non-nil."
  (let* ((n (length a)) (m (length b))
         (max-d (if max-differences (min (+ n m) max-differences) (+ n m)))
         (offset (1+ max-d))
         (v (make-vector (+ 3 (* 2 max-d)) 0))
         ;; the part -D-1..D+1 of V before each step D, for the way back
         (trace nil)
         (found nil))
    (catch 'found
      (dotimes (d (1+ max-d))
        (push (substring v (- offset d 1) (+ offset d 2)) trace)
        (let ((k (- d)))
          (while (<= k d)
            (let* ((x (if (or (= k (- d))
                              (and (/= k d)
                                   (< (aref v (+ offset k -1))
                                      (aref v (+ offset k 1)))))
                          (aref v (+ offset k 1))
                        (1+ (aref v (+ offset k -1)))))
                   (y (- x k)))
              (while (and (< x n) (< y m) (equal (aref a x) (aref b y)))
                (setq x (1+ x) y (1+ y)))
              (aset v (+ offset k) x)
              (when (and (>= x n) (>= y m))
                (setq found d)
                (throw 'found nil)))
            (setq k (+ k 2))))))
    (when found
      (let ((x n) (y m) (pairs nil) (d found))
        (dolist (before trace)
          ;; BEFORE is V before step D, indexed from -D-1
          (let* ((k (- x y))
                 (get (lambda (k) (aref before (+ k d 1))))
                 (prev-k (if (or (= k (- d))
                                 (and (/= k d)
                                      (< (funcall get (1- k))
                                         (funcall get (1+ k)))))
                             (1+ k)
                           (1- k)))
                 (prev-x (funcall get prev-k))
                 (prev-y (- prev-x prev-k)))
            (while (and (> x prev-x) (> y prev-y))
              (setq x (1- x) y (1- y))
              (push (cons x y) pairs))
            (when (> d 0)
              (setq x prev-x y prev-y))
            (setq d (1- d))))
        pairs))))

(defun pg-lcs-gaps (pairs n m)
  "The runs of two sequences of lengths N and M between their PAIRS.
PAIRS, a list or a vector, are the pairs (I . J) of the indices of
their paired elements, in increasing order.  A list of (RUN-A . RUN-B),
the indices of the elements of the run in each sequence, each (FIRST
. END), END excluded, or nil if the run is empty on this side."
  (let ((runs nil) (i 0) (j 0))
    (seq-doseq (pair (vconcat pairs (vector (cons n m))))
      (when (or (< i (car pair)) (< j (cdr pair)))
        (push (cons (and (< i (car pair)) (cons i (car pair)))
                    (and (< j (cdr pair)) (cons j (cdr pair))))
              runs))
      (setq i (1+ (car pair)) j (1+ (cdr pair))))
    (nreverse runs)))

(provide 'pg-lcs)
;;; pg-lcs.el ends here
