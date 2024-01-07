;;; heap.el --- Heap (a.k.a. priority queue) data structure  -*- lexical-binding: t; -*-

;; Copyright (C) 2004-2006, 2008, 2012-2013, 2017  Free Software Foundation, Inc

;; Author: Toby Cubitt <toby-predictive@dr-qubit.org>
;; Version: 0.5
;; Keywords: extensions, data structures, heap, priority queue
;; URL: http://www.dr-qubit.org/emacs.php
;; Repository: http://www.dr-qubit.org/git/predictive.git

;; This file is part of Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation, either version 3 of the License, or (at your option)
;; any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along
;; with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:
;;
;; A heap is a form of efficient self-sorting tree.  In particular, the root
;; node is guaranteed to be the highest-ranked entry in the tree.  (The
;; comparison function used for ranking the data can, of course, be freely
;; defined).  Therefore repeatedly removing the root node will return the data
;; in order of increasing rank.  They are often used as priority queues, for
;; scheduling tasks in order of importance.
;;
;; This package implements ternary heaps, since they are about 12% more
;; efficient than binary heaps for heaps containing more than about 10
;; elements, and for very small heaps the difference is negligible.  The
;; asymptotic complexity of ternary heap operations is the same as for a
;; binary heap: 'add', 'delete-root' and 'modify' operations are all O(log n)
;; on a heap containing n elements.
;;
;; Note that this package implements a heap as an implicit data structure on a
;; vector.  Therefore, the maximum size of the heap has to be specified in
;; advance.  Although the heap will grow dynamically if it becomes full, this
;; requires copying the entire heap, so insertion has worst-case complexity O(n)
;; instead of O(log n), though the amortized complexity is still O(log n).  (For
;; applications where the maximum size of the heap is not known in advance, an
;; implementation based on binary trees might be more suitable, but is not
;; currently implemented in this package.)
;;
;; You create a heap using `make-heap', add elements to it using `heap-add',
;; delete and return the root of the heap using `heap-delete-root', and modify
;; an element of the heap using `heap-modify'.  A number of other heap
;; convenience functions are also provided, all with the prefix `heap-'.
;; Functions with prefix `heap--' are for internal use only, and should never be
;; used outside this package.


;;; Code:

(eval-when-compile (require 'cl-lib))

(defmacro heap--when-generators (then)
  "Evaluate THEN if `generator' library is available."
  (declare (debug t))
  (when (require 'generator nil 'noerror) then))


;;; ================================================================
;;;        Internal functions for use in the heap package

(cl-defstruct (heap-
               :named
               (:constructor nil)
               (:constructor heap--create
                             (cmpfun &optional (size 10) (resize 2)
                                     &aux
                                     (vect (make-vector size nil))
                                     (count 0)))
               (:copier nil))
  vect cmpfun count size resize)


(defsubst heap--isort (v i j f)
  "Return first index from I or J in vector V.

Indexes I and J are ordered by calling sorting function F on
their respective elements in V."
  (if (funcall f (aref v i) (aref v j)) i j))


(defun heap--child (heap i)
  "Return the index of the first of the 3 children of element I in HEAP, if any.

The children, should they exist, are ordered using the HEAP
comparison function."
  (let ((v (heap--vect heap))
        (f (heap--cmpfun heap))
        (c (heap--count heap))
        (j (* 3 i)))
    (let ((first (1+ j)))
      (unless (>= first c)
        (let ((second (+ 2 j)))
          (if (>= second c)
              first
            (let ((best (heap--isort v first second f))
                  (third (+ 3 j)))
              (if (>= third c)
                  best
                (heap--isort v best third f)))))))))


(defsubst heap--vswap (v i j)
  "Swap elements I and J in vector V."
  (cl-psetf (aref v i) (aref v j)
            (aref v j) (aref v i)))


(defun heap--sift-up (heap n)
  "Sift instance with index N in HEAP upwards.

Proceed until it reaches its order in the HEAP as determined by
the HEAP comparison function, or its top."
  (let* ((v (heap--vect heap))
         (f (heap--cmpfun heap))
         (i n)
         (j)
         (e (aref v i)))
    (while (and (> i 0)
		(funcall f e (aref v (setq j (/ (1- i) 3)))))
      (heap--vswap v i j)
      (setq i j))))


(defun heap--sift-down (heap n)
  "Sift instance with index N in the HEAP downwards.

Proceed until it reaches its order in the HEAP as determined by
the HEAP comparison function, or its bottom."
  (let* ((v (heap--vect heap))
	 (f (heap--cmpfun heap))
	 (i n)
         (j (heap--child heap i))
	 (e (aref v i)))
    (while (and j
                (funcall f (aref v j) e))
      (heap--vswap v i j)
      (setq i j
            j (heap--child heap i)))))



;;; ================================================================
;;;          The public functions which operate on heaps.

;;;###autoload
(defun make-heap (compare-function &optional initial-size resize-factor)
  "Create an empty heap with comparison function COMPARE-FUNCTION.

COMPARE-FUNCTION is called with two elements of the heap, and
should return non-nil if the first element should sort before the
second, nil otherwise.

Optional argument INITIAL-SIZE sets the initial size of the heap,
defaulting to 10.  Optional argument RESIZE-FACTOR sets the factor
by which the heap's size is increased if it runs out of space,
defaulting to 2."
  (let ((initial-size (or initial-size 10))
        (resize-factor (or resize-factor 2)))
    (heap--create compare-function initial-size resize-factor)))


;;;###autoload
(defalias 'heap-create #'make-heap)
(defalias 'heap-pop #'heap-delete-root)
(defalias 'heap-push #'heap-add)


(defun heap-copy (heap)
  "Return a copy of heap HEAP."
  (let ((newheap (heap--create (heap--cmpfun heap)
                               (heap--size heap)
                               (heap--resize heap))))
    (setf (heap--vect newheap) (vconcat (heap--vect heap))
          (heap--count newheap) (heap--count heap))
    newheap))


(defun heap-empty-p (heap)
  "Return t if heap HEAP is empty, nil otherwise."
  (zerop (heap--count heap)))


(defun heap-size (heap)
  "Return the number of entries in heap HEAP."
  (heap--count heap))


(defun heap-compare-function (heap)
  "Return the comparison function for the heap HEAP."
  (heap--cmpfun heap))


(defun heap-add (heap data)
  "Add DATA to heap HEAP, and return DATA."
  (let ((count (heap--count heap))
	(size (heap--size heap))
	(vect (heap--vect heap)))
    (if (< count size)
	(aset vect count data)
      (setf (heap--vect heap)
            (vconcat (heap--vect heap) (vector data)
                     (make-vector
                      (1- (* size (1- (heap--resize heap))))
                      nil))
            (heap--size heap) (* size (heap--resize heap))))
    (let ((count (setf (heap--count heap) (1+ (heap--count heap)))))
      (heap--sift-up heap (1- count))))
  data)


(defun heap-root (heap)
  "Return the root of heap HEAP, without removing it."
  (if (zerop (heap--count heap)) nil (aref (heap--vect heap) 0)))


(defun heap-delete-root (heap)
  "Return the root of heap HEAP and remove it from HEAP."
  (let ((v (heap--vect heap)))
    (unless (zerop (heap--count heap))
      (let ((root (aref v 0))
            (count (cl-decf (heap--count heap))))
        (if (zerop count)
	    (setf (heap--vect heap) (make-vector (heap--size heap) nil))
	  (aset v 0 (aref v count))
	  (aset v count nil)
	  (heap--sift-down heap 0))
        root))))


(defun heap-modify (heap match-function data)
  "Replace the first heap entry identified by MATCH-FUNCTION
with DATA, if a match exists. Return t if there was a match, nil
otherwise.

The function MATCH-FUNCTION should take one argument of the type
stored in the heap, and return non-nil if it should be modified,
nil otherwise.

Note that only the match highest up the heap is modified."
  (let ((vect (heap--vect heap))
	(count (heap--count heap))
	(i 0))
    ;; search vector for the first match
    (while (and (< i count)
		(not (funcall match-function (aref vect i))))
      (setq i (1+ i)))
    ;; if a match was found, modify it
    (if (< i count)
	(let ((olddata (aref vect i)))
	  (aset vect i data)
	  ;; if the new data is greater than old data, sift-up,
	  ;; otherwise sift-down
	  (if (funcall (heap--cmpfun heap) data olddata)
	      (heap--sift-up heap i)
	    (heap--sift-down heap i))
	  t)  ; return t if the match was successfully modified
      nil)))  ; return nil if no match was found


(defun heap-build (compare-function vec &optional resize-factor)
  "Build a heap from vector VEC with COMPARE-FUNCTION
as the comparison function.

Note that VEC is modified, and becomes part of the heap data
structure. If you don't want this, copy the vector first and pass
the copy in VEC.

COMPARE-FUNCTION takes two arguments, A and B, and returns
non-nil or nil. To implement a max-heap, it should return non-nil
if A is greater than B. To implemenet a min-heap, it should
return non-nil if A is less than B.

RESIZE-FACTOR sets the factor by which the heap's size is
increased if it runs out of space, defaulting to 2."
  (or resize-factor (setq resize-factor 2))
  (let ((heap (heap--create compare-function (length vec) resize-factor))
	(i (ceiling
	    (1- (expt 3 (ceiling (1- (log (1+ (* 2 (length vec))) 3))))) 2)))
    (setf (heap--vect heap) vec
	  (heap--count heap) (length vec))
    (while (>= (decf i) 0) (heap--sift-down heap i))
    heap))


(defun heap-merge (heap &rest heaps)
  "Merge HEAP with remaining HEAPS.

The merged heap takes the comparison function and resize-fector
of the first HEAP argument.

\(Note that in this heap implementation, the merge operation is
not very efficient, taking O(n) time for combined heap size n\)."
  (setq heaps (mapcar #'heap--vect heaps))
  (heap-build (heap--cmpfun heap)
	      (apply #'vconcat (heap--vect heap) heaps)
	      (heap--resize heap)))


(defun heap-clear (heap)
  "Remove all entries from HEAP.

Return number of entries removed."
  (prog1
      (heap--count heap)
    (setf (heap--vect heap) (make-vector (length (heap--vect heap)) nil)
          (heap--count heap) 0)))


(heap--when-generators
 (iter-defun heap-iter (heap)
   "Return a heap iterator object.

Calling `iter-next' on this object will retrieve the next element
from the heap. The heap itself is not modified.

\(Note that in this heap implementation, constructing a heap
iterator is not very efficient, taking O(n) time for a heap of
size n. Each call to `iter-next' on the other hand *is*
efficient, taking O(log n) time.\)"
   (let ((heap (heap-copy heap)))
     (while (not (heap-empty-p heap))
       (iter-yield (heap-delete-root heap))))))


(provide 'heap)

;;; heap.el ends here
