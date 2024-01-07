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

(defmacro hippo--when-generators (then)
  "Evaluate THEN if `generator' library is available."
  (declare (debug t))
  (when (require 'generator nil 'noerror) then))


;;; ================================================================
;;;        Internal functions for use in the heap package

(cl-defstruct (hippo (:conc-name hippo--)
                     (:constructor nil)
                     (:copier nil)
                     (:constructor hippo--create
                                   (cmpfun &optional
                                           (initial-size 10)
                                           (resize-factor 2)))
                     :named)
  (vect (make-vector initial-size nil))
  (cmpfun nil)
  (count 0)
  (initial-size 10)
  (resize-factor 2))


(defsubst hippo--isort (v i j f)
  "Return first index from I or J in vector V.

Indexes I and J are ordered by calling sorting function F on
their respective elements in V."
  (if (funcall f (aref v i) (aref v j)) i j))


(defun hippo--child (heap i)
  "Return the index of the first of the 3 children of element I in HEAP, if any.

The children, should they exist, are ordered using the HEAP
comparison function."
  (let ((v (hippo--vect heap))
        (f (hippo--cmpfun heap))
        (c (hippo--count heap))
        (j (* 3 i)))
    (let ((first (1+ j)))
      (unless (>= first c)
        (let ((second (+ 2 j)))
          (if (>= second c)
              first
            (let ((best (hippo--isort v first second f))
                  (third (+ 3 j)))
              (if (>= third c)
                  best
                (hippo--isort v best third f)))))))))


(defsubst hippo--vswap (v i j)
  "Swap elements I and J in vector V."
  (cl-psetf (aref v i) (aref v j)
            (aref v j) (aref v i)))


(defun hippo--sift-up (heap n)
  "Sift instance with index N in HEAP upwards.

Proceed until it reaches its order in the HEAP as determined by
the HEAP comparison function, or its top."
  (let* ((v (hippo--vect heap))
         (f (hippo--cmpfun heap))
         (i n)
         (j)
         (e (aref v i)))
    (while (and (> i 0)
		(funcall f e (aref v (setq j (/ (1- i) 3)))))
      (hippo--vswap v i j)
      (setq i j))))


(defun hippo--sift-down (heap n)
  "Sift instance with index N in the HEAP downwards.

Proceed until it reaches its order in the HEAP as determined by
the HEAP comparison function, or its bottom."
  (let* ((v (hippo--vect heap))
	 (f (hippo--cmpfun heap))
	 (i n)
         (j (hippo--child heap i))
	 (e (aref v i)))
    (while (and j
                (funcall f (aref v j) e))
      (hippo--vswap v i j)
      (setq i j
            j (hippo--child heap i)))))


(defun hippo--heapify (heap)
  "Heapify heap HEAP."
  (let* ((c (hippo--count heap))
         (i (ceiling
             (1- (expt 3 (ceiling (1- (log (1+ (* 2 c)) 3))))) 2)))
    (cl-loop for i downfrom i to 0 do
             (hippo--sift-down heap i))
    heap))



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
    (hippo--create compare-function initial-size resize-factor)))


;;;###autoload
(defalias 'hippo-create #'make-heap)
(defalias 'hippo-pop #'hippo-delete-root)
(defalias 'hippo-push #'hippo-add)


(defun hippo-copy (heap)
  "Return a copy of heap HEAP."
  (let ((newheap (hippo--create (hippo--cmpfun heap)
                                (hippo--initial-size heap)
                                (hippo--resize-factor heap))))
    (setf (hippo--vect newheap) (vconcat (hippo--vect heap))
          (hippo--count newheap) (hippo--count heap))
    newheap))


(defun hippo-empty-p (heap)
  "Return t if heap HEAP is empty, nil otherwise."
  (zerop (hippo--count heap)))


(defun hippo-size (heap)
  "Return the number of entries in heap HEAP."
  (hippo--count heap))


(defun hippo-compare-function (heap)
  "Return the comparison function for the heap HEAP."
  (hippo--cmpfun heap))


(defun hippo-add (heap data)
  "Add DATA to heap HEAP, and return DATA."
  (let ((count (hippo--count heap))
	(size (hippo--initial-size heap))
	(vect (hippo--vect heap)))
    (if (< count size)
	(aset vect count data)
      (setf (hippo--vect heap)
            (vconcat (hippo--vect heap) (vector data)
                     (make-vector
                      (1- (* size (1- (hippo--resize-factor heap))))
                      nil))
            (hippo--initial-size heap) (* size (hippo--resize-factor heap))))
    (let ((count (setf (hippo--count heap) (1+ (hippo--count heap)))))
      (hippo--sift-up heap (1- count))))
  data)


(defun hippo-root (heap)
  "Return the root of heap HEAP, without removing it."
  (if (zerop (hippo--count heap)) nil (aref (hippo--vect heap) 0)))


(defun hippo-delete-root (heap)
  "Return the root of heap HEAP and remove it from HEAP."
  (let ((v (hippo--vect heap)))
    (unless (zerop (hippo--count heap))
      (let ((root (aref v 0))
            (count (cl-decf (hippo--count heap))))
        (if (zerop count)
	    (setf (hippo--vect heap) (make-vector (hippo--initial-size heap) nil))
	  (aset v 0 (aref v count))
	  (aset v count nil)
	  (hippo--sift-down heap 0))
        root))))


(defun hippo-modify (heap match-function data)
  "Replace the first element matched by MATCH-FUNCTION in heap HEAP with DATA.

The function MATCH-FUNCTION is a predicate called with an element
of HEAP as its single argument, and returns non-nil if that
element should be modified, nil otherwise.  Only the first
matched occurrence is modified.

Return t if there was a match, nil otherwise."
  (let* ((v (hippo--vect heap))
         (i (seq-position v (seq-find match-function v))))
    (unless (not i)
      (let ((olddata (aref v i)))
        (aset v i data)
        (if (funcall (hippo--cmpfun heap) data olddata)
            (hippo--sift-up heap i)
          (hippo--sift-down heap i)))
      t)))


(defun hippo-build (compare-function vec &optional resize-factor)
  "Create a heap from vector VEC with comparison function COMPARE-FUNCTION.

COMPARE-FUNCTION is called with two elements of the heap, and
should return non-nil if the first element should sort before the
second, nil otherwise.

Optional argument RESIZE-FACTOR sets the factor by which the
heap's size is increased if it runs out of space, defaulting to
2."
  (let ((heap (hippo--create
               compare-function
               (length vec)
               (or resize-factor 2))))
    (setf (hippo--vect heap) (copy-sequence vec)
          (hippo--count heap) (length vec))
    (hippo--heapify heap)
    heap))


(defun hippo-merge (heap &rest heaps)
  "Merge heap HEAP with remaining HEAPS.

The newly merged heap takes the comparison function and
resize-factor of heap HEAP.

Note that this operation requires O(n) time to merge n heaps."
  (let ((vv (mapcar #'hippo--vect heaps)))
    (hippo-build (hippo--cmpfun heap)
                (apply #'vconcat (hippo--vect heap) vv)
                (hippo--resize-factor heap))))


(defun hippo-clear (heap)
  "Remove all entries from heap HEAP.

Return number of entries removed."
  (prog1
      (hippo--count heap)
    (setf (hippo--vect heap) (make-vector (hippo--initial-size heap) nil)
          (hippo--count heap) 0)))


(hippo--when-generators
 (iter-defun hippo-iter (heap)
   "Return a heap iterator object.

Calling `iter-next' on this object will retrieve the next element
from the heap. The heap itself is not modified.

Note that constructing a heap iterator is an inefficient
operation that takes O(n) time for a heap of size n.  Calls to
`iter-next' are comparatively efficient, taking O(log n) time
each."
   (let ((heap (hippo-copy heap)))
     (while (not (hippo-empty-p heap))
       (iter-yield (hippo-delete-root heap))))))


(provide 'heap)

;;; heap.el ends here
