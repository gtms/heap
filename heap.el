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
;; node is guaranteed to be the highest-ranked entry in the tree.  (The sorting
;; function used for ranking the data can, of course, be freely defined).
;; Therefore repeatedly removing the root node will return the data in order of
;; increasing rank.  They are often used as priority queues, for scheduling
;; tasks in order of importance.
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
;; You create an empty heap using `heap-new', add elements to it using
;; `heap-push', extract the root of the heap using `heap-pop', and update an
;; element of the heap using `heap-modify'.  `heap-from' lets you turn a
;; sortable vector into a heap.  A number of other heap convenience functions
;; are also provided, all with the prefix `heap-'.  Functions with prefix
;; `heap--' are for internal use only.


;;; Code:

(eval-when-compile (require 'cl-lib))

(defmacro heap--when-generators (then)
  "Evaluate THEN if `generator' library is available."
  (declare (debug t))
  (when (require 'generator nil 'noerror) then))


;;; ================================================================
;;;        Internal functions for use in the heap package

(cl-defstruct (heap (:conc-name heap--)
                    (:constructor nil)
                    (:copier nil)
                    (:constructor heap--new
                                  (sorting-function
                                   &optional
                                   (allocated-size 10)
                                   (resize-factor 2)))
                    :named)
  (vector (make-vector allocated-size nil))
  sorting-function
  (count 0)
  (allocated-size 10)
  (resize-factor 2))


(defsubst heap--isort (v i j f)
  "Return the first from index I or J in vector V.

Indexes I and J are ordered by calling sorting function F on
their respective elements in V."
  (if (funcall f (aref v i) (aref v j)) i j))


(defun heap--first-child (heap i)
  "Return the index of the first child of element I in heap HEAP, if any.

Comparisons between each of the three children, should they
exist, are made using the heap sorting function."
  (let ((v (heap--vector heap))
        (f (heap--sorting-function heap))
        (c (heap--count heap))
        (left (1+ (* 3 i))))
    (unless (>= left c)
      (let ((center (1+ left)))
        (if (>= center c)
            left
          (let ((best (heap--isort v left center f))
                (right (1+ center)))
            (if (>= right c)
                best
              (heap--isort v best right f))))))))


(defsubst heap--vswap (v i j)
  "Swap elements I and J in vector V."
  (cl-psetf (aref v i) (aref v j)
            (aref v j) (aref v i)))


(defun heap--sift-up (heap i)
  "Sift instance with index I in heap HEAP upwards.

Proceed until it reaches its order in the heap as determined by
the heap's sorting function, or its top."
  (let* ((v (heap--vector heap))
         (f (heap--sorting-function heap))
         (i i)
         (j)
         (e (aref v i)))
    (while (and (> i 0)
                (funcall f e (aref v (setq j (/ (1- i) 3)))))
      (heap--vswap v i j)
      (setq i j))))


(defun heap--sift-down (heap i)
  "Sift instance with index I in heap HEAP downwards.

Proceed until it reaches its order in the heap as determined by
the heap's sorting function, or its bottom."
  (let* ((v (heap--vector heap))
         (f (heap--sorting-function heap))
         (i i)
         (j (heap--first-child heap i))
         (e (aref v i)))
    (while (and j (funcall f (aref v j) e))
      (heap--vswap v i j)
      (setq i j
            j (heap--first-child heap i)))))


(defun heap--heapify (heap)
  "Heapify heap HEAP."
  (let* ((c (heap--count heap))
         (i (ceiling
             (1- (expt 3 (ceiling (1- (log (1+ (* 2 c)) 3))))) 2)))
    (cl-loop for i downfrom i to 0 do
             (heap--sift-down heap i))
    heap))



;;; ================================================================
;;;          The public functions which operate on heaps.

;;;###autoload
(defalias 'heap-new #'heap--new
  "Create an empty heap with sorting function SORTING-FUNCTION.

SORTING-FUNCTION is called with two elements of the heap, and
should return non-nil if the first element should sort before the
second, nil otherwise.

Optional argument ALLOCATED-SIZE sets the initial size of the
heap, defaulting to 10.  Optional argument RESIZE-FACTOR sets the
factor by which the heap's size is increased if it runs out of
space, defaulting to 2.")


(defun heap-copy (heap)
  "Return a copy of heap HEAP."
  (let ((newheap (heap--new (heap--sorting-function heap)
                            (heap--allocated-size heap)
                            (heap--resize-factor heap))))
    (setf (heap--vector newheap) (vconcat (heap--vector heap))
          (heap--count newheap) (heap--count heap))
    newheap))


(defun heap-empty-p (heap)
  "Return t if heap HEAP is empty, nil otherwise."
  (zerop (heap--count heap)))


(defun heap-count (heap)
  "Return the number of entries in heap HEAP."
  (heap--count heap))


(defun heap-sorting-function (heap)
  "Return the sorting function of heap HEAP."
  (heap--sorting-function heap))


(defun heap-push (heap data)
  "Add DATA to heap HEAP, and return DATA."
  (let ((count (heap--count heap))
        (size (heap--allocated-size heap))
        (v (heap--vector heap)))
    (if (< count size)
        (aset v count data)
      (setf (heap--vector heap)
            (vconcat (heap--vector heap) (vector data)
                     (make-vector
                      (1- (* size (1- (heap--resize-factor heap))))
                      nil))
            (heap--allocated-size heap)
            (* size (heap--resize-factor heap))))
    (let ((count (setf (heap--count heap) (1+ (heap--count heap)))))
      (heap--sift-up heap (1- count))))
  data)


(defun heap-root (heap)
  "Return the root of heap HEAP, without removing it."
  (if (zerop (heap--count heap)) nil (aref (heap--vector heap) 0)))


(defun heap-pop (heap)
  "Return the root of heap HEAP and remove it from the heap."
  (unless (zerop (heap--count heap))
    (let* ((v (heap--vector heap))
           (root (aref v 0))
           (count (cl-decf (heap--count heap))))
      (if (zerop count)
          (setf (heap--vector heap)
                (make-vector (heap--allocated-size heap) nil))
        (aset v 0 (aref v count))
        (aset v count nil)
        (heap--sift-down heap 0))
      root)))


(defun heap-modify (heap match-function data)
  "Replace the first element matched by MATCH-FUNCTION in heap HEAP with DATA.

The function MATCH-FUNCTION is a predicate called with an element
of HEAP as its single argument, and returns non-nil if that
element should be modified, nil otherwise.  Only the first
matched occurrence is modified.

Return t if a match is found, nil otherwise."
  (let* ((v (heap--vector heap))
         (i (seq-position v (seq-find match-function v))))
    (unless (not i)
      (let ((olddata (aref v i)))
        (aset v i data)
        (if (funcall (heap--sorting-function heap) data olddata)
            (heap--sift-up heap i)
          (heap--sift-down heap i)))
      t)))


;;;###autoload
(defun heap-from (vector sorting-function &optional resize-factor)
  "Create a heap from vector VECTOR with sorting function SORTING-FUNCTION.

SORTING-FUNCTION is called with two elements of the heap, and
should return non-nil if the first element should sort before the
second, nil otherwise.

Optional argument RESIZE-FACTOR sets the factor by which the
heap's size is increased if it runs out of space, defaulting to
2."
  (let ((heap (heap--new
               sorting-function
               (length vector)
               (or resize-factor 2))))
    (setf (heap--vector heap) (copy-sequence vector)
          (heap--count heap) (length vector))
    (heap--heapify heap)
    heap))


(defun heap-merge (heap &rest heaps)
  "Merge heap HEAP with remaining HEAPS.

The newly merged heap takes the sorting function and
resize-factor of heap HEAP.

Note that this operation requires O(n) time to merge n heaps."
  (let ((vv (mapcar #'heap--vector heaps)))
    (heap-from (heap--sorting-function heap)
                 (apply #'vconcat (heap--vector heap) vv)
                 (heap--resize-factor heap))))


(defun heap-clear (heap)
  "Remove all entries from heap HEAP.

Return the number of entries removed."
  (prog1
      (heap--count heap)
    (setf (heap--vector heap)
          (make-vector (heap--allocated-size heap) nil)
          (heap--count heap) 0)))


(heap--when-generators
 (iter-defun heap-iter (heap)
   "Return a heap iterator object.

Calling `iter-next' on this object will retrieve the next element
from the heap. The heap itself is not modified.

Note that constructing a heap iterator is an inefficient
operation that takes O(n) time for a heap of size n.  Calls to
`iter-next' are comparatively efficient, taking O(log n) time
each."
   (let ((heap (heap-copy heap)))
     (while (not (heap-empty-p heap))
       (iter-yield (heap-pop heap))))))


(provide 'heap)

;;; heap.el ends here
