#lang r7rs

;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*                                                                 *-*-
;-*-*                    Linked Positional Lists                      *-*-
;-*-*                                                                 *-*-
;-*-*                       Wolfgang De Meuter                        *-*-
;-*-*                   2011  Software Languages Lab                  *-*-
;-*-*                   Vrije Universiteit Brussel                    *-*-
;-*-*                                                                 *-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-

(define-library (single-linked-positional-list)
  (export new from-scheme-list positional-list?
          length full? empty?
          map for-each
          first last has-next? has-previous? next previous
          find update! delete! peek
          add-before! add-after!)
  (import (except (scheme base) length))
  (begin
    (define make-list-node (lambda (x y) (vector x y)))
    (define list-node-val (lambda (v) (vector-ref v 0)))
    (define list-node-val! (lambda (v e) (vector-set! v 0 e)))
    (define list-node-next (lambda (v) (vector-ref v 1)))
    (define list-node-next! (lambda (v e) (vector-set! v 1 e)))
 
    (define-record-type positional-list 
      (make h e)
      positional-list?
      (h head head!)
      (e equality))
 
    (define (new ==?)
      (make '() ==?))
 
    (define (iter-from-head-until plst stop?)
      (define frst (head plst))
      (let chasing-pointers 
        ((prev '())
         (next frst))
        (if (stop? next)
            prev
            (chasing-pointers 
             next 
             (list-node-next next)))))
 
    (define (attach-first! plst val)
      (define frst (head plst))
      (define node (make-list-node val frst))
      (head! plst node))
 
    (define (attach-middle! plst val pos)
      (define next (list-node-next pos))
      (define node (make-list-node val next))
      (list-node-next! pos node))
 
    (define (attach-last! plst val)
      (define last (iter-from-head-until plst null?))
      (define node (make-list-node val '()))
      (define frst (head plst))
      (if (null? frst)
          (head! plst node) ; last is also first
          (list-node-next! last node)))
 
    (define (detach-first! plst)
      (define frst (head plst))
      (define scnd (list-node-next frst))
      (head! plst scnd))
 
    (define (detach-middle! plst pos)
      (define next (list-node-next pos))
      (define prev (iter-from-head-until 
                    plst 
                    (lambda (node) (eq? pos node))))
      (list-node-next! prev next))
 
    (define (detach-last! plst pos)
      (define frst (head plst))
      (define scnd (list-node-next frst))
      (if (null? scnd) ; last is also first
          (head! plst '())
          (list-node-next! (iter-from-head-until 
                            plst 
                            (lambda (last) (not (has-next? plst last)))) 
                           '())))
 
    (define (length plst)
      (let length-iter
        ((curr (head plst))
         (size 0))
        (if (null? curr)
            size
            (length-iter (list-node-next curr) (+ size 1)))))
 
    (define (full? plst)
      #f)
 
    (define (empty? plst)
      (null? (head plst)))
 
    (define (first plst)
      (if (null? (head plst))
          (error "list empty (first)" plst)
          (head plst)))
 
    (define (last plst)
      (if (null? (head plst))
          (error "list empty (last)" plst)
          (iter-from-head-until plst null?)))
 
    (define (has-next? plst pos)
      (not (null? (list-node-next pos))))
 
    (define (has-previous? plst pos)
      (not (eq? pos (head plst))))
 
    (define (next plst pos)
      (if (not (has-next? plst pos))
          (error "list has no next (next)" plst)
          (list-node-next pos)))
 
    (define (previous plst pos)
      (if (not (has-previous? plst pos))
          (error "list has no previous (previous)" plst)
          (iter-from-head-until plst (lambda (node) (eq? pos node)))))
 
    (define (update! plst pos val)
      (list-node-val! pos val)
      plst)
 
    (define (peek plst pos)
      (list-node-val pos))

;;
    (define (from-scheme-list slst ==?)
      (define result (new ==?))
      (if (null? slst)
          result
          (let for-all
            ((orig (cdr slst))
             (curr (first (add-after! result (car slst)))))
            (cond
              ((not (null? orig))
               (add-after! result (car orig) curr)
               (for-all (cdr orig) (next result curr)))
              (else
               result)))))
 
    (define (map plst f ==?)
      (define result (new ==?))
      (if (empty? plst)
          result
          (let for-all
            ((orig (first plst))
             (curr (first 
                    (add-after! result (f (peek plst (first plst)))))))
            (if (has-next? plst orig)
                (for-all (next plst orig) 
                  (next (add-after! result
                                    (f (peek plst (next plst orig))) 
                                    curr)
                        curr))
                result))))
 
    (define (for-each plst f)
      (if (not (empty? plst))
          (let for-all
            ((curr (first plst)))
            (f (peek plst curr))
            (if (has-next? plst curr)
                (for-all (next plst curr)))))
      plst)
 
    (define (add-before! plst val . pos)
      (define optional? (not (null? pos)))
      (cond 
        ((and (empty? plst) optional?)
         (error "illegal position (add-before!)" plst))
        ((or (not optional?) (eq? (car pos) (first plst)))
         (attach-first! plst val))
        (else
         (attach-middle! plst val (previous plst (car pos)))))
      plst)
 
    (define (add-after! plst val . pos)
      (define optional? (not (null? pos)))
      (cond
        ((and (empty? plst) optional?)
         (error "illegal position (add-after!)" plst))
        ((not optional?)
         (attach-last! plst val))
        (else
         (attach-middle! plst val (car pos))))
      plst)
 
    (define (delete! plst pos)
      (cond 
        ((eq? pos (first plst))
         (detach-first! plst))
        ((not (has-next? plst pos))
         (detach-last! plst pos))
        (else
         (detach-middle! plst pos)))
      plst)


;;      
    (define (find plst key)
      (define ==? (equality plst))
      (if (empty? plst)
          #f
          (let sequential-search
            ((curr (first plst)))
            (cond
              ((==? key (peek plst curr)) 
               curr)
              ((not (has-next? plst curr))
               #f)
              (else 
               (sequential-search (next plst curr)))))))))