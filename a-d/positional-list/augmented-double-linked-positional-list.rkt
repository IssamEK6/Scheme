#lang r7rs

;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*                                                                 *-*-
;-*-*           Double Linked Positional Lists (Augmented)            *-*-
;-*-*                                                                 *-*-
;-*-*                       Wolfgang De Meuter                        *-*-
;-*-*                   2018  Software Languages Lab                  *-*-
;-*-*                   Vrije Universiteit Brussel                    *-*-
;-*-*                                                                 *-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-

(define-library (augmented-double-linked-positional-list)
  (export new from-scheme-list positional-list?
          length full? empty?
          map for-each
          first last has-next? has-previous? next previous
          find update! delete! peek
          add-before! add-after!)
  (import (except (scheme base) length))
  
  (begin
 
    (define-record-type list-node
      (make-list-node v n p)
      list-node?
      (v list-node-val  list-node-val!)
      (n list-node-next list-node-next!)
      (p list-node-prev list-node-prev!))
 
    (define-record-type positional-list
      (make h t s e)
      positional-list?
      (h head head!)
      (t tail tail!)
      (s size size!)
      (e equality))
 
    (define (new ==?)
      (make '() '() 0 ==?))
 
    (define (attach-first! plst val)
      (define frst (head plst))
      (define node (make-list-node val frst '()))
      (head! plst node)
      (if (not (null? frst))
          (list-node-prev! frst node)
          (tail! plst node)) ; first null => last null
      (size! plst (+ 1 (size plst))))
 
    (define (attach-middle! plst val pos)
      (define next (list-node-next pos))
      (define node (make-list-node val next pos))
      (list-node-next! pos node)
      (if (not (null? next))
          (list-node-prev! next node)
          (tail! plst node)); next null => new last
      (size! plst (+ 1 (size plst))))
 
    (define (attach-last! plst val)
      (define last (tail plst))
      (define node (make-list-node val '() last))
      (define frst (head plst))
      (if (null? frst) ; first is last
          (head! plst node)
          (list-node-next! last node))
      (tail! plst node)
      (size! plst (+ 1 (size plst))))
 
    (define (detach-first! plst)
      (define frst (head plst))
      (define scnd (list-node-next frst))
      (head! plst scnd)
      (if (not (null? scnd))               ; first is the only one
          (list-node-prev! scnd '())
          (tail! plst '()))
      (size! plst (- (size plst) 1)))
 
    (define (detach-middle! plst pos)
      (define next (list-node-next pos))
      (define prev (list-node-prev pos))
      (list-node-next! prev next)
      (list-node-prev! next prev)
      (size! plst (- (size plst) 1)))
 
    (define (detach-last! plst pos)
      (define frst (head plst))
      (define scnd (list-node-next frst))
      (define last (tail plst))
      (define penu (list-node-prev last))
      (if (null? scnd) ; last is also first
          (head! plst '())
          (list-node-next! penu '()))
      (tail! plst penu)
      (size! plst (- (size plst) 1)))
 
    (define (length plst)
      (size plst))
 
    (define (full? plst)
      #f)
 
    (define (empty? plst)
      (null? (head plst)))
 
    (define (first plst)
      (if (null? (head plst))
          (error "list empty (first)" plst)
          (head plst)))
 
    (define (last plst)
      (if (null? (tail plst))
          (error "list empty (last)" plst)
          (tail plst)))
 
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
          (list-node-prev pos)))
 
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
      (if (empty? plst)
          #f
          (let
              ((==? (equality plst)))
            (attach-last! plst key)
            (let*
                ((pos (let search-sentinel
                        ((curr (first plst)))
                        (if (==? (peek plst curr) key)
                            curr
                            (search-sentinel (next plst curr)))))
                 (res (if (has-next? plst pos)
                          pos
                          #f)))
              (detach-last! plst (last plst))
              res))))))