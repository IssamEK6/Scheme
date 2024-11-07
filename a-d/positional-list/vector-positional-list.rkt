#lang r7rs

;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*                                                                 *-*-
;-*-*                   Vectorial Positional Lists                    *-*-
;-*-*                                                                 *-*-
;-*-*                       Wolfgang De Meuter                        *-*-
;-*-*                   2018  Software Languages Lab                  *-*-
;-*-*                   Vrije Universiteit Brussel                    *-*-
;-*-*                                                                 *-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-

(define-library (vector-positional-list)
  (export new from-scheme-list positional-list?
          length full? empty?
          map for-each
          first last has-next? has-previous? next previous
          find update! delete! peek
          add-before! add-after!)
  (import (except (scheme base) length))
  (begin
    (define positional-list-size 10)

    (define-record-type positional-list
      (make v s e)
      positional-list?
      (v storage storage!)
      (s size size!)
      (e equality))

    (define (new ==?)
      (make (make-vector positional-list-size) 0 ==?))

    (define (storage-move-right vector i j)
      (do ((idx j (- idx 1)))
        ((< idx i))
        (vector-set! vector (+ idx 1) (vector-ref vector idx))))

    (define (storage-move-left vector i j)
      (do ((idx i (+ idx 1)))
        ((> idx j))
        (vector-set! vector (- idx 1) (vector-ref vector idx))))
 
    (define (attach-first! plst val)
      (attach-middle! plst val -1))

    (define (attach-middle! plst val pos)
      (define vect (storage plst))
      (define free (size plst))
      (storage-move-right vect (+ pos 1) (- free 1))
      (vector-set! vect (+ pos 1) val)
      (size! plst (+ free 1)))

    (define (attach-last! plst val)
      (define vect (storage plst))
      (define free (size plst))
      (vector-set! vect free val)
      (size! plst (+ free 1)))
 
    (define (detach-first! plst)
      (detach-middle! plst 0))
 
    (define (detach-last! plst pos)
      (define free (size plst))
      (size! plst (- free 1)))
 
    (define (detach-middle! plst pos)
      (define vect (storage plst))
      (define free (size plst))
      (storage-move-left vect (+ pos 1) (- free 1))
      (size! plst (- free 1)))
 
    (define (length plst)
      (size plst))
 
    (define (empty? plst)
      (= 0 (size plst)))
 
    (define (full? plst)
      (= (size plst)
         (vector-length (storage plst))))
 
    (define (first plst)
      (if (= 0 (size plst))
          (error "empty list (first)" plst)
          0))
 
    (define (last plst)
      (if (= 0 (size plst))
          (error "empty list (last)" plst)
          (- (size plst) 1)))
 
    (define (has-next? plst pos)
      (< (+ pos 1) (size plst)))
 
    (define (has-previous? plst pos)
      (< 0 pos))
 
    (define (next plst pos)
      (if (not (has-next? plst pos))
          (error "list has no next (next)" plst)
          (+ pos 1)))
 
    (define (previous plst pos)
      (if (not (has-previous? plst pos))
          (error "list has no previous (previous)" plst)
          (- pos 1)))
 
    (define (peek plst pos)
      (if (> pos (size plst))
          (error "illegal position (peek)" plst)
          (vector-ref (storage plst) pos)))
 
    (define (update! plst pos val)
      (if (> pos (size plst))
          (error "illegal position (update!)" plst)
          (vector-set! (storage plst) pos val)))
          
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