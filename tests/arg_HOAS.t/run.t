  $ . ../setup-project.sh
  $ dune build test.vo
  ----<<---- enter:  
  coq.say raw: 
   (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
         parameter B2 explicit (sort (typ «test.test.4»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  raw: 
  parameter A1 maximal (sort (typ «test.test.2»)) c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
       parameter B2 explicit (sort (typ «test.test.4»)) c3 \
        arity
         (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
     c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
         parameter B2 explicit (sort (typ «test.test.4»)) c4 \
          arity
           (prod `x` (global (indt «nat»)) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
         parameter B2 explicit (sort (typ «test.test.4»)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
  ---->>---- exit:  
  coq.say raw: 
   (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
         parameter B2 explicit (sort (typ «test.test.4»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
       parameter A2 explicit c0 c1 \
        inductive foo1 tt 
         (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
           parameter B2 explicit (sort (typ «test.test.4»)) c3 \
            arity
             (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
         c2 \
         [constructor a_k1 
           (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
             parameter B2 explicit (sort (typ «test.test.4»)) c4 \
              arity
               (prod `x` (global (indt «nat»)) c5 \
                 prod `_` 
                  (app
                    [c2, app [global (indt «prod»), c3, c3], c4, 
                     app
                      [global (indc «S»), 
                       app
                        [global (indc «S»), 
                         app [global (indc «S»), global (indc «O»)]]]]) 
                  c6 \ app [c2, c3, c4, c5])), 
          constructor a_k2 
           (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
             parameter B2 explicit (sort (typ «test.test.4»)) c4 \
              arity
               (prod `_` c0 c5 \
                 app
                  [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
       parameter A2 explicit c0 c1 \
        inductive foo1 tt 
         (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
           parameter B2 explicit (sort (typ «test.test.4»)) c3 \
            arity
             (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
         c2 \
         [constructor a_k1 
           (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
             parameter B2 explicit (sort (typ «test.test.4»)) c4 \
              arity
               (prod `x` (global (indt «nat»)) c5 \
                 prod `_` 
                  (app
                    [c2, app [global (indt «prod»), c3, c3], c4, 
                     app
                      [global (indc «S»), 
                       app
                        [global (indc «S»), 
                         app [global (indc «S»), global (indc «O»)]]]]) 
                  c6 \ app [c2, c3, c4, c5])), 
          constructor a_k2 
           (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
             parameter B2 explicit (sort (typ «test.test.4»)) c4 \
              arity
               (prod `_` c0 c5 \
                 app
                  [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
         parameter B2 explicit (sort (typ «test.test.4»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  typed: 
  parameter A1 maximal (sort (typ «test.test.2»)) c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
       parameter B2 explicit (sort (typ «test.test.4»)) c3 \
        arity
         (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
     c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
         parameter B2 explicit (sort (typ «test.test.4»)) c4 \
          arity
           (prod `x` (global (indt «nat»)) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
         parameter B2 explicit (sort (typ «test.test.4»)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
  ---->>---- exit:  
  coq.say typed: 
   (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
         parameter B2 explicit (sort (typ «test.test.4»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  ----<<---- enter:  
  coq.env.add-indt
   (parameter A1 maximal (sort (typ «test.test.2»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.3»)) c2 \
         parameter B2 explicit (sort (typ «test.test.4»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.7»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.3»)) c3 \
           parameter B2 explicit (sort (typ «test.test.4»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
   X0
  ---->>---- exit:  
  coq.env.add-indt
   (parameter A1 maximal (sort (typ «foo1.u0»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c2 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c3 \
          arity (prod `_` (global (indt «nat»)) c4 \ sort (typ «foo1.u3»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
           parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
           parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
   «foo1»
  foo1 ?A2 ?B1 ?B2 ?n : Type
       : Type
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?n : [ |- nat]
  a_k1 ?A2 ?B1 ?B2 3 ?f : foo1 ?A2 ?B1 ?B2 3
       : foo1 ?A2 ?B1 ?B2 3
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?f : [ |- foo1 ?A2 (?B1 * ?B1) ?B2 3]
  ----<<---- enter:  
  coq.say raw: 
   (parameter A1 maximal X0 c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ X1)) c2 \
         parameter B2 explicit (sort (typ X2)) c3 \
          arity (prod `_` (global (indt «nat»)) c4 \ sort (typ X3))) c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ X4)) c3 \
           parameter B2 explicit (sort (typ X5)) c4 \
            arity
             (prod `x` (X6 c0 c1 c2 c3 c4) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ X7)) c3 \
           parameter B2 explicit (sort (typ X8)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  raw: 
  parameter A1 maximal X0 c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ X1)) c2 \
       parameter B2 explicit (sort (typ X2)) c3 \
        arity (prod `_` (global (indt «nat»)) c4 \ sort (typ X3))) c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ X4)) c3 \
         parameter B2 explicit (sort (typ X5)) c4 \
          arity
           (prod `x` (X6 c0 c1 c2 c3 c4) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ X7)) c3 \
         parameter B2 explicit (sort (typ X8)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
  ---->>---- exit:  
  coq.say raw: 
   (parameter A1 maximal X0 c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ X1)) c2 \
         parameter B2 explicit (sort (typ X2)) c3 \
          arity (prod `_` (global (indt «nat»)) c4 \ sort (typ X3))) c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ X4)) c3 \
           parameter B2 explicit (sort (typ X5)) c4 \
            arity
             (prod `x` (X6 c0 c1 c2 c3 c4) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ X7)) c3 \
           parameter B2 explicit (sort (typ X8)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (parameter A1 maximal X0 c0 \
       parameter A2 explicit c0 c1 \
        inductive foo1 tt 
         (parameter B1 explicit (sort (typ X1)) c2 \
           parameter B2 explicit (sort (typ X2)) c3 \
            arity (prod `_` (global (indt «nat»)) c4 \ sort (typ X3))) c2 \
         [constructor a_k1 
           (parameter B1 explicit (sort (typ X4)) c3 \
             parameter B2 explicit (sort (typ X5)) c4 \
              arity
               (prod `x` (X6 c0 c1 c2 c3 c4) c5 \
                 prod `_` 
                  (app
                    [c2, app [global (indt «prod»), c3, c3], c4, 
                     app
                      [global (indc «S»), 
                       app
                        [global (indc «S»), 
                         app [global (indc «S»), global (indc «O»)]]]]) 
                  c6 \ app [c2, c3, c4, c5])), 
          constructor a_k2 
           (parameter B1 explicit (sort (typ X7)) c3 \
             parameter B2 explicit (sort (typ X8)) c4 \
              arity
               (prod `_` c0 c5 \
                 app
                  [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
     X9) Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (parameter A1 maximal X0 c0 \
       parameter A2 explicit c0 c1 \
        inductive foo1 tt 
         (parameter B1 explicit (sort (typ «test.test.41»)) c2 \
           parameter B2 explicit (sort (typ «test.test.44»)) c3 \
            arity
             (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.47»))) 
         c2 \
         [constructor a_k1 
           (parameter B1 explicit (sort (typ «test.test.52»)) c3 \
             parameter B2 explicit (sort (typ «test.test.54»)) c4 \
              arity
               (prod `x` (X6 c0 c1 c2 c3 c4) c5 \
                 prod `_` 
                  (app
                    [c2, app [global (indt «prod»), c3, c3], c4, 
                     app
                      [global (indc «S»), 
                       app
                        [global (indc «S»), 
                         app [global (indc «S»), global (indc «O»)]]]]) 
                  c6 \ app [c2, c3, c4, c5])), 
          constructor a_k2 
           (parameter B1 explicit (sort (typ «test.test.61»)) c3 \
             parameter B2 explicit (sort (typ «test.test.63»)) c4 \
              arity
               (prod `_` c0 c5 \
                 app
                  [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
     (parameter A1 maximal (sort (typ «test.test.40»)) c0 \
       parameter A2 explicit c0 c1 \
        inductive foo1 tt 
         (parameter B1 explicit (sort (typ «test.test.42»)) c2 \
           parameter B2 explicit (sort (typ «test.test.45»)) c3 \
            arity
             (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.48»))) 
         c2 \
         [constructor a_k1 
           (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
             parameter B2 explicit (sort (typ «test.test.55»)) c4 \
              arity
               (prod `x` (global (indt «nat»)) c5 \
                 prod `_` 
                  (app
                    [c2, app [global (indt «prod»), c3, c3], c4, 
                     app
                      [global (indc «S»), 
                       app
                        [global (indc «S»), 
                         app [global (indc «S»), global (indc «O»)]]]]) 
                  c6 \ app [c2, c3, c4, c5])), 
          constructor a_k2 
           (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
             parameter B2 explicit (sort (typ «test.test.64»)) c4 \
              arity
               (prod `_` c0 c5 \
                 app
                  [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (parameter A1 maximal (sort (typ «test.test.40»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.42»)) c2 \
         parameter B2 explicit (sort (typ «test.test.45»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.48»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
           parameter B2 explicit (sort (typ «test.test.55»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
           parameter B2 explicit (sort (typ «test.test.64»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  typed: 
  parameter A1 maximal (sort (typ «test.test.40»)) c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ «test.test.42»)) c2 \
       parameter B2 explicit (sort (typ «test.test.45»)) c3 \
        arity
         (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.48»))) 
     c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
         parameter B2 explicit (sort (typ «test.test.55»)) c4 \
          arity
           (prod `x` (global (indt «nat»)) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
         parameter B2 explicit (sort (typ «test.test.64»)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
  ---->>---- exit:  
  coq.say typed: 
   (parameter A1 maximal (sort (typ «test.test.40»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.42»)) c2 \
         parameter B2 explicit (sort (typ «test.test.45»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.48»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
           parameter B2 explicit (sort (typ «test.test.55»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
           parameter B2 explicit (sort (typ «test.test.64»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))])
  ----<<---- enter:  
  coq.env.add-indt
   (parameter A1 maximal (sort (typ «test.test.40»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «test.test.42»)) c2 \
         parameter B2 explicit (sort (typ «test.test.45»)) c3 \
          arity
           (prod `_` (global (indt «nat»)) c4 \ sort (typ «test.test.48»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
           parameter B2 explicit (sort (typ «test.test.55»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
           parameter B2 explicit (sort (typ «test.test.64»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
   X10
  ---->>---- exit:  
  coq.env.add-indt
   (parameter A1 maximal (sort (typ «foo1.u0»)) c0 \
     parameter A2 explicit c0 c1 \
      inductive foo1 tt 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c2 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c3 \
          arity (prod `_` (global (indt «nat»)) c4 \ sort (typ «foo1.u3»))) 
       c2 \
       [constructor a_k1 
         (parameter B1 explicit (sort (typ «test.test.53»)) c3 \
           parameter B2 explicit (sort (typ «test.test.55»)) c4 \
            arity
             (prod `x` (global (indt «nat»)) c5 \
               prod `_` 
                (app
                  [c2, app [global (indt «prod»), c3, c3], c4, 
                   app
                    [global (indc «S»), 
                     app
                      [global (indc «S»), 
                       app [global (indc «S»), global (indc «O»)]]]]) c6 \
                app [c2, c3, c4, c5])), 
        constructor a_k2 
         (parameter B1 explicit (sort (typ «test.test.62»)) c3 \
           parameter B2 explicit (sort (typ «test.test.64»)) c4 \
            arity
             (prod `_` c0 c5 \
               app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]) 
   «foo1»
  foo1 ?A2 ?B1 ?B2 ?n : Type
       : Type
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?n : [ |- nat]
  a_k1 ?A2 ?B1 ?B2 3 ?f : foo1 ?A2 ?B1 ?B2 3
       : foo1 ?A2 ?B1 ?B2 3
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?f : [ |- foo1 ?A2 (?B1 * ?B1) ?B2 3]
  Query assignments:
    D = parameter A explicit (sort (typ «t.u0»)) c0 \
   inductive t tt 
    (parameter y explicit (global (indt «nat»)) c1 \
      arity (sort (typ «test.test.82»))) c1 \
    [constructor K 
      (parameter y explicit (global (indt «nat»)) c2 \
        parameter x explicit c0 c3 \
         parameter n maximal (global (indt «nat»)) c4 \
          arity (prod `_` (app [c1, c4]) c5 \ app [c1, c2]))]
    I = «t»
  Universe constraints:
  UNIVERSES:
   {test.test.82} |= Set <= test.test.82
                     t.u0 <= test.test.82
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  ----<<---- enter:  
  coq.say raw: 
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  raw: 
  record foo (sort (typ «Set»)) Build_foo 
   (field [coercion off, canonical tt] f 
     (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
     field [coercion off, canonical tt] _ 
      (app
        [global (indt «eq»), global (indt «nat»), 
         app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)
  ---->>---- exit:  
  coq.say raw: 
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (record foo (sort (typ «Set»)) Build_foo 
       (field [coercion off, canonical tt] f 
         (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
         field [coercion off, canonical tt] _ 
          (app
            [global (indt «eq»), global (indt «nat»), 
             app [c0, global (indc «O»)], global (indc «O»)]) c1 \
          end-record))) Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (record foo (sort (typ «Set»)) Build_foo 
       (field [coercion off, canonical tt] f 
         (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
         field [coercion off, canonical tt] _ 
          (app
            [global (indt «eq»), global (indt «nat»), 
             app [c0, global (indc «O»)], global (indc «O»)]) c1 \
          end-record))) Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  typed: 
  record foo (sort (typ «Set»)) Build_foo 
   (field [coercion off, canonical tt] f 
     (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
     field [coercion off, canonical tt] _ 
      (app
        [global (indt «eq»), global (indt «nat»), 
         app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)
  ---->>---- exit:  
  coq.say typed: 
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  ----<<---- enter:  
  coq.env.add-indt
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)) 
   X0
  ---->>---- exit:  
  coq.env.add-indt
   (record foo (sort (typ «Set»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)) 
   «foo»
  ----<<---- enter:  
  coq.say raw: 
   (record foo (sort (typ X0)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), X1 c0, app [c0, global (indc «O»)], 
           global (indc «O»)]) c1 \ end-record))
  raw: 
  record foo (sort (typ X0)) Build_foo 
   (field [coercion off, canonical tt] f 
     (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
     field [coercion off, canonical tt] _ 
      (app
        [global (indt «eq»), X1 c0, app [c0, global (indc «O»)], 
         global (indc «O»)]) c1 \ end-record)
  ---->>---- exit:  
  coq.say raw: 
   (record foo (sort (typ X0)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), X1 c0, app [c0, global (indc «O»)], 
           global (indc «O»)]) c1 \ end-record))
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (record foo (sort (typ X0)) Build_foo 
       (field [coercion off, canonical tt] f 
         (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
         field [coercion off, canonical tt] _ 
          (app
            [global (indt «eq»), X1 c0, app [c0, global (indc «O»)], 
             global (indc «O»)]) c1 \ end-record)) X2) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (record foo (sort (typ «test.test.85»)) Build_foo 
       (field [coercion off, canonical tt] f 
         (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
         field [coercion off, canonical tt] _ 
          (app
            [global (indt «eq»), X1 c0, app [c0, global (indc «O»)], 
             global (indc «O»)]) c1 \ end-record)) 
     (record foo (sort (typ «test.test.86»)) Build_foo 
       (field [coercion off, canonical tt] f 
         (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
         field [coercion off, canonical tt] _ 
          (app
            [global (indt «eq»), global (indt «nat»), 
             app [c0, global (indc «O»)], global (indc «O»)]) c1 \
          end-record))) Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (record foo (sort (typ «test.test.86»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  typed: 
  record foo (sort (typ «test.test.86»)) Build_foo 
   (field [coercion off, canonical tt] f 
     (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
     field [coercion off, canonical tt] _ 
      (app
        [global (indt «eq»), global (indt «nat»), 
         app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)
  ---->>---- exit:  
  coq.say typed: 
   (record foo (sort (typ «test.test.86»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record))
  ----<<---- enter:  
  coq.env.add-indt
   (record foo (sort (typ «test.test.86»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)) 
   X3
  ---->>---- exit:  
  coq.env.add-indt
   (record foo (sort (typ «foo.u0»)) Build_foo 
     (field [coercion off, canonical tt] f 
       (prod `_` (global (indt «nat»)) c0 \ global (indt «nat»)) c0 \
       field [coercion off, canonical tt] _ 
        (app
          [global (indt «eq»), global (indt «nat»), 
           app [c0, global (indc «O»)], global (indc «O»)]) c1 \ end-record)) 
   «foo»
  ----<<---- enter:  
  coq.say raw: 
   (parameter A explicit (sort (typ «test.test.88»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.88»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record))
  raw: 
  parameter A explicit (sort (typ «test.test.88»)) c0 \
   parameter B explicit c0 c1 \
    record foo (sort (typ «test.test.88»)) Build_foo 
     (field [coercion off, canonical tt] a 
       (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
       field [coercion reversible, canonical tt] z 
        (prod `a` c0 c3 \
          prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
        field [coercion off, canonical ff] x 
         (let `w` (global (indt «nat»)) 
           (app
             [global (indc «S»), 
              app
               [global (indc «S»), 
                app [global (indc «S»), global (indc «O»)]]]) c4 \
           prod `x` c0 c5 \
            app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
         end-record)
  ---->>---- exit:  
  coq.say raw: 
   (parameter A explicit (sort (typ «test.test.88»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.88»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (parameter A explicit (sort (typ «test.test.88»)) c0 \
       parameter B explicit c0 c1 \
        record foo (sort (typ «test.test.88»)) Build_foo 
         (field [coercion off, canonical tt] a 
           (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
           field [coercion reversible, canonical tt] z 
            (prod `a` c0 c3 \
              prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
            field [coercion off, canonical ff] x 
             (let `w` (global (indt «nat»)) 
               (app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]) c4 \
               prod `x` c0 c5 \
                app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
             end-record))) Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (parameter A explicit (sort (typ «test.test.88»)) c0 \
       parameter B explicit c0 c1 \
        record foo (sort (typ «test.test.88»)) Build_foo 
         (field [coercion off, canonical tt] a 
           (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
           field [coercion reversible, canonical tt] z 
            (prod `a` c0 c3 \
              prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
            field [coercion off, canonical ff] x 
             (let `w` (global (indt «nat»)) 
               (app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]) c4 \
               prod `x` c0 c5 \
                app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
             end-record))) Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (parameter A explicit (sort (typ «test.test.88»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.88»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record))
  typed: 
  parameter A explicit (sort (typ «test.test.88»)) c0 \
   parameter B explicit c0 c1 \
    record foo (sort (typ «test.test.88»)) Build_foo 
     (field [coercion off, canonical tt] a 
       (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
       field [coercion reversible, canonical tt] z 
        (prod `a` c0 c3 \
          prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
        field [coercion off, canonical ff] x 
         (let `w` (global (indt «nat»)) 
           (app
             [global (indc «S»), 
              app
               [global (indc «S»), 
                app [global (indc «S»), global (indc «O»)]]]) c4 \
           prod `x` c0 c5 \
            app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
         end-record)
  ---->>---- exit:  
  coq.say typed: 
   (parameter A explicit (sort (typ «test.test.88»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.88»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record))
  ----<<---- enter:  
  coq.env.add-indt
   (parameter A explicit (sort (typ «test.test.88»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.88»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record)) X0
  ---->>---- exit:  
  coq.env.add-indt
   (parameter A explicit (sort (typ «foo.u0»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «foo.u0»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record)) «foo»
  Query assignments:
    I = «foo»
  ----<<---- enter:  
  coq.say raw: 
   (parameter A explicit X0 c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ X1)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), X2 c0 c1 c3, c1, c1]) c4 \ c0) 
          c3 \
          field [coercion off, canonical ff] x 
           (let `w` (X3 c0 c1 c2 c3) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` (X4 c0 c1 c2 c3 c4) c5 \
              app
               [global (indt «eq»), X5 c0 c1 c2 c3 c4 c5, app [c2, c5, c5], 
                c5]) c4 \ end-record))
  raw: 
  parameter A explicit X0 c0 \
   parameter B explicit c0 c1 \
    record foo (sort (typ X1)) Build_foo 
     (field [coercion off, canonical tt] a 
       (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
       field [coercion reversible, canonical tt] z 
        (prod `a` c0 c3 \
          prod `_` (app [global (indt «eq»), X2 c0 c1 c3, c1, c1]) c4 \ c0) 
        c3 \
        field [coercion off, canonical ff] x 
         (let `w` (X3 c0 c1 c2 c3) 
           (app
             [global (indc «S»), 
              app
               [global (indc «S»), 
                app [global (indc «S»), global (indc «O»)]]]) c4 \
           prod `x` (X4 c0 c1 c2 c3 c4) c5 \
            app
             [global (indt «eq»), X5 c0 c1 c2 c3 c4 c5, app [c2, c5, c5], c5]) 
         c4 \ end-record)
  ---->>---- exit:  
  coq.say raw: 
   (parameter A explicit X0 c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ X1)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `a` c0 c3 \
            prod `_` (app [global (indt «eq»), X2 c0 c1 c3, c1, c1]) c4 \ c0) 
          c3 \
          field [coercion off, canonical ff] x 
           (let `w` (X3 c0 c1 c2 c3) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` (X4 c0 c1 c2 c3 c4) c5 \
              app
               [global (indt «eq»), X5 c0 c1 c2 c3 c4 c5, app [c2, c5, c5], 
                c5]) c4 \ end-record))
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (parameter A explicit X0 c0 \
       parameter B explicit c0 c1 \
        record foo (sort (typ X1)) Build_foo 
         (field [coercion off, canonical tt] a 
           (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
           field [coercion reversible, canonical tt] z 
            (prod `a` c0 c3 \
              prod `_` (app [global (indt «eq»), X2 c0 c1 c3, c1, c1]) c4 \
               c0) c3 \
            field [coercion off, canonical ff] x 
             (let `w` (X3 c0 c1 c2 c3) 
               (app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]) c4 \
               prod `x` (X4 c0 c1 c2 c3 c4) c5 \
                app
                 [global (indt «eq»), X5 c0 c1 c2 c3 c4 c5, 
                  app [c2, c5, c5], c5]) c4 \ end-record)) X6) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-indt-decl-skeleton
     (parameter A explicit X0 c0 \
       parameter B explicit c0 c1 \
        record foo (sort (typ «test.test.95»)) Build_foo 
         (field [coercion off, canonical tt] a 
           (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
           field [coercion reversible, canonical tt] z 
            (prod `a` c0 c3 \
              prod `_` (app [global (indt «eq»), X2 c0 c1 c3, c1, c1]) c4 \
               c0) c3 \
            field [coercion off, canonical ff] x 
             (let `w` (X3 c0 c1 c2 c3) 
               (app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]) c4 \
               prod `x` (X4 c0 c1 c2 c3 c4) c5 \
                app
                 [global (indt «eq»), X5 c0 c1 c2 c3 c4 c5, 
                  app [c2, c5, c5], c5]) c4 \ end-record)) 
     (parameter A explicit (sort (typ «test.test.94»)) c0 \
       parameter B explicit c0 c1 \
        record foo (sort (typ «test.test.96»)) Build_foo 
         (field [coercion off, canonical tt] a 
           (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
           field [coercion reversible, canonical tt] z 
            (prod `elpi_ctx_entry_4_` c0 c3 \
              prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
            field [coercion off, canonical ff] x 
             (let `w` (global (indt «nat»)) 
               (app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]) c4 \
               prod `x` c0 c5 \
                app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
             end-record))) Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (parameter A explicit (sort (typ «test.test.94»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.96»)) Build_foo 
       (field [coercion off, canonical tt] a 
         (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
         field [coercion reversible, canonical tt] z 
          (prod `elpi_ctx_entry_4_` c0 c3 \
            prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
          field [coercion off, canonical ff] x 
           (let `w` (global (indt «nat»)) 
             (app
               [global (indc «S»), 
                app
                 [global (indc «S»), 
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record))
  typed: 
  parameter A explicit (sort (typ «test.test.94»)) c0 \
   parameter B explicit c0 c1 \
    record foo (sort (typ «test.test.96»)) Build_foo 
     (field [coercion off, canonical tt] a 
       (prod `_` c0 c2 \ prod `_` c0 c3 \ c0) c2 \
       field [coercion reversible, canonical tt] z 
        (prod `elpi_ctx_entry_4_` c0 c3 \
          prod `_` (app [global (indt «eq»), c0, c1, c1]) c4 \ c0) c3 \
        field [coercion off, canonical ff] x 
         (let `w` (global (indt «nat»)) 
           (app
             [global (indc «S»), 
              app
               [global (indc «S»), 
                app [global (indc «S»), global (indc «O»)]]]) c4 \
           prod `x` c0 c5 \
            app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
         end-record)
  ---->>---- exit:  
  coq.say typed: 
   (parameter A explicit (sort (typ «test.test.94»)) c0 \
     parameter B explicit c0 c1 \
      record foo (sort (typ «test.test.96»)) Build_foo 
  ...TRUNCATED BY DUNE...
                  app [global (indc «S»), global (indc «O»)]]]) c4 \
             prod `x` c0 c5 \
              app [global (indt «eq»), c0, app [c2, c5, c5], c5]) c4 \
           end-record)) «foo»
  Query assignments:
    I = «foo»
  ----<<---- enter:  
  coq.arity->term
   (parameter P explicit (sort (typ «test.test.99»)) c0 \
     parameter w explicit c0 c1 \
      parameter n explicit (global (indt «nat»)) c2 \
       arity (global (indt «nat»))) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter P explicit (sort (typ «test.test.99»)) c0 \
     parameter w explicit c0 c1 \
      parameter n explicit (global (indt «nat»)) c2 \
       arity (global (indt «nat»))) 
   (prod `P` (sort (typ «test.test.99»)) c0 \
     prod `w` c0 c1 \
      prod `n` (global (indt «nat»)) c2 \ global (indt «nat»))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck
     (fun `P` (sort (typ «test.test.99»)) c0 \
       fun `w` c0 c1 \
        fun `n` (global (indt «nat»)) c2 \
         app
          [global (const «Nat.add»), c2, 
           app [global (indc «S»), global (indc «O»)]]) 
     (prod `P` (sort (typ «test.test.99»)) c0 \
       prod `w` c0 c1 \
        prod `n` (global (indt «nat»)) c2 \ global (indt «nat»))) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck
     (fun `P` (sort (typ «test.test.99»)) c0 \
       fun `w` c0 c1 \
        fun `n` (global (indt «nat»)) c2 \
         app
          [global (const «Nat.add»), c2, 
           app [global (indc «S»), global (indc «O»)]]) 
     (prod `P` (sort (typ «test.test.99»)) c0 \
       prod `w` c0 c1 \
        prod `n` (global (indt «nat»)) c2 \ global (indt «nat»))) 
   illtyped definition
  ----<<---- enter:  
  coq.env.add-const x1 
   (fun `P` (sort (typ «test.test.99»)) c0 \
     fun `w` c0 c1 \
      fun `n` (global (indt «nat»)) c2 \
       app
        [global (const «Nat.add»), c2, 
         app [global (indc «S»), global (indc «O»)]]) 
   (prod `P` (sort (typ «test.test.99»)) c0 \
     prod `w` c0 c1 \
      prod `n` (global (indt «nat»)) c2 \ global (indt «nat»)) X1 X2
  ---->>---- exit:  
  coq.env.add-const x1 
   (fun `P` (sort (typ «x1.u0»)) c0 \
     fun `w` c0 c1 \
      fun `n` (global (indt «nat»)) c2 \
       app
        [global (const «Nat.add»), c2, 
         app [global (indc «S»), global (indc «O»)]]) 
   (prod `P` (sort (typ «x1.u0»)) c0 \
     prod `w` c0 c1 \
      prod `n` (global (indt «nat»)) c2 \ global (indt «nat»)) X1 «x1»
  x1 : forall P : Type, P -> nat -> nat
       : forall P : Type, P -> nat -> nat
  eq_refl : x1 = (fun (P : Type) (_ : P) (n : nat) => n + 1)
       : x1 = (fun (P : Type) (_ : P) (n : nat) => n + 1)
  ----<<---- enter:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (sort (typ «test.test.102»))) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (sort (typ «test.test.102»))) 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.102»))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-ty
     (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.102»)) X1) 
   illtyped axiom
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-ty
     (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.102»)) 
     (typ «test.test.103»)) illtyped axiom
  ----<<---- enter:  
  coq.env.add-axiom y 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.102»)) X2
  ---->>---- exit:  
  coq.env.add-axiom y 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «y.u0»)) «y»
  y : nat -> Type
       : nat -> Type
  ----<<---- enter:  
  coq.arity->term
   (parameter P explicit (sort (typ X0)) c0 \
     parameter w explicit c0 c1 \
      parameter n explicit (global (indt «nat»)) c2 \ arity (X1 c0 c1 c2)) X2
  ---->>---- exit:  
  coq.arity->term
   (parameter P explicit (sort (typ X0)) c0 \
     parameter w explicit c0 c1 \
      parameter n explicit (global (indt «nat»)) c2 \ arity (X3 c0 c1 c2)) 
   (prod `P` (sort (typ X0)) c0 \
     prod `w` c0 c1 \ prod `n` (global (indt «nat»)) (X3 c0 c1))
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-ty-skeleton
     (prod `P` (sort (typ X0)) c0 \
       prod `w` c0 c1 \ prod `n` (global (indt «nat»)) (X3 c0 c1)) X4 X5) 
   illtyped arity
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-ty-skeleton
     (prod `P` (sort (typ «test.test.105»)) c0 \
       prod `w` c0 c1 \ prod `n` (global (indt «nat»)) (X6 c0 c1)) 
     (typ «test.test.108») 
     (prod `P` (sort (typ «test.test.106»)) c0 \
       prod `w` c0 c1 \ prod `n` (global (indt «nat»)) c2 \ X7 c0 c1 c2)) 
   illtyped arity
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-skeleton
     (fun `P` (sort (typ X8)) c0 \
       fun `w` c0 c1 \
        fun `n` (global (indt «nat»)) c2 \
         app
          [global (const «Nat.add»), c2, 
           app [global (indc «S»), global (indc «O»)]]) 
     (prod `P` (sort (typ «test.test.106»)) c0 \
       prod `w` c0 c1 \ prod `n` (global (indt «nat»)) c2 \ X7 c0 c1 c2) X9) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-skeleton
     (fun `P` (sort (typ «test.test.109»)) c0 \
       fun `w` c0 c1 \
        fun `n` (global (indt «nat»)) c2 \
         app
          [global (const «Nat.add»), c2, 
           app [global (indc «S»), global (indc «O»)]]) 
     (prod `P` (sort (typ «test.test.106»)) c0 \
       prod `w` c0 c1 \
        prod `n` (global (indt «nat»)) c2 \ global (indt «nat»)) 
     (fun `P` (sort (typ «test.test.110»)) c0 \
       fun `w` c0 c1 \
        fun `n` (global (indt «nat»)) c2 \
         app
          [global (const «Nat.add»), c2, 
           app [global (indc «S»), global (indc «O»)]])) 
   illtyped definition
  ----<<---- enter:  
  coq.env.add-const x1 
   (fun `P` (sort (typ «test.test.110»)) c0 \
     fun `w` c0 c1 \
      fun `n` (global (indt «nat»)) c2 \
       app
        [global (const «Nat.add»), c2, 
         app [global (indc «S»), global (indc «O»)]]) 
   (prod `P` (sort (typ «test.test.106»)) c0 \
     prod `w` c0 c1 \
      prod `n` (global (indt «nat»)) c2 \ global (indt «nat»)) X10 X11
  ---->>---- exit:  
  coq.env.add-const x1 
   (fun `P` (sort (typ «x1.u1»)) c0 \
     fun `w` c0 c1 \
      fun `n` (global (indt «nat»)) c2 \
       app
        [global (const «Nat.add»), c2, 
         app [global (indc «S»), global (indc «O»)]]) 
   (prod `P` (sort (typ «x1.u0»)) c0 \
     prod `w` c0 c1 \
      prod `n` (global (indt «nat»)) c2 \ global (indt «nat»)) X10 «x1»
  x1 : forall P : Type, P -> nat -> nat
       : forall P : Type, P -> nat -> nat
  eq_refl : x1 = (fun (P : Type) (_ : P) (n : nat) => n + 1)
       : x1 = (fun (P : Type) (_ : P) (n : nat) => n + 1)
  ----<<---- enter:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (sort (typ «test.test.113»))) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (sort (typ «test.test.113»))) 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.113»))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-ty
     (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.113»)) X1) 
   illtyped axiom
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-ty
     (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.113»)) 
     (typ «test.test.114»)) illtyped axiom
  ----<<---- enter:  
  coq.env.add-axiom y 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «test.test.113»)) X2
  ---->>---- exit:  
  coq.env.add-axiom y 
   (prod `n` (global (indt «nat»)) c0 \ sort (typ «y.u0»)) «y»
  y : nat -> Type
       : nat -> Type
  ----<<---- enter:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (global (indt «nat»))) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter n explicit (global (indt «nat»)) c0 \
     arity (global (indt «nat»))) 
   (prod `n` (global (indt «nat»)) c0 \ global (indt «nat»))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck
     (fun `n` (global (indt «nat»)) c0 \ app [global (indc «S»), c0]) 
     (prod `n` (global (indt «nat»)) c0 \ global (indt «nat»))) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck
     (fun `n` (global (indt «nat»)) c0 \ app [global (indc «S»), c0]) 
     (prod `n` (global (indt «nat»)) c0 \ global (indt «nat»))) 
   illtyped definition
  ----<<---- enter:  
  coq.env.add-const x 
   (fun `n` (global (indt «nat»)) c0 \ app [global (indc «S»), c0]) 
   (prod `n` (global (indt «nat»)) c0 \ global (indt «nat»)) X1 X2
  ---->>---- exit:  
  coq.env.add-const x 
   (fun `n` (global (indt «nat»)) c0 \ app [global (indc «S»), c0]) 
   (prod `n` (global (indt «nat»)) c0 \ global (indt «nat»)) X1 «x»
  ----<<---- enter:  
  coq.say raw: 
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record))
  raw: 
  record foo (sort prop) Build_foo 
   (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
     end-record)
  ---->>---- exit:  
  coq.say raw: 
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record))
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (record foo (sort prop) Build_foo 
       (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
         end-record))) Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (record foo (sort prop) Build_foo 
       (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
         end-record))) Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record))
  typed: 
  record foo (sort prop) Build_foo 
   (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
     end-record)
  ---->>---- exit:  
  coq.say typed: 
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record))
  ----<<---- enter:  
  coq.env.add-indt
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record)) X0
  ---->>---- exit:  
  coq.env.add-indt
   (record foo (sort prop) Build_foo 
     (field [coercion off, canonical tt] bar (global (indt «True»)) c0 \
       end-record)) «foo»
  parameter A1 maximal (sort (typ «foo1.u0»)) c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ «foo1.u1»)) c2 \
       parameter B2 explicit (sort (typ «foo1.u2»)) c3 \
        arity (prod `_` (global (indt «nat»)) c4 \ sort (typ «foo1.u3»))) 
     c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
          arity
           (prod `x` (global (indt «nat»)) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
  Query assignments:
    D = parameter A1 maximal (sort (typ «foo1.u0»)) c0 \
   parameter A2 explicit c0 c1 \
    inductive foo1 tt 
     (parameter B1 explicit (sort (typ «foo1.u1»)) c2 \
       parameter B2 explicit (sort (typ «foo1.u2»)) c3 \
        arity (prod `_` (global (indt «nat»)) c4 \ sort (typ «foo1.u3»))) 
     c2 \
     [constructor a_k1 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
          arity
           (prod `x` (global (indt «nat»)) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c4, 
                 app
                  [global (indc «S»), 
                   app
                    [global (indc «S»), 
                     app [global (indc «S»), global (indc «O»)]]]]) c6 \
              app [c2, c3, c4, c5])), 
      constructor a_k2 
       (parameter B1 explicit (sort (typ «foo1.u1»)) c3 \
         parameter B2 explicit (sort (typ «foo1.u2»)) c4 \
          arity
           (prod `_` c0 c5 \
             app [c2, c3, c4, app [global (indc «S»), global (indc «O»)]]))]
    I = «inductive_nup.foo1»
  foo1 ?A2 ?B1 ?B2 ?n : Type
       : Type
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?n : [ |- nat]
  a_k1 ?A2 ?B1 ?B2 3 ?f : foo1 ?A2 ?B1 ?B2 3
       : foo1 ?A2 ?B1 ?B2 3
  where
  ?A1 : [ |- Type]
  ?A2 : [ |- ?A1]
  ?B1 : [ |- Type]
  ?B2 : [ |- Type]
  ?f : [ |- foo1 ?A2 (?B1 * ?B1) ?B2 3]
  Query assignments:
    I = «inductive_nup.r»
    R = parameter A explicit (sort (typ «r.u0»)) c0 \
   parameter a explicit c0 c1 \
    record r (sort (typ «r.u0»)) R 
     (field [coercion reversible, canonical tt] f (prod `_` c0 c2 \ c0) c2 \
       field [coercion off, canonical tt] g c0 c3 \
        field [coercion off, canonical tt] p 
         (app [global (indt «eq»), c0, c1, c3]) c4 \ end-record)
  Record r (A : Type) (a : A) : Type := R { f : A -> A;  g : A;  p : a = g }.
  
  Arguments r A%type_scope a
  Arguments R A%type_scope a f%function_scope g p
  ----<<---- enter:  coq.say raw: (inductive X1 tt (arity (sort prop)) c0 \ [])
  raw: inductive X1 tt (arity (sort prop)) c0 \ []
  ---->>---- exit:  coq.say raw: (inductive X1 tt (arity (sort prop)) c0 \ [])
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl (inductive X1 tt (arity (sort prop)) c0 \ [])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl (inductive X1 tt (arity (sort prop)) c0 \ [])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: (inductive X1 tt (arity (sort prop)) c0 \ [])
  typed: inductive X1 tt (arity (sort prop)) c0 \ []
  ---->>---- exit:  
  coq.say typed: (inductive X1 tt (arity (sort prop)) c0 \ [])
  ----<<---- enter:  
  coq.env.add-indt (inductive X1 tt (arity (sort prop)) c0 \ []) X0
  ---->>---- exit:  
  coq.env.add-indt (inductive X1 tt (arity (sort prop)) c0 \ []) «X1»
  X1 : Prop
  
  X1 is not universe polymorphic
  Expands to: Inductive test.test.X1
  ----<<---- enter:  
  coq.say raw: 
   (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ []) 
   (upoly-decl [«test.test.131»] tt [] tt)
  raw: inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ [] 
  upoly-decl [«test.test.131»] tt [] tt
  ---->>---- exit:  
  coq.say raw: 
   (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ []) 
   (upoly-decl [«test.test.131»] tt [] tt)
  ----<<---- enter:  coq.univ.print
  Universe constraints: UNIVERSES:
                         {eu1} |= 
                        ALGEBRAIC UNIVERSES:
                         {}
                        FLEXIBLE UNIVERSES:
                         eu1
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  ---->>---- exit:  coq.univ.print
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ [])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ [])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ [])
  typed: inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ []
  ---->>---- exit:  
  coq.say typed: 
   (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ [])
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.131»] tt [] tt) X0
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.131»] tt [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.131»] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.131»] tt [] tt) =>
   coq.env.add-indt
    (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ []) X1
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.131»] tt [] tt) =>
   coq.env.add-indt
    (inductive X3 tt (arity (sort (typ «test.test.131»))) c0 \ []) «X3»
  ----<<---- enter:  
  coq.say raw: 
   (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ []) 
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt)
  raw: inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ [] 
  upoly-decl-cumul [auto «test.test.139»] tt [] tt
  ---->>---- exit:  
  coq.say raw: 
   (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ []) 
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt)
  ----<<---- enter:  coq.univ.print
  Universe constraints: UNIVERSES:
                         {eu2} |= 
                        ALGEBRAIC UNIVERSES:
                         {}
                        FLEXIBLE UNIVERSES:
                         eu2
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  ---->>---- exit:  coq.univ.print
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ [])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ [])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ [])
  typed: inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ []
  ---->>---- exit:  
  coq.say typed: 
   (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ [])
  ----<<---- enter:  
  coq.upoly-decl->attribute
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt) X0
  ---->>---- exit:  
  coq.upoly-decl->attribute
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt) 
   (get-option coq:udecl-cumul 
     (upoly-decl-cumul [auto «test.test.139»] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl-cumul 
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt) =>
   coq.env.add-indt
    (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ []) X1
  ---->>---- exit:  
  get-option coq:udecl-cumul 
   (upoly-decl-cumul [auto «test.test.139»] tt [] tt) =>
   coq.env.add-indt
    (inductive X4 tt (arity (sort (typ «test.test.139»))) c0 \ []) «X4»
  X3@{eu1} : Type@{eu1}
  (* eu1 |=  *)
  
  X3 is universe polymorphic
  Expands to: Inductive test.test.X3
  X4@{eu2} : Type@{eu2}
  (* *eu2 |=  *)
  
  X4 is universe polymorphic
  Expands to: Inductive test.test.X4
  Query assignments:
    GR = indt «X3»
  Universe constraints:
  UNIVERSES:
   {test.test.147} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.147
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    GR = indt «X4»
  Universe constraints:
  UNIVERSES:
   {test.test.148} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.148
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  ----<<---- enter:  
  coq.say raw: 
   (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ []) 
   (upoly-decl [«test.test.149»] ff [] ff)
  raw: inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ [] 
  upoly-decl [«test.test.149»] ff [] ff
  ---->>---- exit:  
  coq.say raw: 
   (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ []) 
   (upoly-decl [«test.test.149»] ff [] ff)
  ----<<---- enter:  coq.univ.print
  Universe constraints: UNIVERSES:
                         {eu3} |= 
                        ALGEBRAIC UNIVERSES:
                         {}
                        FLEXIBLE UNIVERSES:
                         eu3
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  ---->>---- exit:  coq.univ.print
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ [])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ [])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ [])
  typed: inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ []
  ---->>---- exit:  
  coq.say typed: 
   (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ [])
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.149»] ff [] ff) X0
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.149»] ff [] ff) 
   (get-option coq:udecl (upoly-decl [«test.test.149»] ff [] ff))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.149»] ff [] ff) =>
   coq.env.add-indt
    (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ []) X1
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.149»] ff [] ff) =>
   coq.env.add-indt
    (inductive X5 tt (arity (sort (typ «test.test.149»))) c0 \ []) «X5»
  X5@{eu3} : Type@{eu3}
  (* eu3 |=  *)
  
  X5 is universe polymorphic
  Expands to: Inductive test.test.X5
  ----<<---- enter:  
  coq.say raw: 
   (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
     [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))]) 
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff)
  raw: 
  inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
   [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))] 
  upoly-decl [«test.test.157», «test.test.158»] ff 
   [lt «test.test.157» «test.test.158»] ff
  ---->>---- exit:  
  coq.say raw: 
   (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
     [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))]) 
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff)
  ----<<---- enter:  coq.univ.print
  Universe constraints: UNIVERSES:
                         {eu5 eu4} |= eu4 < eu5
                        ALGEBRAIC UNIVERSES:
                         {}
                        FLEXIBLE UNIVERSES:
                         eu5
                         eu4
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  ---->>---- exit:  coq.univ.print
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
       [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))])) 
   Illtyped inductive declaration
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck-indt-decl
     (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
       [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))])) 
   Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
     [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))])
  typed: 
  inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
   [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))]
  ---->>---- exit:  
  coq.say typed: 
   (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
     [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))])
  ----<<---- enter:  
  coq.upoly-decl->attribute
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff) X0
  ---->>---- exit:  
  coq.upoly-decl->attribute
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff) 
   (get-option coq:udecl 
     (upoly-decl [«test.test.157», «test.test.158»] ff 
       [lt «test.test.157» «test.test.158»] ff))
  ----<<---- enter:  
  get-option coq:udecl 
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff) =>
   coq.env.add-indt
    (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
      [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))]) 
    X1
  ---->>---- exit:  
  get-option coq:udecl 
   (upoly-decl [«test.test.157», «test.test.158»] ff 
     [lt «test.test.157» «test.test.158»] ff) =>
   coq.env.add-indt
    (inductive X6 tt (arity (sort (typ «test.test.158»))) c0 \
      [constructor K (arity (prod `u` (sort (typ «test.test.157»)) c1 \ c0))]) 
    «X6»
  X6@{eu4 eu5} : Type@{eu5}
  (* eu4 eu5 |= eu4 < eu5 *)
  
  X6 is universe polymorphic
  Expands to: Inductive test.test.X6
  ----<<---- enter:  
  coq.say raw: (inductive X8 tt (arity (sort (typ X0))) c0 \ []) 
   (upoly-decl [] tt [] tt)
  raw: inductive X8 tt (arity (sort (typ X0))) c0 \ [] upoly-decl [] tt [] tt
  ---->>---- exit:  
  coq.say raw: (inductive X8 tt (arity (sort (typ X0))) c0 \ []) 
   (upoly-decl [] tt [] tt)
  ----<<---- enter:  coq.univ.print
  Universe constraints: 
  ---->>---- exit:  coq.univ.print
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-indt-decl-skeleton
      (inductive X8 tt (arity (sort (typ X0))) c0 \ []) X1) 
    Illtyped inductive declaration
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-indt-decl-skeleton
      (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ []) 
      (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ [])) 
    Illtyped inductive declaration
  ----<<---- enter:  
  coq.say typed: 
   (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ [])
  typed: inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ []
  ---->>---- exit:  
  coq.say typed: 
   (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ [])
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X2
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-indt
    (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ []) X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-indt
    (inductive X8 tt (arity (sort (typ «test.test.173»))) c0 \ []) «X8»
  X8@{u} : Type@{u}
  (* u |=  *)
  
  X8 is universe polymorphic
  Expands to: Inductive test.test.X8
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.181»)) c0 \
     parameter x explicit c0 c1 \ arity c0) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.181»)) c0 \
     parameter x explicit c0 c1 \ arity c0) 
   (prod `T` (sort (typ «test.test.181»)) c0 \ prod `x` c0 c1 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «test.test.181»)) c0 \ fun `x` c0 c1 \ c1) 
     (prod `T` (sort (typ «test.test.181»)) c0 \ prod `x` c0 c1 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «test.test.181»)) c0 \ fun `x` c0 c1 \ c1) 
     (prod `T` (sort (typ «test.test.181»)) c0 \ prod `x` c0 c1 \ c0)) 
   illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f1 
    (fun `T` (sort (typ «test.test.181»)) c0 \ fun `x` c0 c1 \ c1) 
    (prod `T` (sort (typ «test.test.181»)) c0 \ prod `x` c0 c1 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f1 
    (fun `T` (sort (typ «test.test.181»)) c0 \ fun `x` c0 c1 \ c1) 
    (prod `T` (sort (typ «test.test.181»)) c0 \ prod `x` c0 c1 \ c0) X2 
    «f1»
  f1@{u} : forall T : Type@{u}, T -> T
  (* u |=  *)
  
  f1 is universe polymorphic
  Arguments f1 T%type_scope x
  f1 is transparent
  Expands to: Constant test.test.f1
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.182»)) c0 \
     parameter T1 explicit (sort (typ «test.test.182»)) c1 \
      parameter x explicit c0 c2 \ arity c0) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.182»)) c0 \
     parameter T1 explicit (sort (typ «test.test.182»)) c1 \
      parameter x explicit c0 c2 \ arity c0) 
   (prod `T` (sort (typ «test.test.182»)) c0 \
     prod `T1` (sort (typ «test.test.182»)) c1 \ prod `x` c0 c2 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «test.test.182»)) c0 \
       fun `T1` (sort (typ «test.test.182»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «test.test.182»)) c0 \
       prod `T1` (sort (typ «test.test.182»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «test.test.182»)) c0 \
       fun `T1` (sort (typ «test.test.182»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «test.test.182»)) c0 \
       prod `T1` (sort (typ «test.test.182»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.182»] ff [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.182»] ff [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.182»] ff [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.182»] ff [] tt) =>
   coq.env.add-const f2 
    (fun `T` (sort (typ «test.test.182»)) c0 \
      fun `T1` (sort (typ «test.test.182»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «test.test.182»)) c0 \
      prod `T1` (sort (typ «test.test.182»)) c1 \ prod `x` c0 c2 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.182»] ff [] tt) =>
   coq.env.add-const f2 
    (fun `T` (sort (typ «test.test.182»)) c0 \
      fun `T1` (sort (typ «test.test.182»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «test.test.182»)) c0 \
      prod `T1` (sort (typ «test.test.182»)) c1 \ prod `x` c0 c2 \ c0) X2 
    «f2»
  f2@{u} : forall T : Type@{u}, Type@{u} -> T -> T
  (* u |=  *)
  
  f2 is universe polymorphic
  Arguments f2 (T T1)%type_scope x
  f2 is transparent
  Expands to: Constant test.test.f2
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ X0)) c0 \
     parameter x explicit c0 c1 \ arity (X1 c0 c1)) X2
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ X0)) c0 \
     parameter x explicit c0 c1 \ arity (X3 c0 c1)) 
   (prod `T` (sort (typ X0)) c0 \ prod `x` c0 (X3 c0))
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-ty-skeleton
      (prod `T` (sort (typ X0)) c0 \ prod `x` c0 (X3 c0)) X4 X5) illtyped arity
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-ty-skeleton
      (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 (X6 c0)) 
      (typ «test.test.185») 
      (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 c1 \ X7 c0 c1)) 
    illtyped arity
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (fun `T` (sort (typ X8)) c0 \ fun `x` c0 c1 \ c1) 
      (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 c1 \ X7 c0 c1) 
      X9) illtyped definition
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton
      (fun `T` (sort (typ «test.test.186»)) c0 \ fun `x` c0 c1 \ c1) 
      (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 c1 \ c0) 
      (fun `T` (sort (typ «test.test.183»)) c0 \ fun `x` c0 c1 \ c1)) 
    illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X10
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f3 
    (fun `T` (sort (typ «test.test.183»)) c0 \ fun `x` c0 c1 \ c1) 
    (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 c1 \ c0) X11 X12
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f3 
    (fun `T` (sort (typ «test.test.183»)) c0 \ fun `x` c0 c1 \ c1) 
    (prod `T` (sort (typ «test.test.183»)) c0 \ prod `x` c0 c1 \ c0) X11 
    «f3»
  f3@{u} : forall T : Type@{u}, T -> T
  (* u |=  *)
  
  f3 is universe polymorphic
  Arguments f3 T%type_scope x
  f3 is transparent
  Expands to: Constant test.test.f3
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.187»)) c0 \
     parameter T1 explicit (sort (typ «test.test.187»)) c1 \
      parameter x explicit c0 c2 \ arity (X0 c0 c1 c2)) X1
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ «test.test.187»)) c0 \
     parameter T1 explicit (sort (typ «test.test.187»)) c1 \
      parameter x explicit c0 c2 \ arity (X2 c0 c1 c2)) 
   (prod `T` (sort (typ «test.test.187»)) c0 \
     prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 (X2 c0 c1))
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-ty-skeleton
      (prod `T` (sort (typ «test.test.187»)) c0 \
        prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 (X2 c0 c1)) 
      X3 X4) illtyped arity
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-ty-skeleton
      (prod `T` (sort (typ «test.test.187»)) c0 \
        prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 (X5 c0 c1)) 
      (typ «test.test.189») 
      (prod `T` (sort (typ «test.test.187»)) c0 \
        prod `T1` (sort (typ «test.test.187»)) c1 \
         prod `x` c0 c2 \ X6 c0 c1 c2)) illtyped arity
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton
      (fun `T` (sort (typ «test.test.187»)) c0 \
        fun `T1` (sort (typ «test.test.187»)) c1 \ fun `x` c0 c2 \ c2) 
      (prod `T` (sort (typ «test.test.187»)) c0 \
        prod `T1` (sort (typ «test.test.187»)) c1 \
         prod `x` c0 c2 \ X6 c0 c1 c2) X7) illtyped definition
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton
      (fun `T` (sort (typ «test.test.187»)) c0 \
        fun `T1` (sort (typ «test.test.187»)) c1 \ fun `x` c0 c2 \ c2) 
      (prod `T` (sort (typ «test.test.187»)) c0 \
        prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 c2 \ c0) 
      (fun `T` (sort (typ «test.test.187»)) c0 \
        fun `T1` (sort (typ «test.test.187»)) c1 \ fun `x` c0 c2 \ c2)) 
    illtyped definition
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.187»] ff [] tt) X8
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.187»] ff [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.187»] ff [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.187»] ff [] tt) =>
   coq.env.add-const f4 
    (fun `T` (sort (typ «test.test.187»)) c0 \
      fun `T1` (sort (typ «test.test.187»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «test.test.187»)) c0 \
      prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 c2 \ c0) X9 X10
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.187»] ff [] tt) =>
   coq.env.add-const f4 
    (fun `T` (sort (typ «test.test.187»)) c0 \
      fun `T1` (sort (typ «test.test.187»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «test.test.187»)) c0 \
      prod `T1` (sort (typ «test.test.187»)) c1 \ prod `x` c0 c2 \ c0) X9 
    «f4»
  f4@{u} : forall T : Type@{u}, Type@{u} -> T -> T
  (* u |=  *)
  
  f4 is universe polymorphic
  Arguments f4 (T T1)%type_scope x
  f4 is transparent
  Expands to: Constant test.test.f4
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ «uuu»)) c0 \
     parameter T1 explicit (sort (typ «uuu»)) c1 \
      parameter x explicit c0 c2 \ arity (X0 c0 c1 c2)) X1
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ «uuu»)) c0 \
     parameter T1 explicit (sort (typ «uuu»)) c1 \
      parameter x explicit c0 c2 \ arity (X2 c0 c1 c2)) 
   (prod `T` (sort (typ «uuu»)) c0 \
     prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 (X2 c0 c1))
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-ty-skeleton
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 (X2 c0 c1)) X3 X4) 
   illtyped arity
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-ty-skeleton
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 (X5 c0 c1)) 
     (typ «test.test.194») 
     (prod `T` (sort (typ «test.test.191»)) c0 \
       prod `T1` (sort (typ «test.test.192»)) c1 \
        prod `x` c0 c2 \ X6 c0 c1 c2)) illtyped arity
  ----<<---- enter:  
  std.assert-ok!
   (coq.elaborate-skeleton
     (fun `T` (sort (typ «uuu»)) c0 \
       fun `T1` (sort (typ «uuu»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «test.test.191»)) c0 \
       prod `T1` (sort (typ «test.test.192»)) c1 \
        prod `x` c0 c2 \ X6 c0 c1 c2) X7) illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.elaborate-skeleton
     (fun `T` (sort (typ «uuu»)) c0 \
       fun `T1` (sort (typ «uuu»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «test.test.191»)) c0 \
       prod `T1` (sort (typ «test.test.192»)) c1 \ prod `x` c0 c2 \ c0) 
     (fun `T` (sort (typ «test.test.195»)) c0 \
       fun `T1` (sort (typ «test.test.196»)) c1 \ fun `x` c0 c2 \ c2)) 
   illtyped definition
  ----<<---- enter:  
  coq.env.add-const f5 
   (fun `T` (sort (typ «test.test.195»)) c0 \
     fun `T1` (sort (typ «test.test.196»)) c1 \ fun `x` c0 c2 \ c2) 
   (prod `T` (sort (typ «test.test.191»)) c0 \
     prod `T1` (sort (typ «test.test.192»)) c1 \ prod `x` c0 c2 \ c0) X8 X9
  ---->>---- exit:  
  coq.env.add-const f5 
   (fun `T` (sort (typ «f5.u2»)) c0 \
     fun `T1` (sort (typ «f5.u3»)) c1 \ fun `x` c0 c2 \ c2) 
   (prod `T` (sort (typ «f5.u0»)) c0 \
     prod `T1` (sort (typ «f5.u1»)) c1 \ prod `x` c0 c2 \ c0) X8 «f5»
  ----<<---- enter:  
  coq.arity->term
   (parameter T explicit (sort (typ «uuu»)) c0 \
     parameter T1 explicit (sort (typ «test.test.197»)) c1 \
      parameter x explicit c0 c2 \ arity c0) X0
  ---->>---- exit:  
  coq.arity->term
   (parameter T explicit (sort (typ «uuu»)) c0 \
     parameter T1 explicit (sort (typ «test.test.197»)) c1 \
      parameter x explicit c0 c2 \ arity c0) 
   (prod `T` (sort (typ «uuu»)) c0 \
     prod `T1` (sort (typ «test.test.197»)) c1 \ prod `x` c0 c2 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «uuu»)) c0 \
       fun `T1` (sort (typ «test.test.197»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.197»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck
     (fun `T` (sort (typ «uuu»)) c0 \
       fun `T1` (sort (typ «test.test.197»)) c1 \ fun `x` c0 c2 \ c2) 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.197»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.197»] ff [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.197»] ff [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.197»] ff [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.197»] ff [] tt) =>
   coq.env.add-const f6 
    (fun `T` (sort (typ «uuu»)) c0 \
      fun `T1` (sort (typ «test.test.197»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.197»)) c1 \ prod `x` c0 c2 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.197»] ff [] tt) =>
   coq.env.add-const f6 
    (fun `T` (sort (typ «uuu»)) c0 \
      fun `T1` (sort (typ «test.test.197»)) c1 \ fun `x` c0 c2 \ c2) 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.197»)) c1 \ prod `x` c0 c2 \ c0) X2 
    «f6»
  f6@{uuux} : forall T : Type@{uuu}, Type@{uuux} -> T -> T
  (* uuux |=  *)
  
  f6 is universe polymorphic
  Arguments f6 (T T1)%type_scope x
  f6 is transparent
  Expands to: Constant test.test.f6
  ----<<---- enter:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0)) X0
  ---->>---- exit:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0)) 
   (prod `T` (sort (typ «uuu»)) c0 \
     prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «Set») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «Set») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f7 (pglobal (const «f6») «Set») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f7 (pglobal (const «f6») «Set») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0) X2 «f7»
  ----<<---- enter:  coq.arity->term (arity X0) X1
  ---->>---- exit:  coq.arity->term (arity X1) X1
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 X2 X3) illtyped arity
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 (typ «test.test.198») (X4)) 
    illtyped arity
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «Set») (X4) X5) 
    illtyped definition
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «Set») 
      (prod `T` (sort (typ «uuu»)) c0 \
        prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0) 
      (pglobal (const «f6») «Set»)) illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X6
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f8 (pglobal (const «f6») «Set») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0) X7 X8
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f8 (pglobal (const «f6») «Set») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «Set»)) c1 \ prod `x` c0 c2 \ c0) X7 «f8»
  ----<<---- enter:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0)) X0
  ---->>---- exit:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0)) 
   (prod `T` (sort (typ «uuu»)) c0 \
     prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «uuu») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «uuu») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f7' (pglobal (const «f6») «uuu») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f7' (pglobal (const «f6») «uuu») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0) X2 «f7'»
  ----<<---- enter:  coq.arity->term (arity X0) X1
  ---->>---- exit:  coq.arity->term (arity X1) X1
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 X2 X3) illtyped arity
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 (typ «test.test.199») (X4)) 
    illtyped arity
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «uuu») (X4) X5) 
    illtyped definition
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «uuu») 
      (prod `T` (sort (typ «uuu»)) c0 \
        prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0) 
      (pglobal (const «f6») «uuu»)) illtyped definition
  ----<<---- enter:  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) X6
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [] tt [] tt) 
   (get-option coq:udecl (upoly-decl [] tt [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f8' (pglobal (const «f6») «uuu») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0) X7 X8
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [] tt [] tt) =>
   coq.env.add-const f8' (pglobal (const «f6») «uuu») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «uuu»)) c1 \ prod `x` c0 c2 \ c0) X7 «f8'»
  ----<<---- enter:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0)) X0
  ---->>---- exit:  
  coq.arity->term
   (arity
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0)) 
   (prod `T` (sort (typ «uuu»)) c0 \
     prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0)
  ----<<---- enter:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «test.test.200») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ---->>---- exit:  
  std.assert-ok!
   (coq.typecheck (pglobal (const «f6») «test.test.200») 
     (prod `T` (sort (typ «uuu»)) c0 \
       prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0)) 
   illtyped definition
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.200»] ff [] tt) X1
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.200»] ff [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.200»] ff [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.200»] ff [] tt) =>
   coq.env.add-const f7'' (pglobal (const «f6») «test.test.200») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0) X2 X3
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.200»] ff [] tt) =>
   coq.env.add-const f7'' (pglobal (const «f6») «test.test.200») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.200»)) c1 \ prod `x` c0 c2 \ c0) X2 
    «f7''»
  ----<<---- enter:  coq.arity->term (arity X0) X1
  ---->>---- exit:  coq.arity->term (arity X1) X1
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 X2 X3) illtyped arity
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok! (coq.elaborate-ty-skeleton X1 (typ «test.test.202») (X4)) 
    illtyped arity
  ----<<---- enter:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «test.test.201») (X4) X5) 
    illtyped definition
  ---->>---- exit:  
  get-option coq:keepunivs tt =>
   std.assert-ok!
    (coq.elaborate-skeleton (pglobal (const «f6») «test.test.201») 
      (prod `T` (sort (typ «uuu»)) c0 \
        prod `T1` (sort (typ «test.test.201»)) c1 \ prod `x` c0 c2 \ c0) 
      (pglobal (const «f6») «test.test.201»)) illtyped definition
  ----<<---- enter:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.201»] ff [] tt) X6
  ---->>---- exit:  
  coq.upoly-decl->attribute (upoly-decl [«test.test.201»] ff [] tt) 
   (get-option coq:udecl (upoly-decl [«test.test.201»] ff [] tt))
  ----<<---- enter:  
  get-option coq:udecl (upoly-decl [«test.test.201»] ff [] tt) =>
   coq.env.add-const f8'' (pglobal (const «f6») «test.test.201») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.201»)) c1 \ prod `x` c0 c2 \ c0) X7 X8
  ---->>---- exit:  
  get-option coq:udecl (upoly-decl [«test.test.201»] ff [] tt) =>
   coq.env.add-const f8'' (pglobal (const «f6») «test.test.201») 
    (prod `T` (sort (typ «uuu»)) c0 \
      prod `T1` (sort (typ «test.test.201»)) c1 \ prod `x` c0 c2 \ c0) X7 
    «f8''»
  const-decl D 
   (some
     (fun `i` (global (indt «I»)) c0 \
       fun `l` (app [global (indt «L»), c0]) c1 \ global (indt «True»))) 
   (parameter i maximal (global (indt «I»)) c0 \
     parameter l maximal (app [global (indt «L»), c0]) c1 \ arity (sort prop)) 
  const-decl D 
   (some
     (fun `i` (global (indt «I»)) c0 \
       fun `H` (app [global (indt «L»), c0]) c1 \ global (indt «True»))) 
   (parameter i maximal (global (indt «I»)) c0 \
     parameter H maximal (app [global (indt «L»), c0]) c1 \ arity (sort prop)) 
  const-decl D 
   (some
     (fun `i` (global (indt «I»)) c0 \
       fun `H` (app [global (indt «L»), c0]) c1 \
        fun `n` (global (indt «nat»)) c2 \ global (indt «True»))) 
   (parameter i maximal (global (indt «I»)) c0 \
     parameter H maximal (app [global (indt «L»), c0]) c1 \
      parameter n explicit (global (indt «nat»)) c2 \ arity (sort prop))
