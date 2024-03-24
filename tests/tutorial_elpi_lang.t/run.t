  $ . ../setup-project.sh
  $ dune build test.vo
  The age of alice is 20
  Query assignments:
    A = 20
  mallory is 23 years old
  Query assignments:
    P = mallory
  alice is 20 years old
  Query assignments:
    P = alice
  mallory and bob are 23 years old
  Query assignments:
    A = 23
    P = mallory
    Q = bob
  I picked P = mallory
  I picked Q = mallory
  I picked Q = bob
  the last choice worked!
  mallory and bob are 23 years old
  Query assignments:
    A = 23
    P = mallory
    Q = bob
  bob is older than alice
  Query assignments:
    X = alice
  both bob and mallory are older than alice
  Query assignments:
    X = alice
  F = c0 \ age alice c0
  F 20 = age alice 20
  F 23 = age alice 23
  Query assignments:
    F = c0 \
  age alice c0
  λx.x ~> fun c0 \ c0
  (λx.x) (λx.x) ~> fun c0 \ c0
  Query assignments:
    I = fun c0 \ c0
    T = fun c0 \ c0
    T1 = fun c0 \ c0
  (Fst foo bar) ~> foo
  (foo bar) ~> app foo bar
  Query assignments:
    Fst = fun c0 \ fun c1 \ c0
    S = app foo bar
    S1 = app foo bar
    T = app (app (fun c0 \ fun c1 \ c0) foo) bar
    T1 = foo
  The type of λx.λy.x is: arr X0 (arr X1 X0)
  Query assignments:
    Ty = arr X0 (arr X1 X0)
  Error: fun c0 \ app c0 c0 has no type
  Query assignments:
    Delta = fun c0 \ app c0 c0
    Ty = X0
  2 + 1 = s (s (s z))
  Query assignments:
    R = s (s (s z))
  Query assignments:
    X = X0
    Z = X1
  Syntactic constraints:  sum X0 (s z) X1  /* suspended on X0 */
  The result is: s z
  Query assignments:
    X = z
    Z = s z
  Query assignments:
    X = s z
   sum X0 (s z) X1  /* suspended on X0 */
  Currently Y = X1
   sum X2 (s z) X3  /* suspended on X2 */
  Currently Y = s X3
  Finally Y = s (s z)
  Query assignments:
    X = s z
    Y = s (s z)
    Z = z
  Query assignments:
    X = X0
  Syntactic constraints:
   even X0  /* suspended on X0 */ odd X0  /* suspended on X0 */
  X0 can't be even and odd at the same time
  Query assignments:
    A = [1, 2, 3, 3, 2, 1]
  Query assignments:
    A = [1, 2, 3, 3, 2, 1]
  result = 5
  Query assignments:
    X = result =
    Y = 5
  result = 5
  Query assignments:
    Spilled_1 = 5
  Query assignments:
    R1 = X0
    R2 = [2, 3, 4]
    R3 = [2, 3, 4]
  Query assignments:
    R = [2, 3, 4]
  Y = c0
  arr X0 (arr X1 X0)
  Query assignments:
    Ty = arr X0 (arr X1 X0)
  run 1 {{{  
            
    rid:0 step:1 gid:6 user:curgoal = , 
                                      of (fun c0 \ fun c1 \ c0) X0 , coq.say X0 
                                      
    rid:0 step:1 gid:6 user:rule = and 
                                   
    rid:0 step:1 gid:6 user:subgoal = 7 
                                      
    rid:0 step:1 gid:7 user:newgoal = of (fun c0 \ fun c1 \ c0) X0 
                                      
    rid:0 step:1 gid:6 user:subgoal = 8 
                                      
    rid:0 step:1 gid:8 user:newgoal = coq.say X0 
                                      
    rid:0 step:1 gid:6 user:rule:and = success 
                                       
  }}} ->  (0.000s)
  run 2 {{{  
            
    rid:0 step:2 gid:7 user:curgoal = of 
                                      of (fun c0 \ fun c1 \ c0) X0 
                                      
    rid:0 step:2 gid:7 user:rule = backchain 
                                   
    rid:0 step:2 gid:7 user:rule:backchain:candidates = File "./test.v", line 596, column 3, character 15363: 
                                                        
  }}} ->  (0.000s)
  select 3 {{{  
               
    rid:0 step:2 gid:7 user:rule:backchain:try = File "./test.v", line 596, column 3, character 15363: 
                                                 (of (fun A0) (arr A1 A2)) :- (
                                                  pi (c0 \
                                                   (of c0 A1 => of (A0 c0) A2))). 
                                                 
    rid:0 step:2 gid:0 user:assign = A0 := c0 \
                                     fun c1 \ c0 
                                     
    rid:0 step:2 gid:0 user:assign = X0 := arr X1 X2 
                                     
    rid:0 step:2 gid:7 user:subgoal = 9 
                                      
    rid:0 step:2 gid:9 user:newgoal = pi c0 \ of c0 X1 => of (fun c1 \ c0) X2 
                                      
    rid:0 step:2 gid:9 user:rule:backchain = success 
                                             
  }}} ->  (0.000s)
  run 3 {{{  
            
    rid:0 step:3 gid:9 user:curgoal = pi 
                                      pi c0 \ of c0 X1 => of (fun c1 \ c0) X2 
                                      
    rid:0 step:3 gid:9 user:rule = pi 
                                   
    rid:0 step:3 gid:9 user:subgoal = 10 
                                      
    rid:0 step:3 gid:10 user:newgoal = of c0 X1 => of (fun c1 \ c0) X2 
                                       
    rid:0 step:3 gid:10 user:rule:pi = success 
                                       
  }}} ->  (0.000s)
  run 4 {{{  
            
    rid:0 step:4 gid:10 user:curgoal = => 
                                       of c0 X1 => of (fun c1 \ c0) X2 
                                       
    rid:0 step:4 gid:10 user:rule = implication 
                                    
    rid:0 step:4 gid:10 user:subgoal = 11 
                                       
    rid:0 step:4 gid:11 user:newgoal = of (fun c1 \ c0) X2 
                                       
    rid:0 step:4 gid:11 user:rule:implication = success 
                                                
  }}} ->  (0.000s)
  run 5 {{{  
            
    rid:0 step:5 gid:11 user:curgoal = of 
                                       of (fun c1 \ c0) X2 
                                       
    rid:0 step:5 gid:11 user:rule = backchain 
                                    
    rid:0 step:5 gid:11 user:rule:backchain:candidates = File "./test.v", line 596, column 3, character 15363: 
                                                         
  }}} ->  (0.000s)
  select 4 {{{  
               
    rid:0 step:5 gid:11 user:rule:backchain:try = File "./test.v", line 596, column 3, character 15363: 
                                                  (of (fun A0) (arr A1 A2)) :- (
                                                   pi (c0 \
                                                    (of c0 A1 => of (A0 c0) A2))). 
                                                  
    rid:0 step:5 gid:0 user:assign = A0 := c1 \
                                     c0 
                                     
    rid:0 step:5 gid:0 user:assign = X2 := arr X3 X4 
                                     
    rid:0 step:5 gid:11 user:subgoal = 12 
                                       
    rid:0 step:5 gid:12 user:newgoal = pi c1 \ of c1 X3 => of c0 X4 
                                       
    rid:0 step:5 gid:12 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 6 {{{  
            
    rid:0 step:6 gid:12 user:curgoal = pi 
                                       pi c1 \ of c1 X3 => of c0 X4 
                                       
    rid:0 step:6 gid:12 user:rule = pi 
                                    
    rid:0 step:6 gid:12 user:subgoal = 13 
                                       
    rid:0 step:6 gid:13 user:newgoal = of c1 X3 => of c0 X4 
                                       
    rid:0 step:6 gid:13 user:rule:pi = success 
                                       
  }}} ->  (0.000s)
  run 7 {{{  
            
    rid:0 step:7 gid:13 user:curgoal = => 
                                       of c1 X3 => of c0 X4 
                                       
    rid:0 step:7 gid:13 user:rule = implication 
                                    
    rid:0 step:7 gid:13 user:subgoal = 14 
                                       
    rid:0 step:7 gid:14 user:newgoal = of c0 X4 
                                       
    rid:0 step:7 gid:14 user:rule:implication = success 
                                                
  }}} ->  (0.000s)
  run 8 {{{  
            
    rid:0 step:8 gid:14 user:curgoal = of 
                                       of c0 X4 
                                       
    rid:0 step:8 gid:14 user:rule = backchain 
                                    
    rid:0 step:8 gid:14 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 5 {{{  
               
    rid:0 step:8 gid:14 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 X1) :- . 
                                                  
    rid:0 step:8 gid:0 user:assign = X1 := X4 
                                     
    rid:0 step:8 gid:14 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 9 {{{  
            
    rid:0 step:9 gid:8 user:curgoal = coq.say 
                                      coq.say (arr X4 (arr X3 X4)) 
                                      
    rid:0 step:9 gid:8 user:rule = builtin 
                                   
    rid:0 step:9 gid:8 user:rule:builtin:name = coq.say 
                                                
  arr X4 (arr X3 X4)
    rid:0 step:9 gid:8 user:rule:builtin = success 
                                           
  }}} ->  (0.000s)
  Query assignments:
    Ty = arr X4 (arr X3 X4)
  run 1 {{{  
            
    rid:1 step:1 gid:15 user:curgoal = , 
                                       of (fun c0 \ app c0 c0) X0 , coq.say X0 
                                       
    rid:1 step:1 gid:15 user:rule = and 
                                    
    rid:1 step:1 gid:15 user:subgoal = 16 
                                       
    rid:1 step:1 gid:16 user:newgoal = of (fun c0 \ app c0 c0) X0 
                                       
    rid:1 step:1 gid:15 user:subgoal = 17 
                                       
    rid:1 step:1 gid:17 user:newgoal = coq.say X0 
                                       
    rid:1 step:1 gid:15 user:rule:and = success 
                                        
  }}} ->  (0.000s)
  run 2 {{{  
            
    rid:1 step:2 gid:16 user:curgoal = of 
                                       of (fun c0 \ app c0 c0) X0 
                                       
    rid:1 step:2 gid:16 user:rule = backchain 
                                    
    rid:1 step:2 gid:16 user:rule:backchain:candidates = File "./test.v", line 596, column 3, character 15363: 
                                                         
  }}} ->  (0.000s)
  select 3 {{{  
               
    rid:1 step:2 gid:16 user:rule:backchain:try = File "./test.v", line 596, column 3, character 15363: 
                                                  (of (fun A0) (arr A1 A2)) :- (
                                                   pi (c0 \
                                                    (of c0 A1 => of (A0 c0) A2))). 
                                                  
    rid:1 step:2 gid:0 user:assign = A0 := c0 \
                                     app c0 c0 
                                     
    rid:1 step:2 gid:0 user:assign = X0 := arr X1 X2 
                                     
    rid:1 step:2 gid:16 user:subgoal = 18 
                                       
    rid:1 step:2 gid:18 user:newgoal = pi c0 \ of c0 X1 => of (app c0 c0) X2 
                                       
    rid:1 step:2 gid:18 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 3 {{{  
            
    rid:1 step:3 gid:18 user:curgoal = pi 
                                       pi c0 \ of c0 X1 => of (app c0 c0) X2 
                                       
    rid:1 step:3 gid:18 user:rule = pi 
                                    
    rid:1 step:3 gid:18 user:subgoal = 19 
                                       
    rid:1 step:3 gid:19 user:newgoal = of c0 X1 => of (app c0 c0) X2 
                                       
    rid:1 step:3 gid:19 user:rule:pi = success 
                                       
  }}} ->  (0.000s)
  run 4 {{{  
            
    rid:1 step:4 gid:19 user:curgoal = => 
                                       of c0 X1 => of (app c0 c0) X2 
                                       
    rid:1 step:4 gid:19 user:rule = implication 
                                    
    rid:1 step:4 gid:19 user:subgoal = 20 
                                       
    rid:1 step:4 gid:20 user:newgoal = of (app c0 c0) X2 
                                       
    rid:1 step:4 gid:20 user:rule:implication = success 
                                                
  }}} ->  (0.000s)
  run 5 {{{  
            
    rid:1 step:5 gid:20 user:curgoal = of 
                                       of (app c0 c0) X2 
                                       
    rid:1 step:5 gid:20 user:rule = backchain 
                                    
    rid:1 step:5 gid:20 user:rule:backchain:candidates = File "./test.v", line 591, column 3, character 15198: 
                                                         
  }}} ->  (0.000s)
  select 4 {{{  
               
    rid:1 step:5 gid:20 user:rule:backchain:try = File "./test.v", line 591, column 3, character 15198: 
                                                  (of (app A0 A1) A2) :- (
                                                   of A0 (arr A3 A2)), 
                                                   (of A1 A3). 
                                                  
    rid:1 step:5 gid:0 user:assign = A0 := c0 
                                     
    rid:1 step:5 gid:0 user:assign = A1 := c0 
                                     
    rid:1 step:5 gid:0 user:assign = A2 := X2 
                                     
    rid:1 step:5 gid:20 user:subgoal = 21 
                                       
    rid:1 step:5 gid:21 user:newgoal = of c0 (arr X3^1 X2) 
                                       
    rid:1 step:5 gid:21 user:subgoal = 22 
                                       
    rid:1 step:5 gid:22 user:newgoal = of c0 X3^1 
                                       
    rid:1 step:5 gid:21 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 6 {{{  
            
    rid:1 step:6 gid:21 user:curgoal = of 
                                       of c0 (arr X3^1 X2) 
                                       
    rid:1 step:6 gid:21 user:rule = backchain 
                                    
    rid:1 step:6 gid:21 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 5 {{{  
               
    rid:1 step:6 gid:21 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 X1) :- . 
                                                  
    rid:1 step:6 gid:0 user:assign:expand = X3^1 := X4 c0 
                                            
    rid:1 step:6 gid:0 user:assign:restrict = 0 X4 c0 := c0 \
                                              .X5 
                                              
    rid:1 step:6 gid:0 user:assign = X1 := arr X5 X2 
                                     
    rid:1 step:6 gid:21 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 7 {{{  
            
    rid:1 step:7 gid:22 user:curgoal = of 
                                       of c0 X5 
                                       
    rid:1 step:7 gid:22 user:rule = backchain 
                                    
    rid:1 step:7 gid:22 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 6 {{{  
               
    rid:1 step:7 gid:22 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 (arr X5 X2)) :- . 
                                                  
    rid:1 step:7 gid:22 user:backchain:fail-to = unify X5 with arr X5 X2 
                                                 
  }}} ->  (0.000s)
  select 7 {{{  
               
    rid:1 step:7 gid:22 user:rule:backchain = fail 
                                              
  }}} ->  (0.000s)
  run 6 {{{  
            
    rid:2 step:6 gid:29 user:curgoal = pi 
                                       pi c1 \ of c1 X0 => of c0 X1 
                                       
    rid:2 step:6 gid:29 user:rule = pi 
                                    
    rid:2 step:6 gid:29 user:subgoal = 30 
                                       
    rid:2 step:6 gid:30 user:newgoal = of c1 X0 => of c0 X1 
                                       
    rid:2 step:6 gid:30 user:rule:pi = success 
                                       
  }}} ->  (0.000s)
  run 7 {{{  
            
    rid:2 step:7 gid:30 user:curgoal = => 
                                       of c1 X0 => of c0 X1 
                                       
    rid:2 step:7 gid:30 user:rule = implication 
                                    
    rid:2 step:7 gid:30 user:subgoal = 31 
                                       
    rid:2 step:7 gid:31 user:newgoal = of c0 X1 
                                       
    rid:2 step:7 gid:31 user:rule:implication = success 
                                                
  }}} ->  (0.000s)
  run 8 {{{  
            
    rid:2 step:8 gid:31 user:curgoal = of 
                                       of c0 X1 
                                       
    rid:2 step:8 gid:31 user:rule = backchain 
                                    
    rid:2 step:8 gid:31 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 5 {{{  
               
    rid:2 step:8 gid:31 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 X2) :- . 
                                                  
    rid:2 step:8 gid:0 user:assign = X2 := X1 
                                     
    rid:2 step:8 gid:31 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  arr X1 (arr X0 X1)
  Query assignments:
    Ty = arr X1 (arr X0 X1)
  run 2 {{{  
            
    rid:3 step:2 gid:33 user:curgoal = of 
                                       of (fun c0 \ fun c1 \ c0) X0 
                                       
    rid:3 step:2 gid:33 user:rule = backchain 
                                    
    rid:3 step:2 gid:33 user:rule:backchain:candidates = File "./test.v", line 596, column 3, character 15363: 
                                                         
  }}} ->  (0.000s)
  select 3 {{{  
               
    rid:3 step:2 gid:33 user:rule:backchain:try = File "./test.v", line 596, column 3, character 15363: 
                                                  (of (fun A0) (arr A1 A2)) :- (
                                                   pi (c0 \
                                                    (of c0 A1 => of (A0 c0) A2))). 
                                                  
    rid:3 step:2 gid:0 user:assign = A0 := c0 \
                                     fun c1 \ c0 
                                     
    rid:3 step:2 gid:0 user:assign = X0 := arr X1 X2 
                                     
    rid:3 step:2 gid:33 user:subgoal = 35 
                                       
    rid:3 step:2 gid:35 user:newgoal = pi c0 \ of c0 X1 => of (fun c1 \ c0) X2 
                                       
    rid:3 step:2 gid:35 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 5 {{{  
            
    rid:3 step:5 gid:37 user:curgoal = of 
                                       of (fun c1 \ c0) X2 
                                       
    rid:3 step:5 gid:37 user:rule = backchain 
                                    
    rid:3 step:5 gid:37 user:rule:backchain:candidates = File "./test.v", line 596, column 3, character 15363: 
                                                         
  }}} ->  (0.000s)
  select 4 {{{  
               
    rid:3 step:5 gid:37 user:rule:backchain:try = File "./test.v", line 596, column 3, character 15363: 
                                                  (of (fun A0) (arr A1 A2)) :- (
                                                   pi (c0 \
                                                    (of c0 A1 => of (A0 c0) A2))). 
                                                  
    rid:3 step:5 gid:0 user:assign = A0 := c1 \
                                     c0 
                                     
    rid:3 step:5 gid:0 user:assign = X2 := arr X3 X4 
                                     
    rid:3 step:5 gid:37 user:subgoal = 38 
                                       
    rid:3 step:5 gid:38 user:newgoal = pi c1 \ of c1 X3 => of c0 X4 
                                       
    rid:3 step:5 gid:38 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  run 8 {{{  
            
    rid:3 step:8 gid:40 user:curgoal = of 
                                       of c0 X4 
                                       
    rid:3 step:8 gid:40 user:rule = backchain 
                                    
    rid:3 step:8 gid:40 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 5 {{{  
               
    rid:3 step:8 gid:40 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 X1) :- . 
                                                  
    rid:3 step:8 gid:0 user:assign = X1 := X4 
                                     
    rid:3 step:8 gid:40 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  arr X4 (arr X3 X4)
  Query assignments:
    Ty = arr X4 (arr X3 X4)
  run 8 {{{  
            
    rid:4 step:8 gid:49 user:curgoal = of 
                                       of c0 X0 
                                       
    rid:4 step:8 gid:49 user:rule = backchain 
                                    
    rid:4 step:8 gid:49 user:rule:backchain:candidates = File "(context step_id:4)", line 1, column 0, character 0: 
                                                         
  }}} ->  (0.000s)
  select 5 {{{  
               
    rid:4 step:8 gid:49 user:rule:backchain:try = File "(context step_id:4)", line 1, column 0, character 0: 
                                                  (of c0 X1) :- . 
                                                  
    rid:4 step:8 gid:0 user:assign = X1 := X0 
                                     
    rid:4 step:8 gid:49 user:rule:backchain = success 
                                              
  }}} ->  (0.000s)
  arr X0 (arr X2 X0)
  Query assignments:
    Ty = arr X0 (arr X2 X0)
  calling mypred on  3
  calling mypred on  2
  calling mypred on  1
  calling mypred on  0
  ok
  Query assignments:
    A = X0
    B = X0
    C = X0
