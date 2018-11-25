(*
   Desta Pickering
   CptS Hw2 - SML Functions
   Semptember 24, 2018
*)

Control.Print.printDepth := 100;

(* Filter function used through out *)
fun filterAll aFun [] = []
   | filterAll aFun (cur::rest_of_list) =
      if aFun cur 
         then cur::(filterAll aFun rest_of_list)
      else (filterAll aFun rest_of_list)

(* Map function used through out *)
fun mapAll aFun [] = []
   | mapAll aFun (cur::rest_of_list) = 
      (aFun cur)::(mapAll aFun rest_of_list);

(* Fold function used through out *)
fun foldAll aFun base [] = base
   | foldAll aFun base (cur::rest_of_list) = 
      aFun cur (foldAll aFun base rest_of_list);

(* Problem 1: numbersToSum and numbersToSumTail *)

(* Part A: Non tail recursive solution to numbers to sum *)
fun numbersToSum sum [] = []
   | numbersToSum sum (cur_elem::rest_list) =
   if sum - cur_elem > 0 
      then cur_elem::(numbersToSum (sum-cur_elem) rest_list)
   else [];

(* Part B: Tail recursive solution to numbers to sum *)
fun numbersToSumTail sum [] = []                                                 
   | numbersToSumTail sum List =                                                 
      let
         
         (* Helper functions *)
         fun findTotal cur [] = cur                                                     
            | findTotal cur (x::rest) = 
               (findTotal (cur+x) rest)                      
      
      in                                                                            
         if findTotal 0 List < sum 
            then List                                            
         else numbersToSumTail sum (rev (tl (rev List)))                            
      
      end;  

(* Problem 2: Partition *)
fun partition func cur_list =
   
   let
      
      (* Helper functions *)
      fun exists desired [] = false
         | exists desired (cur::rest_of_list) = 
            if desired = cur 
               then true 
            else (exists desired rest_of_list);
   
   in
      (filterAll func cur_list, filterAll (not o func) cur_list)
   
   end;     

(* Problem 3: areAllUnique *)
fun areAllUnique [] = true
   | areAllUnique cur_list = 
      
      let
         
         (* Helper functions *)
         fun countInList [] desired = 0
            | countInList (cur::rest_of_list) desired =
               if desired = cur 
                  then (countInList rest_of_list desired) + 1
               else (countInList rest_of_list desired)
         
         fun mapUnique [] = []
            | mapUnique (cur::rest_of_list) =
               (countInList rest_of_list cur)::(mapUnique rest_of_list);
         
         fun filterUnique bool = 
            if bool = 0 
               then false
            else true
   
   in
      if filterAll filterUnique (mapUnique cur_list) = [] 
         then true
      else false
   
   end;

(* Problem 4: sum, sumOption, and sumEither *)

(* Part A: Sum *)
fun sum cur_list =
   
   let
   
      (* Helper functions *)
      fun sumSum x y = x + y
      
      fun sumFold [] = 0
         | sumFold cur_list =
         foldAll sumSum 0 cur_list
      
      fun mapSum cur_list = 
         map sumFold cur_list
   
   in
      sumFold (mapSum cur_list)
   
   end;

(* Part B: sumOption *)
fun sumOption cur_list =
   
   let
      
      (* Helper functions *)
      fun addOpt x y = SOME((getOpt(x, 0)) + (getOpt(y, 0)))
      
      fun sumOpt [] = NONE
         | sumOpt cur_list = 
            if foldAll addOpt NONE cur_list = SOME 0 
               then NONE
            else foldAll addOpt NONE cur_list
      
      fun mapOpt cur_list = 
         map sumOpt cur_list
   
   in
      (sumOpt (mapOpt cur_list))
   
   end;

(* Part C: sumEither *)
datatype either = IString of string | IInt of int;

fun sumEither cur_list =
   
   let
      
      (* Function helpers *)
      fun to_int elem = 
         valOf(Int.fromString(elem))
      
      fun addEither ( IString(x)) (IString (y)) = 
            IInt((to_int x) + (to_int y))
         | addEither (IInt (x)) (IInt (y)) = 
            IInt (x + y)
         | addEither (IString (x)) (IInt (y)) = 
            IInt(to_int (x) + y)
         | addEither (IInt (x)) (IString (y)) = 
            IInt(x + (to_int y))
      
      fun sumEitherFold [] = IInt(0)
         | sumEitherFold cur_list = 
            foldAll addEither (IInt(0)) cur_list
      
      fun mapEither cur_list = 
         mapAll sumEitherFold cur_list
   
   in
      sumEitherFold (mapEither cur_list)
   
   end;

(* Question 5: depthScan, depthSearch, addTrees *)

datatype 'a Tree = LEAF of 'a | NODE of 'a * ('a Tree) * ('a Tree);

(* Part A: depthScan *)
fun depthScan (LEAF (n)) = [n]
   | depthScan (NODE (n, t1, t2)) = 
      (depthScan (t1))@((depthScan(t2))@[n]);

(* Part B: depthSearch *)
fun depthSearch (LEAF (n)) coun = if n = coun then 1 else ~1 
   | depthSearch (NODE (n, t1, t2)) coun =
      
      let
         
         (* Function helpers *)
         fun DepthSearch x y = 
            if x = y
               then 1 
            else ~1
      
      in
         if (depthSearch (t1) coun) <> ~1
            then (depthSearch (t1) coun) + 1
         else if (depthSearch (t2) coun) <> ~1
            then (depthSearch (t2) coun) + 1
         else if (DepthSearch n coun) = 1 
            then 1
         else ~1
      
      end;

(* Part C: addTrees *)
fun  addTrees (LEAF (x)) (LEAF (y)) = 
      LEAF(x + y)
   | addTrees (NODE (x, xT1, xT2)) (NODE (y, yT1, yT2)) = 
      NODE ((x + y), (addTrees (xT1) (yT1)), (addTrees (xT2) (yT2)))
   | addTrees (LEAF (x)) (NODE (y, yT1, yT2)) = 
      NODE ((x + y), (yT1), (yT2))     
   | addTrees (NODE (x, xT1, xT2)) (LEAF (y)) =
      NODE ((x + y), (xT1), (xT2));

(** Test Cases Below **)

(* Testing numbersToSum *)
fun numbersToSumTest () =
   
   let
      
      (* Testing values *)
      val numbersToSumT1 = numbersToSum 5 [ 1, 2, 3, 4, 5] = [ 1, 2]
      val numbersToSumT2 = numbersToSum 100 [ 10, 20, 30, 40] = [ 10, 20, 30]
      val numbersToSumT3 = numbersToSum 1 [2] = []
      val numbersToSumT4 = numbersToSum 1 [] = []
      val numbersToSumT5 = numbersToSum 0 [ 1, 2, 3, 4, 5] = []
      val numbersToSumT6 = numbersToSum 300 [ 1, 2, 3, 4, 5] = [ 1, 2, 3, 4, 5]
      val numbersToSumT7 = numbersToSum 40 [ 30, 20, 10, 0] = [30]
      val numbersToSumT8 = numbersToSum 10 [ 0, 0, 0, 0, 0] = [ 0, 0, 0, 0, 0]
   
   in
      print (
      ">> Test Results for Numbers to Sum \n"   ^
      "  test1:\t" ^ Bool.toString(numbersToSumT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(numbersToSumT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(numbersToSumT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(numbersToSumT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(numbersToSumT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(numbersToSumT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(numbersToSumT7) ^ "\n" ^
      "  test8:\t" ^ Bool.toString(numbersToSumT8) ^ "\n" ^
      "\n"
      )       
   
   end;

val _ = numbersToSumTest ();

(* Testing numbersToSumTail *)
fun numbersToSumTailTest () =

   let
      
      (* Testing Values *)
      val numbersToSumTailT1 = numbersToSumTail 5 [ 1, 2, 3, 4, 5] = [ 1, 2]    
      val numbersToSumTailT2 = numbersToSumTail 100 [ 10, 20, 30, 40] = [ 10, 20,30]        
      val numbersToSumTailT3 = numbersToSumTail 1 [2] = []
      val numbersToSumTailT4 = numbersToSumTail 1 [] = []
      val numbersToSumTailT5 = numbersToSumTail 0 [ 1, 2, 3, 4, 5] = []
      val numbersToSumTailT6 = numbersToSumTail 2 [1] = [1]
      val numbersToSumTailT7 = numbersToSumTail 1 [1] = []
      val numbersToSumTailT8 = numbersToSumTail 10000 [ 50, 40, 30, 20, 10] = [ 50, 40, 30, 20, 10]
   
   in
      print (
      ">> Test Results for Numbers to Sum by TailRecursion\n" ^          
      "  test1:\t" ^ Bool.toString(numbersToSumTailT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(numbersToSumTailT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(numbersToSumTailT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(numbersToSumTailT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(numbersToSumTailT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(numbersToSumTailT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(numbersToSumTailT7) ^ "\n" ^
      "  test8:\t" ^ Bool.toString(numbersToSumTailT8) ^ "\n" ^
      "\n"
      )
   
   end;

val _ = numbersToSumTailTest ();

fun partitionTest () =
   
   let
      (* Use for a function later *)
      fun exists n [] = false                                                    
         | exists n (x::rest) = if n=x then true else (exists n rest)            
      
      (* Values Tested *)
      val partitionT1 = partition (fn x => (x<=4)) [1,7,4,5,3,8,2,3] = ([1,4,3,2,3],[7,5,8])
      val partitionT2 = partition null [[1,2],[1],[],[5],[],[6,7,8]] = ([[],[]],[[1,2],[1],[5],[6,7,8]])
      val partitionT3 = partition (fn x=>(x<=5)) [] = ([],[])
      val partitionT4 = partition null []= ([],[])
      val partitionT5 = partition (fn x =>(x=1)) [1,1,1] = ([1,1,1],[])
      val partitionT6 = partition (fn x =>(x=2)) [1,1,1] = ([],[1,1,1])
      val partitionT7 = partition (exists 1) [[1,2],[1],[],[5],[],[6,7,8]] = ([[1,2],[1]],[[],[5],[],[6,7,8]])
   
   in
      print (
      ">> Test Results for partition\n" ^
      "  test1:\t" ^ Bool.toString(partitionT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(partitionT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(partitionT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(partitionT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(partitionT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(partitionT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(partitionT7) ^ "\n" ^
      "\n"
      )
   
   end;

val _ = partitionTest ();

(* Testing areAllUnique *)
fun areAllUniqueTest () =
   
   let
      
      (* Value tested *)
      val areAllUniqueT1 = areAllUnique [] = true
      val areAllUniqueT2 = areAllUnique [1,1,1,1,1] = false
      val areAllUniqueT3 = areAllUnique [1] = true
      val areAllUniqueT4 = areAllUnique [1,2,3,4,3,2,1] = false
      val areAllUniqueT5 = areAllUnique [1,2,3,4,5,6,7,8] = true
      val areAllUniqueT6 = areAllUnique [[],[]] = false
      val areAllUniqueT7 = areAllUnique [[1,2,3],[1,4,5]] = true
   
   in
      print (
      ">> Test Results for Are All Unique\n" ^
      "  test1:\t" ^ Bool.toString(areAllUniqueT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(areAllUniqueT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(areAllUniqueT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(areAllUniqueT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(areAllUniqueT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(areAllUniqueT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(areAllUniqueT7) ^ "\n" ^
      "\n"
      )
   
   end;

val _ = areAllUniqueTest ();

(* Testing sum *)
fun sumTest () =
   
   let
      
      (* Values tested *)
      val sumT1 = sum [] = 0
      val sumT2 = sum [[1]] = 1
      val sumT3 = sum [[1],[1]] = 2
      val sumT4 = sum [[20, 30], [40, 50]] = 140
      val sumT5 = sum [[12,12,12],[12,12,12,12], [12,12],[12]] = 120
      val sumT6 = sum [[]] = 0
      val sumT7 = sum [[1,2,3,4,5,6,7,8,9]] = 45
   
   in
      print(
      ">> Test Results for sum \n" ^
      "  test1:\t" ^ Bool.toString(sumT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(sumT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(sumT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(sumT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(sumT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(sumT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(sumT7) ^ "\n" ^
      "\n"
      )

   end;

val _ = sumTest ();

(* Testing sumOption *)
fun sumOptionTest () =
   
   let
      
      (* Values tested *)
      val sumOptionT1 = sumOption [] = NONE
      val sumOptionT2 = sumOption [[]] = NONE
      val sumOptionT3 = sumOption [[NONE]] = NONE
      val sumOptionT4 = sumOption [[SOME (1)]] = SOME 1
      val sumOptionT5 = sumOption [[NONE, NONE, NONE]] = NONE
      val sumOptionT6 = sumOption [[NONE, NONE], [NONE, NONE]] = NONE
      val sumOptionT7 = sumOption [[NONE],[NONE],[NONE]] = NONE
      val sumOptionT8 = sumOption [[NONE, SOME(1)],[SOME(12), SOME(12), SOME(1)], [NONE]] = SOME 26
   
   in
      print (
      ">> Test Results for sum option\n" ^
      "  test1:\t" ^ Bool.toString(sumOptionT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(sumOptionT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(sumOptionT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(sumOptionT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(sumOptionT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(sumOptionT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(sumOptionT7) ^ "\n" ^
      "  test8:\t" ^ Bool.toString(sumOptionT8) ^ "\n" ^
      "\n"
      )
   
   end;

val _ = sumOptionTest ();

(* Testing sumEither *)
fun sumEitherTest () =
   
   let
      
      (* Values Tested *)
      val sumEitherT1 = sumEither [[]] = IInt 0
      val sumEitherT2 = sumEither [[IString "1"]] = IInt 1
      val sumEitherT3 = sumEither [[IInt 1]] = IInt 1
      val sumEitherT4 = sumEither [[IInt 6], [IString "3"]] = IInt 9
      val sumEitherT5 = sumEither [[IString "4"], [IString "6", IString "10"]] = IInt 20
      val sumEitherT6 = sumEither [[IInt 5, IInt 5], [IInt 8, IInt 8]] = IInt 26
      val sumEitherT7 = sumEither [[],[IInt 6],[],[IString "6"]] = IInt 12
   
   in
      print (
      ">> Test Results for sum either\n" ^
      "  test1:\t" ^ Bool.toString(sumEitherT1) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(sumEitherT2) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(sumEitherT3) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(sumEitherT4) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(sumEitherT5) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(sumEitherT6) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(sumEitherT7) ^ "\n" ^
      "\n"
      )
   
   end;

val _ = sumEitherTest ();

fun compoundTreeTest () = 
   
   let
      (* Trees tested *)
      val tree1 = (NODE (9, NODE (10, NODE(3, LEAF 11, LEAF 90),   LEAF 100), LEAF 7))
      val tree2 = NODE(1, NODE (2, LEAF 3, LEAF 6), NODE(7, NODE(8, LEAF 10 ,LEAF   11),LEAF 9))
      val tree3 =  NODE(1, NODE (2, NODE(3, LEAF 2 ,LEAF 5),LEAF 1), NODE(1,LEAF 8,  LEAF 5))
      
      (* Testing depth scan *)
      val depthScanT01 = depthScan tree1 = [11,90,3,100,10,7,9] 
      val depthScanT02 = depthScan tree2 = [3,6,2,10,11,8,9,7,1]  
      val depthScanT03 = depthScan tree3 = [2,5,3,1,2,8,5,1,1] 

      (* Testing depth search *)
      val depthSearchT01 = depthSearch tree1 9 = 1
      val depthSearchT02 = depthSearch tree1 90 = 4
      val depthSearchT03 = depthSearch tree1 7 = 2
      val depthSearchT04 = depthSearch tree1 99 = ~1

      val depthSearchT05 = depthSearch tree2 1 = 1
      val depthSearchT06 = depthSearch tree2 10 = 4
      val depthSearchT07 = depthSearch tree2 11 = 4
      val depthSearchT08 = depthSearch tree2 99 = ~1

      val depthSearchT09 = depthSearch tree3 8 = 3
      val depthSearchT10 = depthSearch tree3 2 = 4
      val depthSearchT11 = depthSearch tree3 1 = 3
      val depthSearchT12 = depthSearch tree3 99 = ~1

      (* Testing add tree *)
      val addTreeT01 = addTrees tree1 tree2 = NODE
    (10,NODE (12,NODE (6,LEAF 11,LEAF 90),LEAF 106),
     NODE (14,NODE (8,LEAF 10,LEAF 11),LEAF 9)) 
      val addTreeT02 = addTrees tree2 tree3 = NODE
    (2,NODE (4,NODE (6,LEAF 2,LEAF 5),LEAF 7),
     NODE (8,NODE (16,LEAF 10,LEAF 11),LEAF 14))
      val addTreeT03 = addTrees tree3 tree3 = NODE (2,NODE (4,NODE (6,LEAF 4,LEAF 10),LEAF 2),NODE (2,LEAF 16,LEAF 10))
      val addTreeT04 = addTrees tree1 tree1 = NODE (18,NODE (20,NODE (6,LEAF 22,LEAF 180),LEAF 200),LEAF 14)
      val addTreeT05 = addTrees tree2 tree2 =  NODE (2,NODE (4,LEAF 6,LEAF 12),NODE (14,NODE (16,LEAF 20,LEAF 22),LEAF 18))
      val addTreeT06 = addTrees tree3 tree3 =  NODE (2,NODE (4,NODE (6,LEAF 4,LEAF 10),LEAF 2),NODE (2,LEAF 16,LEAF 10))
      val addTreeT07 = addTrees tree1 (addTrees tree2 tree3) = NODE
    (11,NODE (14,NODE (9,LEAF 13,LEAF 95),LEAF 107),
     NODE (15,NODE (16,LEAF 10,LEAF 11),LEAF 14))

   in 
      print(
      ">> Generic Tree testing \n" ^
      ">>>>>Depth Scan Test Results\n"  ^
      "  test1:\t" ^ Bool.toString(depthScanT01) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(depthScanT02) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(depthScanT03) ^ "\n" ^
      "\n" ^
      ">>>>> Depth Search Test Results\n" ^
      "  test1:\t" ^ Bool.toString(depthSearchT01) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(depthSearchT02) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(depthSearchT03) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(depthSearchT04) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(depthSearchT05) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(depthSearchT06) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(depthSearchT07) ^ "\n" ^
      "  test8:\t" ^ Bool.toString(depthSearchT08) ^ "\n" ^
      "  test9:\t" ^ Bool.toString(depthSearchT09) ^ "\n" ^
      "  test10:\t" ^ Bool.toString(depthSearchT10) ^ "\n" ^
      "  test11:\t" ^ Bool.toString(depthSearchT11) ^ "\n" ^
      "  test12:\t" ^ Bool.toString(depthSearchT12) ^ "\n" ^
      "\n" ^
      ">>>>> Add to Tree Test Results \n" ^
      "  test1:\t" ^ Bool.toString(addTreeT01) ^ "\n" ^
      "  test2:\t" ^ Bool.toString(addTreeT02) ^ "\n" ^
      "  test3:\t" ^ Bool.toString(addTreeT03) ^ "\n" ^
      "  test4:\t" ^ Bool.toString(addTreeT04) ^ "\n" ^
      "  test5:\t" ^ Bool.toString(addTreeT05) ^ "\n" ^
      "  test6:\t" ^ Bool.toString(addTreeT06) ^ "\n" ^
      "  test7:\t" ^ Bool.toString(addTreeT07) ^ "\n"
      )
   
   end;

val _ = compoundTreeTest ();
