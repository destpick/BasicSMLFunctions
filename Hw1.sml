(*
   Desta Pickering
   CptS Hw1 - SML Functions
   Semptember 12, 2018
*)


(* 
  Part 1:
  
  a) Determines if the element_looking_for is found in the list passed in.
   If yes returns true, else returns false.
*)
fun exists (element_looking_for, []) = false 
   | exists (element_looking_for, (cur_element::rest_of_list)) = 
   if element_looking_for = cur_element then true 
   else (exists (element_looking_for, rest_of_list));
(* ================================================================*)

(* Part 1 b. (''a * ''a list) -> bool is the right type because there needs to be a comparison made. Which means it needs to be ''a.*)
(* ================================================================*)

(*
   Part 1:
   
   c) Counts the number of times th element_looking_for is found within the list
   Returns zero if element_looking_for is never within the list, else returns the number of instances.
*)
fun countInList [] element_looking_for = 0
   | countInList (cur_element::rest_of_list) element_looking_for =
   if element_looking_for = cur_element 
      then 1 + (countInList rest_of_list element_looking_for)
   else (countInList rest_of_list element_looking_for);      
(* ==============================================================*)

(*
   Part 2:
      Function determines the different elements in one list, as supposed to another list entered in.
      Returns the different elements in the first list.
*)
fun listDiff ([], compareList) = []
   | listDiff (compareElem::compareList, elemList) = 
   let
      (* checks the difference of the two list *)
      fun checkValue(element_one, element_two) =
         if element_one > element_two then element_one - element_two
         else 0
      
      (* checks at the end of list *)
      fun atEnd(elem, []) = []
         | atEnd(elem, compareElem::listOfElem) =
         if elem = compareElem
            then compareElem::atEnd(elem, listOfElem)
         else compareElem::atEnd(elem, listOfElem)
            
      (* delete an element from a list *)
      fun deleteElement(elem, []) = []
         | deleteElement(elem, compareElem::listOfElem) = 
         if elem = compareElem
            then atEnd(elem, listOfElem)
         else compareElem::deleteElement(elem, listOfElem)

   in
      if checkValue((countInList(compareElem::compareList) compareElem), (countInList elemList compareElem)) = 0
         then listDiff (compareList, deleteElement(compareElem, elemList))
      else compareElem::listDiff(compareList,elemList) 
   end;
(* ==============================================================*)

(*
   Part 3:
      Function determines the first number_of_places elements.
      Returns the first number_of_places elements.
*)
fun firstN [] number_of_places = []
   | firstN (cur_element::rest_of_list) number_of_places =
   if number_of_places = 0 
      then (firstN rest_of_list number_of_places)
   else (cur_element::firstN rest_of_list (number_of_places -1));
(* ==============================================================*)

(* 
   Part 4:
*)
(* 
   Example value for testing a function
*)
val buses = [
("Lentil",["Chinook", "Orchard", "Valley", "Emerald","Providence",
"Stadium", "Main", "Arbor", "Sunnyside", "Fountain", "Crestview",
"Wheatland", "Walmart", "Bishop", "Derby", "Dilke"]),
("Wheat",["Chinook", "Orchard", "Valley", "Maple","Aspen",
"TerreView", "Clay", "Dismores", "Martin", "Bishop", "Walmart",
"PorchLight", "Campus"]),
("Silver",["TransferStation", "PorchLight", "Stadium",
"Bishop","Walmart", "Shopco", "RockeyWay"]),
("Blue",["TransferStation", "State", "Larry", "TerreView","Grand",
"TacoBell", "Chinook", "Library"]),
("Gray",["TransferStation", "Wawawai", "Main",
"Sunnyside","Crestview", "CityHall", "Stadium", "Colorado"])
]

(*
   This function looks for a desired_stop within the list of stops.
   Returns a list of current_routes that have that desired_stop on it.
*)
fun busFinder desired_stop [] = []
   | busFinder desired_stop ((current_route,stops)::route_list) =
   if exists(desired_stop, stops) 
      then (current_route::busFinder desired_stop route_list)
   else (busFinder desired_stop route_list);
(* ==============================================================*)

(*
   Part 4:

   b) Because the name of the bus stop is never compared to anything or rather element 'a' therefore it has a diff name
*)

(*
   Part 5:
   
   Calculates resistance.
*)
fun parallelResistors [] = 0.0
   | parallelResistors resistors = 
   let
      fun helper [] = 0.0
         | helper (cur::total) =
         helper(total) + 1.0 /cur
   in
      1.0 / (helper resistors)
   end
(* ==============================================================*)

(*
   Part 6

   a) Pairs everything left
*)
fun pairNleft (num, []) = []
   | pairNleft (num, rest) = 
   let
      fun itterate(num, []) = []
         | itterate(num, (cur::rest)) = 
         if num = 0
            then cur::rest
         else itterate((num-1), rest);
   in
      if (length(rest) mod num) = 0
         then (firstN rest num)::pairNleft(num, itterate(num, rest))
      else (firstN rest (length(rest) mod num))::pairNleft(num,itterate((length(rest) mod num), rest))
   end
(* ==============================================================*)

(*
   b) Pairs everything right
*)
fun pairNright (num, []) = []
   | pairNright (num, rest) =
   let
      fun itterate(num, []) = []
         | itterate(num, (elem::rest)) = 
         if num = 0
            then elem::rest
         else itterate((num-1),rest)
   in
      if (length(rest)) >= num
         then (firstN rest num)::pairNright(num,itterate(num,rest))
      else (firstN rest num)::pairNright(num, [])
   end
(* ==============================================================*)



(*All test cases and helper functions are here inside the let block*)
(*Part 1a Test*)
fun existsTest ()=
	let
		val existsT1 = exists(1,[]) = false
		val existsT2 = exists(1,[1,2,3]) = true
		val existsT3 = exists([1],[[1]]) = true
		val existsT4 = exists([1],[[3],[5]]) = false
		val existsT5 = exists("c",["b","c","z"]) = true
		val existsT6 = exists(56,[36,78,91,96,90,12,46,56]) = true
		val existsT7 = exists(["A"],[["3"],["0"],["i"],["hel"],["K"],["hel"],["a"],["U"]]) = false
		val existsT8 = exists([36],[[35],[78],[91],[34],[24],[1],[0]]) = false
		val existsT9 = exists("49",["4","3","9","23","7"]) = false
		val existsT10 = exists("3",["2","1","0"]) = false
	in
		print ("----------testing exists----------------- \n"   ^
            "   test1: " ^ Bool.toString(existsT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(existsT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(existsT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(existsT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(existsT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(existsT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(existsT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(existsT8) ^ "\n" ^
			"   test9: " ^ Bool.toString(existsT9) ^ "\n" ^
            "   test10: " ^ Bool.toString(existsT10) ^ "\n")
	end;

val _ =existsTest();

(*Part 1c Test*)
fun countInListTest ()=
	let
		val countInListT1 = countInList ["3","5","5","-","4","5","1"] "5" = 3
		val countInListT2 = countInList [] "" = 0
		val countInListT3 = countInList [true, false, false, false, true, true, true] true = 4
		val countInListT4 = countInList  [[],[1,2],[3,2],[5,6,7],[8],[]] [] = 2
		val countInListT5 = countInList ["c","c","z"] "c" = 2
		val countInListT6 = countInList [36,56,91,89,90,56,46,56] 56  = 3
		val countInListT7 = countInList [["g"],["h"],["I"],["s"],["K"],["A"],["i"],["U"]] ["a"] = 0
		val countInListT8 = countInList [[3],[3],[3],[34],[3],[3],[3]] [3] = 6
	in
		print ("--------testing countInList------------------ \n"   ^
            "   test1: " ^ Bool.toString(countInListT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(countInListT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(countInListT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(countInListT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(countInListT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(countInListT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(countInListT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(countInListT8) ^ "\n")
	end;

val _ =countInListTest();

(*Part 2 Test*)
fun listDiffTest ()=
	let
		val listDiffT1 = listDiff(["a","b","c"],["b"]) = ["a", "c"]
		val listDiffT2 = listDiff([1,2,3],[1,1,2]) = [3]
		val listDiffT3 = listDiff([1,2,2,3,3,3],[1,1,2,3]) = [2,3,3]
		val listDiffT4 = listDiff([[2,3],[1,2],[2,3]],[[1],[2,3]]) = [[2,3],[1,2]]
		val listDiffT5 = listDiff ([1,2,3],[]) = [1,2,3]
		val listDiffT6 = listDiff([],[1,2,3,4,5,6,7]) = []
		val listDiffT7 = listDiff(["a","b","a","b","a","b"],["a","a","a"]) = ["b","b","b"]
		val listDiffT8 = listDiff(["a"],["a"]) = []
		val listDiffT9 = listDiff([],["a"]) = []
	in
		print ("--------testing listDiff-------------- \n"   ^
            "   test1: " ^ Bool.toString(listDiffT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(listDiffT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(listDiffT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(listDiffT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(listDiffT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(listDiffT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(listDiffT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(listDiffT8) ^ "\n" ^
			"   test8: " ^ Bool.toString(listDiffT8) ^ "\n")
	end;

val _ =listDiffTest();

(*Part 3 Test*)
fun firstNTest ()=
	let
		val firstNT1 = firstN ["a", "b", "c", "x", "y"] 3 = ["a", "b", "c"]
		val firstNT2 = firstN [1,2,3,4,5,6,7] 4 = [1,2,3,4]
		val firstNT3 = firstN [1,2,3,4,5,6,7] 10 = [1,2,3,4,5,6,7]
		val firstNT4 = firstN [[1,2,3],[4,5],[6],[],[7,8],[]] 4 = [[1,2,3],[4,5],[6],[]]
		val firstNT5 = firstN [] 5 = []
		val firstNT6 = firstN [5,6,7,8,9] 0 = []
		val firstNT7 = firstN ["h","e","l","l","o","!"] 3 = ["h","e","l"]
		val firstNT8 = firstN ["yes"] 1 = ["yes"]
	in
		print ("----------testing firstN---------------- \n"   ^
            "   test1: " ^ Bool.toString(firstNT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(firstNT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(firstNT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(firstNT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(firstNT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(firstNT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(firstNT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(firstNT8) ^ "\n")
	end;

val _ =firstNTest();

(*Part 4 Test*)
fun busFinderTest ()=
	let
		val busFinderT1 = busFinder "Walmart" buses = ["Lentil","Wheat","Silver"]
		val busFinderT2 = busFinder "Shopco" buses = ["Silver"]
		val busFinderT3 = busFinder "Main" buses = ["Lentil","Gray"]
		val busFinderT4 = busFinder "Beasley" buses = []
		val busFinderT5 = busFinder "Moscow" buses = []
		val busFinderT6 = busFinder "Chinook" buses = ["Lentil","Wheat","Blue"]
		val busFinderT7 = busFinder "Wawawai" buses = ["Gray"]
	in
		print ("-----------testing busFinder------------- \n"   ^
            "   test1: " ^ Bool.toString(busFinderT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(busFinderT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(busFinderT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(busFinderT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(busFinderT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(busFinderT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(busFinderT7) ^ "\n")
	end;

val _ =busFinderTest();

(*Part 5 Test*)
fun parallelResistorsTest ()=
	let
		val parallelResistorsT1 = Real.==((parallelResistors [10.0, 10.0, 10.0, 10.0]), 2.5)
		val parallelResistorsT2 = Real.==((parallelResistors [8.0, 16.0, 4.0, 16.0]), 2.0)
        val parallelResistorsT3 = Real.==((parallelResistors [5.0, 10.0, 2.0]) , 1.25)
		val parallelResistorsT4 = Real.==((parallelResistors [1.0, 1.0, 1.0, 1.0]), 0.25)
		val parallelResistorsT5 = Real.==((parallelResistors [1.0]), 1.0)
		val parallelResistorsT6 = Real.==((parallelResistors [0.0]), 0.0)
		val parallelResistorsT7 = Real.==((parallelResistors []), 0.0)
	in
		print ("--------------testing parallelResistors---------------- \n"   ^
            "   test1: " ^ Bool.toString(parallelResistorsT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(parallelResistorsT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(parallelResistorsT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(parallelResistorsT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(parallelResistorsT5) ^ "\n" ^
			"   test7: " ^ Bool.toString(parallelResistorsT6) ^ "\n" ^
			"   test6: " ^ Bool.toString(parallelResistorsT6) ^ "\n")
	end;

val _ =parallelResistorsTest();

(*Part 6 Test*)
fun pairNTest ()=
	let
		val pairNT1 = pairNleft(4,[2, 3, 4, 5]) = [[2,3,4,5]]
		val pairNT2 = pairNright(4,[2, 3, 4, 5]) = [[2,3,4,5]] 
		val pairNT3 = pairNleft(3,[1, 2, 3, 4, 5]) = [[1, 2], [3, 4, 5]]
		val pairNT4 = pairNright(3,[1, 2, 3, 4, 5]) = [[1, 2, 3], [4, 5]]
		val pairNT5 = pairNright(3,[1,4,2,6,7,3,7,1,4,5,3]) = [[1,4,2],[6,7,3],[7,1,4],[5,3]] 
		val pairNT6 = pairNleft(3,[1,4,2,6,7,3,7,1,4,5,3]) = [[1,4],[2,6,7],[3,7,1],[4,5,3]]
		val pairNT7 = pairNright(2,[1, 2, 3, 4, 5, 6]) = [[1, 2], [3, 4], [5, 6]]
		val pairNT8 = pairNleft (2,[1, 2, 3, 4, 5, 6]) = [[1, 2], [3, 4], [5, 6]]
	in
		print ("------------testing pairN----------------- \n"   ^
            "   test1: " ^ Bool.toString(pairNT1) ^ "\n" ^
            "   test2: " ^ Bool.toString(pairNT2) ^ "\n" ^
			"   test3: " ^ Bool.toString(pairNT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(pairNT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(pairNT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(pairNT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(pairNT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(pairNT8) ^ "\n")
	end;

val _ =pairNTest();
