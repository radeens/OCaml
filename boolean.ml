(* OCaml Boolean Formulae & SAT *)

(* To load this file into the OCaml interpreter, type

   #use "boolean.ml"

   at the OCaml prompt
*)

type formula =
    False
  | True
  | Var of char
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | Forall of char * formula
  | Exists of char * formula

type assignment = (char * bool) list

type vec = formula list

(*----------------------------------------------------------
  function f_to_str : formula -> string. 

	converts formula into a string 
*)

let rec f_to_str f = match f with
    False -> "F"
  | True -> "T"
  | Var x -> Char.escaped x
  | And (f1,f2) -> "(" ^ (f_to_str f1) ^ " && " ^ (f_to_str f2) ^ ")"
  | Or (f1,f2) -> "(" ^ (f_to_str f1) ^ " || " ^ (f_to_str f2) ^ ")"
  | Not f1 -> "(! " ^ (f_to_str f1) ^ ")"
  | Forall (x,f1) -> "(forall " ^ (Char.escaped x) ^ " : " ^ (f_to_str f1) ^ ")"
  | Exists (x,f1) -> "(exists " ^ (Char.escaped x) ^ " : " ^ (f_to_str f1) ^ ")"
;;

(*----------------------------------------------------------
  map & fold
*)
 
let rec map f lst = match lst with
  [] -> []
  | h::t -> (f h)::(map f t)
;;
 
let rec fold f a lst = match lst with
  [] -> a
  | h::t -> fold f (f a h) t
;;
 
let reverse lst = fold (fun a h -> (h::a)) [] lst
;;
 

(*  YOUR CODE PAST THIS POINT *)


(*----------------------------------------------------------
  function count_assoc : assignment char -> int. 

	Counts the number of times an association appears 
	for some symbol x in the assignment. 

	count_assoc [('a',true);('a',false)] 'a' returns 2.
*)
let rec count_assoc_help lst x = match lst with
	[] -> 0
	| h::t -> if (fst h = x) then (1 + (count_assoc_help t x)) else count_assoc_help t x
;;

let count_assoc lst x = count_assoc_help lst x;;

(*----------------------------------------------------------
  function remove_assoc_all: assignment char -> assignment. 

	Removes all associations for some symbol x in the assignment. 

	remove_assoc_all [('a',true);('b',true);('a',false)] 'a'
	returns [('b',true)].
*)
let rec remove_assoc_help lst x = match lst with
	[] -> []
	| h::t -> if (fst h = x) then remove_assoc_help t x else h::(remove_assoc_help t x)
	
;;

let remove_assoc_all lst x = remove_assoc_help lst x
;;

(*----------------------------------------------------------
  function change_assoc_all: assignment char bool -> assignment. 

	Changes all associations for some symbol x in the 
	assignment to the specified boolean value. 

	change_assoc_all [('a',true);('a',false)] 'a' true
	returns [('a',true);('a',true)].
*)
let rec change_assoc_all_help lst x y = match lst with
	[] -> []
	| h::t -> if (fst h <> x) then h::(change_assoc_all_help t x y) else ((fst h), y)::(change_assoc_all_help t x y)
;;

let change_assoc_all lst x y = change_assoc_all_help lst x y
;;

(*----------------------------------------------------------
  function assoc_last: assignment char -> bool. 

	Returns the value bound to the last association 
	for some symbol x in the assignment. 

	assoc_last [('a',true);('a',false)] 'a' returns false. 
*)
let rec assoc_last_help lst x = match lst with
	[] -> false
	| h::t -> if (fst h = x) then (snd h) else assoc_last_help t x

let assoc_last lst x= 
	let l = reverse lst in assoc_last_help l x
;;

(*----------------------------------------------------------
  function create_assoc : char list -> bool -> assignment
 
        creates assignment (to bool) for all chars in list using map
 
  function create_assoc_help : bool -> char -> (char * bool)
 
        helper function for create_assoc

	Takes a boolean argument, and returns a function that takes 
	a char (from a char list) and returns a (char * bool) 
	association that can be added to an assignment.
*)
 
 
let create_assoc_help v = fun h -> (h, v) ;;
 
let create_assoc lst v = (map (create_assoc_help v) lst) ;;
 
(*----------------------------------------------------------
  function find_assoc : assignment -> bool -> assignment
 
        return all assignments with bool value
 
  function find_assoc_help : bool -> assignment -> (char * bool) -> assignment
 
        helper function for find_assoc
 
	Takes a boolean argument, and returns a function that given 
	an assignment and a (char * bool) association, adds the 
	association to the assignment if appropriate.
*)
 
 
let find_assoc_help v = 
	fun a h -> if (snd h = v) then  h::a else a;;
 
let find_assoc lst v = reverse (fold (find_assoc_help v) [] lst) ;;

(*----------------------------------------------------------
  function eval : formula -> assignment -> bool. 

	evaluates the boolean formula on the given variable assignment 
	returns the result as an OCaml bool. 
*)

let rec eval f e = match f with 
    False -> false
  | True -> true
  | Var x -> (match e with 
			[] -> false
			|h::t -> if (fst h = x) then snd h else eval f t)
  | And (f1,f2) -> (eval f1 e) && (eval f2 e)
  | Or (f1,f2) -> eval f1 e || eval f2 e
  | Not f1 -> if eval f1 e = false then true else true
  | Forall (x,f1) -> eval f1((x, true)::e) && eval f1((x, false)::e)
  | Exists (x,f1) -> eval f1((x, true)::e) || eval f1((x, false)::e)  
;;

(*----------------------------------------------------------
  function vars_of : formula -> char list. 

	takes a formula and returns a list of the names of the 
	free variables of the formula. 
*)
let rec extract f x a = match a with
		False -> x
	| True -> x
	| Var y -> if (List.mem y f) then [] else [y]
	| And (f1,f2) -> (extract f x f1)@(extract f x f2)
	| Or (f1, f2) -> (extract f x f1)@(extract f x f2)
	| Not f1 -> extract f x f1
	| Forall (y,f1) -> extract (y::f) x f1
	| Exists (y,f1) -> extract (y::f) x f1 
;;

let rec get e n = match e with 
	[] -> n
	| h::t -> if not(List.mem h n) then get t (h::n) else get t n
;;

let vars_of x = 
	let f = (extract [] [] x) in get f []
;;

(*----------------------------------------------------------
  function sat : formula -> assignment option. 

	function returns Some a, where a is a satisfying assignment, 
	if the formula is satisfiable, or None otherwise. 
*)

let rec get_second c list = 
	if c = 0 then List.rev list
	else get_second (c/2) ((if (c mod 2) <> 1 then false else true)::list)
;;

let rec get_first list1 list2 list = 
		if List.length list2 < list then match list1 with
			[] -> get_first list1 (false::list2) list
			| h::t -> get_first t (h::list2) list
		else List.rev list2
;;

let rec sat_help x y c = 
		if (List.length y == 0) && (eval x []) then Some []
		else if (List.length y == 0) && (not(eval x [])) then None
		else if (c > ((List.length y) * (List.length y))) then None
		else 
			let result = List.combine y (get_first (get_second c []) [] (List.length y)) in
				if (eval x result) then Some result
				else sat_help x y (c+1)
;;

let sat x = 
	 let y = vars_of x in sat_help x y 0
;;

(*----------------------------------------------------------
  function int_of_vec : vec -> int. 

	takes a vec composed solely of Trues and Falses 
	returns the integer equivalent.
	
*)
let rec pow a = match a with
  	0 -> 1
  | 1 -> a
  | n -> 2 * pow (n-1)
;;

let rec int_of_help x c = match x with
	 [] -> 0
	|h::t -> if h = True then (pow c + int_of_help t (c+1)) 
					 else int_of_help t (c+1) 
;;

let int_of_vec x = 
	let i = 1 in int_of_help x i
;;

(*----------------------------------------------------------
  function vec_of_int : int -> vec. 

	takes a non-negative integer 
	returns the corresponding vec. 
*)

let rec vec_of_help x list = 
	if x = 0 then reverse list
	else vec_of_help (x/2) ((if (x mod 2) = 1 then True else False)::list)
;;

let vec_of_int x = 
	vec_of_help x []
;;

(*----------------------------------------------------------
  function subst : assignment -> vec -> vec. 

	reduces the vec argument to a vec of all Trues and Falses 
	by replacing the variables in the vec according to the 
	assignment and then evaluating each bit. 
*)
let rec subst_help a v = match v with 
	[] -> []
	| h::t -> (if eval h a = true then True::(subst_help a t)
						else False::(subst_help a t))
;;

let subst x y = 
	subst_help x y
;;

(*----------------------------------------------------------
  function eq : vec -> vec -> formula. 

	returns a formula representing whether the two bit vectors are equal. 
*)
let eq_help_help list1 list2 =
		Or(And(list1, list2), And(Not(list1), Not(list2)))	
;;

let rec eq_help vec1 vec2 = match vec1 with
	[] -> False
	| [y] -> eq_help_help y (List.hd vec2)
	| h::t -> (match vec2 with 
			[] -> False
			| h1::t1 -> And ((eq_help_help h h1), eq_help t t1))
;;
let eq x y =
	eq_help x y
;;

(*----------------------------------------------------------
  function add : vec -> vec -> vec. 

	returns a new vec representing the sum of the two vectors. 
*)
let not_both x y =
	(Or(And(x, Not(y)), And(Not(x), y)))
;;
let add_full x y z = 
		((not_both (not_both x y) z), (Or(And(x,y), And(z, not_both x y))))
;;

let rec add_help x y bool = match  x with
	[] -> [bool]
	| h::t -> (match add_full h (List.hd y) bool with
					 (a, b) -> match y with 
							 [] -> [bool]
							| h1::t1 -> a::add_help t t1 b)
;;
let add x y = add_help x y False
;;

(*----------------------------------------------------------
  function pad : vec -> int -> vec. 

	pad v i returns a new vec that is equal to v 
	but whose length is the greater of i and the length of v. 
*)
let rec pad_help d =
	if d = 0 then []
	else False::(pad_help (d-1))
;;

let pad x y =
	if y <= (List.length x) then x
	else List.append x (pad_help(y-(List.length x)))
;;

(*----------------------------------------------------------
  function add_three : vec -> vec -> vec -> vec. 

	returns a new vector that represents the sum of 
	the three input vectors. 
*)

let add_three x y z =
	(add (add x y) (pad z (List.length (add x y))))
;;

(*----------------------------------------------------------
  function is_digit : vec -> formula. 

	input is a vec of length 4 (i.e., exactly 4 boolean formulae). 

	returns a formula that is true if and only if the vec is 
	greater than or equal to 1 and less than or equal to 9.
*)
let rec is_digit_help x c = 
	if c = 9 then eq x (pad (vec_of_int c) 4)
	else (Or(eq x (pad (vec_of_int c) 4), (is_digit_help x (c+1))))
;;


let is_digit x =
	is_digit_help x 1
;;

(*----------------------------------------------------------
  function disjoint : vec list -> formula. 

	takes a list of vecs and returns a formula representing whether 
	all the vecs are different from each other.
*)
let rec is_dis_help1 x y = match y with
	[] -> False
	|[z] -> Not(eq x z)
	| h::t -> And(Not(eq x h),is_dis_help1 x t)
;;

let rec is_dis_help x y = match x with 
	[] -> False
	|[z] -> True
	| h::t -> (match y with 
			[] -> False
			| h1::t1 -> And(is_dis_help1 h t1, is_dis_help t  t1))
;;

let disjoint x =
	is_dis_help x x	
;;

(*----------------------------------------------------------
  function is_magic : vec list -> formula. 

	takes a list of exactly nine vecs and returns a formula 
	representing whether the list is a magic square. 
	c1 c2 c3
	c4 c5 c6
	c7 c8 c9
*)
let look_aux r1 r2 r3 r4 r5 r6 r7 r8 = 
	And((eq r1 r2),And((eq r2 r3),And((eq r3 r4),And((eq r4 r5),And((eq r5 r6),And((eq r6 r7),(eq r7 r8)))))))
;;
let look x = match x with
 	[] -> x 
	|[c1;c2;c3;c4;c5;c6;c7;c8;c9] -> 
		let r1 = add_three c1 c2 c3 in   
			let r2 = add_three c1 c4 c7 in  
				let r3 = add_three c7 c8 c9 in
					let r4 = add_three c3 c6 c9 in
						let r5 = add_three c1 c5 c9 in
							let r6 = add_three c3 c5 c7 in
					 			let r7 = add_three c2 c5 c6 in
									let r8 = add_three c4 c5 c6 in
										look_aux r1 r2 r3 r4 r5 r6 r7 r8
					 
;;
let rec is_d x bool = match x with
	[] -> bool
	| h::t -> is_d t (And(bool, is_digit h))
;;
let is_magic x =
	And(is_d x True, And(disjoint x, look x))
;;
