type 'a tree = Empty | Node of 'a tree * 'a * 'a tree
type elt

module S = Set.Make(struct type t = elt let compare = compare end)
open S

let h = ref empty

(*@ function set_of_tree 
		(t: 'a tree) (s: 'a fset) : 'a fset =
	match t with
	| Empty -> s
	| Node l x r ->
			let s1 = set_of_tree l (add x s) in
			set_of_tree r s1 *)

(*@ function n_distinct (t : elt tree) =
	cardinal (set_of_tree t empty)*)

  let rec distinct_elements_loop 
    (t : elt tree) (k : unit -> unit) : unit =
    match t with
    | Empty -> k ()
    | Node(l, x, r) ->
        h := S.add x (!h);
        distinct_elements_loop l
        (fun (*@ ensures post k () (add_tree (old !h) r) !h () *)
						()-> distinct_elements_loop r k)
(*@ ensures post k () (add_tree (old !h) t) !h () *)
let distinct_elements (t : elt tree) : int =
    h := empty;
    distinct_elements_loop t (fun x -> x);
    cardinal !h
(*@ ensures result = n_distinct t *)