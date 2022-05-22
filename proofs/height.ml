type 'a tree = Empty | Node of 'a tree * 'a *'a tree  

let rec height_tree
(t: 'a tree) (k: int -> 'b) : 'b
= match t with
| Empty -> k 0
| Node(lt, _, rt) ->
  height_tree lt (fun (*@ ensures post k (1 + max hl (height rt)) result *)
    hl ->height_tree rt (fun   (*@ ensures post k(1 + max hl hr) result *)
    hr -> k (1 + max hl hr)))
(*@ ensures post k (height t) result *)
    


let height_tree_cps (t: 'a tree): int =
  height_tree t (fun x -> x)
(*@ r = height_tree t
      ensures (height t) = r*)