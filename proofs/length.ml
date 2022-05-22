let rec length_cps_aux l  (k : int -> 'a) : 'a =
match l with
|[] -> k 0
|x::t -> length_cps_aux t 
  (fun (*@ ensures post k (r + 1) result *)
        r -> k (r + 1))
(*@ ensures post k (length l) result*)


let length (l : 'a list) : int =
  length_cps_aux l (fun x -> x)
(*@ ensures result = length l*)
