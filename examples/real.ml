(* Interactive examples from real.ml, lifted out of the source.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

real_qelim {%fol|exists x. x^4 + x^2 + 1 = 0|};;

real_qelim {%fol|exists x. x^3 - x^2 + x - 1 = 0|};;

real_qelim {%fol|exists x y. x^3 - x^2 + x - 1 = 0 /\
                         y^3 - y^2 + y - 1 = 0 /\ ~(x = y)|};;

#trace testform;;
real_qelim {%fol|exists x. x^2 - 3 * x + 2 = 0 /\ 2 * x - 3 = 0|};;
#untrace testform;;

real_qelim
 {%fol|forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k|};;

real_qelim {%fol|exists x. a * x^2 + b * x + c = 0|};;

real_qelim {%fol|forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           b^2 >= 4 * a * c|};;

real_qelim {%fol|forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           a = 0 /\ (b = 0 ==> c = 0) \/
                           ~(a = 0) /\ b^2 >= 4 * a * c|};;

(* ------------------------------------------------------------------------- *)
(* Termination ordering for group theory completion.                         *)
(* ------------------------------------------------------------------------- *)

real_qelim {%fol|1 < 2 /\ (forall x. 1 < x ==> 1 < x^2) /\
             (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))|};;

(* ---- *)

let eqs = complete_and_simplify ["1"; "*"; "i"]
  [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

let fm = list_conj (map grpform eqs);;

real_qelim fm;;

(* ---- *)

let rec casesplit vars dun pols cont sgns =
  match pols with
    [] -> monicize vars dun cont sgns
  | p::ops -> split_trichotomy sgns (head vars p)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars dun (behead vars p :: ops) cont)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars (dun@[p]) ops cont)

and delconst vars dun p ops cont sgns =
  let cont' m = cont(map (insertat (length dun) (findsign sgns p)) m) in
  casesplit vars dun ops cont' sgns

and matrix vars pols cont sgns =
  if pols = [] then try cont [[]] with Failure _ -> False else
  let p = hd(sort(decreasing (degree vars)) pols) in
  let p' = poly_diff vars p and i = index p pols in
  let qs = let p1,p2 = chop_list i pols in p'::p1 @ tl p2 in
  let gs = map (pdivide_pos vars sgns p) qs in
  let cont' m = cont(map (fun l -> insertat i (hd l) (tl l)) m) in
  casesplit vars [] (qs@gs) (dedmatrix cont') sgns

and monicize vars pols cont sgns =
  let mols,swaps = unzip(map monic pols) in
  let sols = setify mols in
  let indices = map (fun p -> index p sols) mols in
  let transform m =
    map2 (fun sw i -> swap sw (el i m)) swaps indices in
  let cont' mat = cont(map transform mat) in
  matrix vars sols cont' sgns;;

let basic_real_qelim vars (Exists(x,p)) =
  let pols = atom_union
    (function (R(a,[t;Fn("0",[])])) -> [t] | _ -> []) p in
  let cont mat = if exists (fun m -> testform (zip pols m) p) mat
                 then True else False in
  casesplit (x::vars) [] pols cont init_sgns;;

let real_qelim =
  simplify ** evalc **
  lift_qelim polyatom (simplify ** evalc) basic_real_qelim;;

let real_qelim' =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
                      basic_real_qelim;;
