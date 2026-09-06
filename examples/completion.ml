(* Interactive examples from completion.ml, lifted out of the source by
   tools/migrate_to_modules.py.  Not compiled: these are meant to be
   pasted into a toplevel that has opened Atp.All. *)

let eq = {%fol|f(f(x)) = g(x)|} in critical_pairs eq eq;;

(* ---- *)

let eqs =
  [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

let ord = lpo_ge (weight ["1"; "*"; "i"]);;

let eqs' = complete ord
  (eqs,[],unions(allpairs critical_pairs eqs eqs));;

rewrite eqs' {%tm|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))|};;

(* ---- *)

interreduce [] eqs';;

(* ---- *)

complete_and_simplify ["1"; "*"; "i"]
  [{%fol|i(a) * (a * b) = b|}];;

(* ------------------------------------------------------------------------- *)
(* Auxiliary result used to justify extension of language for cancellation.  *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 {%fol|(forall x y z. x * y = x * z ==> y = z) <=>
   (forall x z. exists w. forall y. z = x * y ==> w = y)|};;

skolemize {%fol|forall x z. exists w. forall y. z = x * y ==> w = y|};;

(* ---- *)

let eqs =  [{%fol|(a * b) * (b * c) = b|}];;

complete_and_simplify ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* (l,r)-systems (K&B example 12).                                           *)
(* ------------------------------------------------------------------------- *)

(******** This works, but takes a long time

let eqs =
 [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|x * i(x) = 1|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* Auxiliary result used to justify extension for example 9.                 *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 {%fol|(forall x y z. x * y = x * z ==> y = z) <=>
   (forall x z. exists w. forall y. z = x * y ==> w = y)|};;

skolemize {%fol|forall x z. exists w. forall y. z = x * y ==> w = y|};;

let eqs =
  [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* K&B example 7, where we need to divide through.                           *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}];;

(*********** Can't orient

complete_and_simplify ["f"] eqs;;

*************)

let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}; {%fol|f(a,b,c) = g(a,b)|};
                     {%fol|g(a,b) = h(b)|}];;

complete_and_simplify ["h"; "g"; "f"] eqs;;


(* ------------------------------------------------------------------------- *)
(* Other examples not in the book, mostly from K&B                           *)
(* ------------------------------------------------------------------------- *)

(************

(* ------------------------------------------------------------------------- *)
(* Group theory I (K & B example 1).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* However, with the rules in a different order, things take longer.         *)
(* At least we don't need to defer any critical pairs...                     *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|i(x) * x = 1|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Example 2: if we orient i(x) * i(y) -> i(x * y), things diverge.          *)
(* ------------------------------------------------------------------------- *)

(**************

let eqs =
 [{%fol|1 * x = x|}; {%fol|i(x) * x = 1|}; {%fol|(x * y) * z = x * y * z|}];;

complete_and_simplify ["1"; "i"; "*"] eqs;;
 *************)

(* ------------------------------------------------------------------------- *)
(* Group theory III, with right inverse and identity (K&B example 3).        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * y * z|}; {%fol|x * 1 = x|}; {%fol|x * i(x) = 1|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|i(a) * (a * b) = b|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

let eqs =  [{%fol|a * (i(a) * b) = b|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Group theory IV (K&B example 5).                                          *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * x = x|}; {%fol|11 * x = x|};
  {%fol|i(x) * x = 1|}; {%fol|j(x) * x = 11|}];;

complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|(a * b) * (b * c) = b|}];;

complete_and_simplify ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Random axiom (K&B example 7).                                             *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}];;

(*********** Can't orient

complete_and_simplify ["f"] eqs;;

*************)

let eqs =  [{%fol|f(a,f(b,c,a),d) = c|}; {%fol|f(a,b,c) = g(a,b)|};
                     {%fol|g(a,b) = h(b)|}];;

complete_and_simplify ["h"; "g"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Another random axiom (K&B example 8).                                     *)
(* ------------------------------------------------------------------------- *)

(************* Can't orient

let eqs =  [{%fol|(a * b) * (c * b * a) = b|}];;

complete_and_simplify ["*"] eqs;;

 *************)

(* ------------------------------------------------------------------------- *)
(* The cancellation law (K&B example 9).                                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

complete_and_simplify ["*"; "f"; "g"] eqs;;

let eqs =
  [{%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(**** Just for fun; these aren't tried by Knuth and Bendix

let eqs =
  [{%fol|(x * y) * z = x * y * z|};
   {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

let eqs =
  [{%fol|(x * y) * z = x * y * z|};
   {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

complete_and_simplify ["*"; "f"; "g"] eqs;;

complete_and_simplify ["f"; "g"; "*"] eqs;;

*********)

(* ------------------------------------------------------------------------- *)
(* Loops (K&B example 10).                                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|a * \(a,b) = b|}; {%fol|/(a,b) * b = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|}];;

complete_and_simplify ["1"; "*"; "\\"; "/"] eqs;;

let eqs =
 [{%fol|a * \(a,b) = b|}; {%fol|/(a,b) * b = a|}; {%fol|1 * a = a|}; {%fol|a * 1 = a|};
  {%fol|f(a,a*b) = b|}; {%fol|g(a*b,b) = a|}];;

complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Another variant of groups (K&B example 11).                               *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * 1 = 1|};
  {%fol|a * i(a) = 1|};
  {%fol|f(1,a,b) = a|};
  {%fol|f(a*b,a,b) = g(a*b,b)|}];;

(******** this is not expected to terminate

complete_and_simplify ["1"; "g"; "f"; "*"; "i"] eqs;;

**************)

(* ------------------------------------------------------------------------- *)
(* (l,r)-systems (K&B example 12).                                           *)
(* ------------------------------------------------------------------------- *)

(******** This works, but takes a long time

let eqs =
 [{%fol|(x * y) * z = x * y * z|}; {%fol|1 * x = x|}; {%fol|x * i(x) = 1|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* (r,l)-systems (K&B example 13).                                           *)
(* ------------------------------------------------------------------------- *)

(**** Note that here the simple LPO approach works, whereas K&B need
 **** some additional hacks.
 ****)

let eqs =
 [{%fol|(x * y) * z = x * y * z|}; {%fol|x * 1 = x|}; {%fol|i(x) * x = 1|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* (l,r) systems II (K&B example 14).                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * x = x|}; {%fol|11 * x = x|};
  {%fol|x * i(x) = 1|}; {%fol|x * j(x) = 11|}];;

(******** This seems to be too slow. K&B encounter a similar problem

complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

 ********)

(* ------------------------------------------------------------------------- *)
(* (l,r) systems III (K&B example 15).                                       *)
(* ------------------------------------------------------------------------- *)

(********** According to KB, this wouldn't be expected to work

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * x = x|};
  {%fol|prime(a) * a = star(a)|};
  {%fol|star(a) * b = b|}];;

complete_and_simplify ["1"; "*"; "star"; "prime"] eqs;;

 ************)

(*********** These seem too slow too. Maybe just a bad ordering?

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * x = x|};
  {%fol|hash(a) * dollar(a) * a = star(a)|};
  {%fol|star(a) * b = b|};
  {%fol|a * hash(a) = 1|};
  {%fol|a * 1 = hash(hash(a))|};
  {%fol|hash(hash(hash(a))) = hash(a)|}];;

complete_and_simplify ["1"; "hash"; "star"; "*"; "dollar"] eqs;;

let eqs =
 [{%fol|(x * y) * z = x * y * z|};
  {%fol|1 * x = x|};
  {%fol|hash(a) * dollar(a) * a = star(a)|};
  {%fol|star(a) * b = b|};
  {%fol|a * hash(a) = 1|};
  {%fol|hash(hash(a)) = a * 1|};
  {%fol|hash(hash(hash(a))) = hash(a)|}];;

complete_and_simplify ["1"; "star"; "*"; "hash"; "dollar"] eqs;;

***********)

(* ------------------------------------------------------------------------- *)
(* Central groupoids II. (K&B example 16).                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|(a * a) * a = one(a)|};
  {%fol|a * (a * a) = two(a)|};
  {%fol|(a * b) * (b * c) = b|};
  {%fol|two(a) * b = a * b|}];;

complete_and_simplify ["one"; "two"; "*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Central groupoids II. (K&B example 17).                                   *)
(* ------------------------------------------------------------------------- *)

(******** Not ordered right...

let eqs =
 [{%fol|(a*a * a) = one(a)|};
  {%fol|(a * a*a) = two(a)|};
  {%fol|(a*b * b*c) = b|}];;

complete_and_simplify ["*"; "one"; "two"] eqs;;

 ************)

(* ------------------------------------------------------------------------- *)
(* Simply congruence closure.                                                *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|f(f(f(f(f(1))))) = 1|}; {%fol|f(f(f(1))) = 1|}];;

complete_and_simplify ["1"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Bill McCune's and Deepak Kapur's single axioms for groups.                *)
(* ------------------------------------------------------------------------- *)

(*****************

let eqs =
 [{%fol|x * i(y * (((z * i(z)) * i(u * y)) * x)) = u|}];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

let eqs =
 [{%fol|((1 / (x / (y / (((x / x) / x) / z)))) / z) = y|}];;

complete_and_simplify ["1"; "/"] eqs;;

let eqs =
 [{%fol|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z|}];;

complete_and_simplify ["*"; "i"] eqs;;

**************)

(* ------------------------------------------------------------------------- *)
(* A rather simple example from Baader & Nipkow, p. 141.                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [{%fol|f(f(x)) = g(x)|}];;

complete_and_simplify ["g"; "f"] eqs;;

(* ---- *)

let eqs1,def1,crits1 = funpow 122 (complete1 ord) (eqs,def,crits);;

let eqs2,def2,crits2 = funpow 123 (complete1 ord) (eqs,def,crits);;

(* ---- *)

let eqs =
 [{%fol|f(f(x)) = f(x)|};
  {%fol|g(g(x)) = f(x)|};
  {%fol|f(g(x)) = g(x)|};
  {%fol|g(f(x)) = f(x)|}];;

complete_and_simplify ["f"; "g"] eqs;;

let eqs =  [{%fol|f(g(f(x))) = g(x)|}];;

complete_and_simplify ["f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inductive theorem proving example.                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [{%fol|0 + y = y|};
  {%fol|SUC(x) + y = SUC(x + y)|};
  {%fol|append(nil,l) = l|};
  {%fol|append(h::t,l) = h::append(t,l)|};
  {%fol|length(nil) = 0|};
  {%fol|length(h::t) = SUC(length(t))|};
  {%fol|rev(nil) = nil|};
  {%fol|rev(h::t) = append(rev(t),h::nil)|}];;

complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs;;

let iprove eqs' tm =
 complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
   (tm :: eqs' @ eqs);;

iprove [] {%fol|x + 0 = x|};;

iprove [] {%fol|x + SUC(y) = SUC(x + y)|};;

iprove [] {%fol|(x + y) + z = x + y + z|};;

iprove [] {%fol|length(append(x,y)) = length(x) + length(y)|};;

iprove [] {%fol|append(append(x,y),z) = append(x,append(y,z))|};;

iprove [] {%fol|append(x,nil) = x|};;

iprove [{%fol|append(append(x,y),z) = append(x,append(y,z))|};
        {%fol|append(x,nil) = x|}]
        {%fol|rev(append(x,y)) = append(rev(y),rev(x))|};;

iprove [{%fol|rev(append(x,y)) = append(rev(y),rev(x))|};
        {%fol|append(x,nil) = x|};
        {%fol|append(append(x,y),z) = append(x,append(y,z))|}]
        {%fol|rev(rev(x)) = x|};;

(* ------------------------------------------------------------------------- *)
(* Here it's not immediately so obvious since we get extra equs.             *)
(* ------------------------------------------------------------------------- *)

iprove [] {%fol|rev(rev(x)) = x|};;

(* ------------------------------------------------------------------------- *)
(* With fewer lemmas, it may just need more time or may not terminate.       *)
(* ------------------------------------------------------------------------- *)

(********* not enough lemmas...or maybe it just needs more runtime

iprove [{%fol|rev(append(x,y)) = append(rev(y),rev(x))|}]
        {%fol|rev(rev(x)) = x|};;

 *********)

(* ------------------------------------------------------------------------- *)
(* Now something actually false...                                           *)
(* ------------------------------------------------------------------------- *)

iprove [] {%fol|length(append(x,y)) = length(x)|};; (*** try something false ***)

*************)
