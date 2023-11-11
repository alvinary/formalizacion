theory ShuffleLanguages
  imports Main
begin

(*
So far:
- Singletons can be written as is (like {a})
- Apparently big operators have the same name as small operators, but capitalized
  (at least for union and Union)
- "Big" Union is defined in the theory Complete Lattices
*)

type_synonym 'a language = "('a list) set"

definition language_concat :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" (infixr ";" 75) where
  "A ; B = {xs@ys | xs ys. xs : A & ys : B}"

lemma concatenation_intro [simp, intro] :
  " s : A & t : B \<Longrightarrow> s @ t : A ; B "
  by (auto simp add: language_concat_def)

lemma concatenation_elimination [elim] :
  assumes
    " u : A ; B "
  obtains
    s t where
      " s : A "
      " t : B "
      " u = s @ t"
  using
    assms
  by
    (auto simp: language_concat_def)

lemma concat_nil_right [simp] :
  " A ; {[]} = A "
  by (simp_all add:language_concat_def)

lemma concat_nil_left [simp] :
  " {[]} ; A = A "
  by (simp_all add:language_concat_def)

function shuffles (infixr "\<diamondop>" 80) where
  "shuffles [] ys = {ys}"
| "shuffles xs [] = {xs}"
| "shuffles (x # xs) (y # ys) = (#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys"
  by pat_completeness simp_all
termination by lexicographic_order

definition language_shuffle :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" (infixr "\<diamondop>" 65) where
  " A \<diamondop> B = Union {shuffles xs ys | xs ys. xs : A & ys : B} "

lemma shuffle_intro [simp, intro] :
  " s : A & t : B \<Longrightarrow> (shuffles s t) \<subseteq> A \<diamondop> B "
  sorry

lemma inclusion_forall : "(\<And> x. x : A \<Longrightarrow>  x : B) \<Longrightarrow> A \<subseteq> B"
  by auto

(*
lemma shuffle_exchange_law : "(A \<diamondop> B) ; (C \<diamondop> D) \<subseteq> (A ; C) \<diamondop> (B ; D)"
  sorry
*)

fun head_concat :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "head_concat a Nil = Nil" |
  "head_concat a (b#bs) = (a@b)#(head_concat a bs)"

fun product_concat :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "product_concat Nil s = Nil" |
  "product_concat (x#xs) s = (head_concat x s) @ product_concat xs s"

fun list_shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "list_shuffles [] s = [s]" |
  "list_shuffles s [] = [s]" |
  "list_shuffles (a#s) (b#t) = head_concat [a] (list_shuffles s (b#t)) @ head_concat [b] (list_shuffles (a#s) t)"

fun is_list_member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_list_member x [] = False" |
  "is_list_member x (y#xs) = ( if x=y then True else (is_list_member x xs) )"

(*
lemma is_list_member x xs \<longrightarrow> member x (set xs)

lemma all xs ys n. is_list_member (shuffle_on_index xs ys n) (shuffles xs ys)

lemma is_list_member \<longrightarrow> member x (set xs)

*)

end
