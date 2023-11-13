theory ShuffleLanguages
  imports Main
begin

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

(* String shuffles *)

function shuffles (infixr "\<diamondop>" 80) where
  "shuffles [] ys = {ys}"
| "shuffles xs [] = {xs}"
| "shuffles (x # xs) (y # ys) = (#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys"
  by pat_completeness simp_all
termination by lexicographic_order

(* Language shuffle *)

definition language_shuffle :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" (infixr "\<diamondop>" 65) where
  " A \<diamondop> B = Union {shuffles xs ys | xs ys. xs : A & ys : B} "

lemma shuffle_union_distribute [simp] :
  " A \<diamondop> (B \<union> C) = (A \<diamondop> B) \<union> (A \<diamondop> C) "
  unfolding language_shuffle_def
  by fast+

lemma shuffle_empty_right [simp] :
  " A \<diamondop> {} = {} "
  unfolding language_shuffle_def
  by auto

lemma shuffle_empty_left [simp] :
  " {} \<diamondop> A = {} "
  unfolding language_shuffle_def
  by auto

lemma shuffle_one_left [simp] :
  " {[]} \<diamondop> A = A "
  unfolding language_shuffle_def
  by auto

lemma shuffle_one_right [simp] :
  " A \<diamondop> {[]} = A "
  unfolding language_shuffle_def
  by auto

end
