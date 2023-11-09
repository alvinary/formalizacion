theory CKA
  imports Main "HOL-Lattice.CompleteLattice" ShuffleLanguages
begin

(*

class quantale = proto_quantale + semigroup_mult

class semigroup_mult = times +
  assumes mult_assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "(a * b) * c = a * (b * c)"

class proto_quantale = proto_near_quantale +
  assumes Sup_distl: "x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)"

class proto_near_quantale = complete_lattice + times + 
  assumes Sup_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"

definition (in times) opp_mult (infixl "\<odot>" 70)
  where "x \<odot> y \<equiv> y \<cdot> x"

lemma (in semiring_1) dual_semiring_1:
  "class.semiring_1 1 (\<odot>) (+) 0"
  by unfold_locales (auto simp add: opp_mult_def mult.assoc distrib_right distrib_left)

lemma (in dioid_one_zero) dual_dioid_one_zero:
  "class.dioid_one_zero (+) (\<odot>) 1 0 (\<le>) (<)"
  by unfold_locales (auto simp add: opp_mult_def mult.assoc distrib_right distrib_left)

class complete_lattice = lattice + Inf + Sup + bot + top +
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
    and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
    and Sup_upper: "x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
    and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
    and Inf_empty [simp]: "\<Sqinter>{} = \<top>"
    and Sup_empty [simp]: "\<Squnion>{} = \<bottom>"
begin

*)

locale concat =
  fixes concat :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 75)

locale times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)

locale plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)

locale one =
  fixes one :: "'a"

locale zero =
  fixes zero :: "'a"

(* ac_simps makes a statement available for simplifiers that
use commutativity and associativity *)

class times_monoid  =
  times +
  one +
  assumes
  one_is_right_neuter [ac_simps] : "a * one = a" and
  one_is_left_neuter [ac_simps] : "one * a = a"

class plus_monoid =
  plus +
  zero +
  assumes
  zero_is_right_neuter [ac_simps] : "a + zero = a" and
  zero_is_left_neuter [ac_simps] : "zero + a = a"

class commutative_plus_monoid =
  plus_monoid +
  assumes
  plus_commutative [ac_simps] : "a + b = b + a"

class semiring =
  commutative_plus_monoid +
  times_monoid +
  assumes
    times_distributes_over_plus : "a * (c + b) = a * c + a * b" and
    zero_is_left_anihilator : "zero * a = zero" and
    zero_is_right_anihilator : "a * zero = zero"

class idempotent_semiring =
  semiring +
  assumes
    plus_is_idempotent [simp] : "a + a = a"

class natural_order_semiring =
  idempotent_semiring +
  fixes leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    leq_definition : "leq a b \<longleftrightarrow> a + b = b"

class quantale =
  natural_order_semiring +
  complete_lattice

(*
  "(((a * b);(c * d)) \<le> ((b;c) * (a;d)))"
*)

end