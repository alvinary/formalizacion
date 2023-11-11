theory CKA
  imports Main HOL.Set ShuffleLanguages
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

(* ac_simps makes a statement available for simplifiers that
use commutativity and associativity *)

text "Here we define monoids and semirings,
      as locales."

locale monoid =
  fixes
    compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "." 70) and
    unit :: 'a ("1")
  assumes
    one_is_right_neuter [ simp ] :
      " x.1 = x " and
    one_is_left_neuter [ simp ] :
      " 1.x = x "

locale commutative_monoid =
    monoid "compose" "unit" for
      compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "." 70) and
      unit :: 'a ("1") +
  assumes
    composition_is_commutative [simp] :
      "compose x y = compose y x"

locale semiring =
  plus_commutative_monoid : commutative_monoid plus zero +
  times_monoid : monoid times one for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 80) and
    zero :: 'a ("0") and
    one :: 'a ("1") +
  assumes
    times_distributes_over_plus :
      "times a (plus c b) = plus (times a c) (times a b) " and
    zero_is_left_anihilator [simp] :
      " times zero a = zero " and
    zero_is_right_anihilator [simp] :
      " times a zero = zero "

locale idempotent_semiring =
  semiring plus times zero one for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 80) and
    zero :: 'a ("0") and
    one :: 'a ("1") +
  assumes
    plus_is_idempotent [simp] :
      " plus a a = a " 

(* Natural order and complete lattices *)

locale natural_order_semiring =
  fixes
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<le>" 50) and
    semiring plus times zero one
  assumes
    induced_natural_order :
      " plus a b = b \<longleftrightarrow> leq a b "

(*
locale complete_lattice =
  fixes
    infimum :: "'a set \<Rightarrow> 'a" (infixl "" 60) and
  assumes
    infimum_exists :
      ""

-- top will be sigma star
-- bottom will be the empty set
-- leq is the induced natural order

*)

(* Quantales *)

(*
class quantale =
  natural_order_semiring +
  complete_lattice +
  assumes
    exchange_law :
      <exchange_law>
*)

(*

  Exchange law

  "(((a * b);(c * d)) \<le> ((b;c) * (a;d)))"
*)

text "Now we define shuffle languages
      and instance the locales we
      defined earlier."

(* Instances *)

interpretation "'a set" : commutative_monoid union "empty"
proof
  show " \<And>x. x \<union> {} = x "
    by simp
  show " \<And>x. {} \<union> x = x "
    by simp
  show " \<And>x y. x \<union> y = y \<union> x "
    by (simp add: Un_commute)
qed

lemma shuffle_nil_left : " shuffles [] xs = {xs} "
  by simp

lemma shuffle_nil_right : " shuffles xs [] = {xs} "
  by simp

lemma concat_nil_left : " [] @ xs = xs "
  by simp

lemma concat_nil_right : " xs @ [] = xs "
  by simp

lemma pconcat_one_right : " A ; {[]} = A "
  sorry

lemma pconcat_one_left : " {[]} ; A = A "
  sorry

interpretation "'a language" : monoid language_concat "{[]}"
proof
  show " \<And>x. {[]} ; x = x "
    sorry
  show " \<And>x. language_concat x {[]} = x "
    sorry 
qed

end
     