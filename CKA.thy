theory CKA
  imports Main HOL.Set ShuffleLanguages
begin

(* ac_simps makes a statement available for simplifiers that
use commutativity and associativity *)

(* Doing a proof inside 'Using assms' makes hypotheses available *)

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

text "Now we interpret the
      locales we defined
      earlier."

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

interpretation "'a language" : monoid language_concat "{[]}"
proof
  show " \<And>x. {[]} ; x = x "
    by simp
  show " \<And>x. language_concat x {[]} = x "
    by simp
qed

interpretation union_concat_semiring : semiring union language_concat empty "{[]}"
proof
  show
    " \<And>a c b. a ; (c \<union> b) = a ; c \<union> a ; b "
    unfolding language_concat_def
    by fast+
  show
    " \<And>a. {} ; a = {} "
    unfolding language_concat_def
    by fast+
  show
    " \<And>a. a ; {} = {} "
    unfolding language_concat_def
    by fast+
qed

interpretation union_shuffle_semiring : semiring union language_shuffle empty "{[]}"
proof
  show
    " \<And>a c b. a  \<diamondop> (c \<union> b) = (a \<diamondop> c) \<union> (a \<diamondop> b) "
    unfolding language_concat_def
    by simp_all
  show
    " \<And>x. x \<diamondop> {[]} = x "
    unfolding language_concat_def
    by auto
  show
    " \<And>x. {[]} \<diamondop> x = x "
    unfolding language_concat_def
    by auto
  show
    " \<And>a. {} \<diamondop> a = {} "
    unfolding language_concat_def
    by auto
  show " \<And>a. a \<diamondop> {} = {} "
    unfolding language_concat_def
    by auto
qed

(* Complete lattices *)

locale complete_lattice =
  fixes
    less_or_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    supremum :: "'a set \<Rightarrow> 'a"
  assumes
    infimum_of_set :
      " a \<in> A \<Longrightarrow> less_or_equal a (supremum A) "

interpretation "'a language" : complete_lattice "(\<subseteq>)" "\<Union>"
proof
  show " \<And>a A. a \<in> A \<Longrightarrow> a \<subseteq> \<Union> A "
    by auto
qed

(* Quantales *)

(*
class concurrent_kleene_algebra =
  sequential_quantale : ... +
  concurrent_quantale : ... for
  plus ... (+) and
  seq ... (;) and
  par ... (|) and
  one ... (1) and
  zero ... (0) +
  assumes
    exchange_law :
      <exchange_law>
*)

(* Exchange law *)

lemma cka_exchange_law :
  " (((a \<diamondop> b);(c \<diamondop> d)) \<le> ((b;c) \<diamondop> (a;d))) "
proof
  show " \<And>x. x \<in> (a \<diamondop> b) ; (c \<diamondop> d) \<Longrightarrow> x \<in> b ; c \<diamondop> a ; d "
    unfolding language_concat_def
    unfolding language_shuffle_def
    by simp_all fast
qed

end
     
