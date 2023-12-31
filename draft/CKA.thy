theory CKA
  imports Main HOL.Set ShuffleLanguages
begin

(* ac_simps makes a statement available for simplifiers that
use commutativity and associativity *)

(* Doing a proof inside 'Using assms' makes hypotheses available *)

text "Here we define monoids and semirings
      as locales."

locale monoid =
  fixes
    compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 70) and
    unit :: 'a ("1")
  assumes
    one_is_right_neuter [ simp ] :
      " x \<odot> 1 = x " and
    one_is_left_neuter [ simp ] :
      " 1 \<odot> x = x "

locale commutative_monoid =
    monoid "compose" "unit" for
      compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 70) and
      unit :: 'a ("1") +
  assumes
    composition_is_commutative [simp] :
      " x \<odot> y = y \<odot> x "

locale semiring =
  plus_commutative_monoid : commutative_monoid plus zero +
  times_monoid : monoid times one for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: 'a ("0") and
    one :: 'a ("1") +
  assumes
    times_distributes_over_plus :
      "a \<otimes> (c \<oplus> b) = (a \<otimes> c) \<oplus> (a \<otimes> b) " and
    zero_is_left_anihilator [simp] :
      " 0 \<otimes> a = 0 " and
    zero_is_right_anihilator [simp] :
      " a \<otimes> 0 = 0 "

locale idempotent_semiring =
  semiring plus times zero one for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: 'a ("0") and
    one :: 'a ("1") +
  assumes
    plus_is_idempotent [simp] :
      " a \<oplus> a = a " 

(* Natural order *)

locale natural_order_semiring =
  idempotent_semiring plus times zero one for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: 'a ("0") and
    one :: 'a ("1") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 60) +
  assumes
    induced_natural_order :
      " a \<oplus> b = b \<longleftrightarrow> a \<preceq> b "

text "Now we interpret the
      locales we defined
      earlier."

(* Instances *)

interpretation "'a set" :
  commutative_monoid union "empty"
proof
  show " \<And>x. x \<union> {} = x "
    by simp
  show " \<And>x. {} \<union> x = x "
    by simp
  show " \<And>x y. x \<union> y = y \<union> x "
    by (simp add: Un_commute)
qed

interpretation
  "'a language" : monoid language_concat "{[]}"
proof
  show " \<And>x. {[]} ; x = x "
    by simp
  show " \<And>x. language_concat x {[]} = x "
    by simp
qed

interpretation
  union_concat_semiring : semiring union language_concat empty "{[]}"
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

interpretation union_shuffle_semiring :
  semiring union language_shuffle empty "{[]}"
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

(* Deberia extender la clase ord para no tener ese error de tipo
   al cambiar less_or_equal por \<le> *)

(* Lo ideal seria importar el complete lattice y
   las otras estructuras algebraicas del AFP *)

locale complete_lattice =
  fixes
    less_or_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60) and
    supremum :: "'a set \<Rightarrow> 'a" ("\<Squnion>")
  assumes
    supremum_is_upper_bound :
      " a \<in> A \<Longrightarrow>  less_or_equal a (supremum A) " and
    supremum_is_least_upper_bound :
      " \<And> x A. (\<And> y . y : A \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> (\<Squnion> A) \<sqsubseteq> x "

(*Deberia ser la menor cota superior, no solamente una cota superior *)

interpretation "'a language" : complete_lattice "(\<subseteq>)" "\<Union>"
proof
  show " \<And>a A. a \<in> A \<Longrightarrow> a \<subseteq> \<Union> A "
    by auto
  show " \<And>x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x"
    by auto
qed

(* Quantales *)

locale quantale =
  is_idempotent_semiring :
    natural_order_semiring plus times zero one leq +
  is_complete_lattice : complete_lattice leq sup for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    zero :: "'a" and
    one :: "'a" and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    sup :: "'a set \<Rightarrow> 'a" +
  assumes
    times_distributes_over_suprema :
       " times a (sup A) = sup ({times a x | x. x : A}) "

interpretation concat_quantale :
  quantale "(\<union>)" "(;)" "empty" "{[]}" "(\<subseteq>)" "(\<Union>)"
proof
  show " \<And>a. a \<union> a = a "
    by auto
  show " \<And>a b. (a \<union> b = b) = (a \<subseteq> b) "
    by auto
  show " \<And>a A. a ; \<Union> A = \<Union> {a ; x |x. x \<in> A} "
    unfolding concat_def
    by fast
qed

interpretation shuffle_quantale :
  quantale "(\<union>)" "language_shuffle" "empty" "{[]}" "(\<subseteq>)" "(\<Union>)"
proof
  show " \<And>a. a \<union> a = a "
    by auto
  show " \<And>a b. (a \<union> b = b) = (a \<subseteq> b) "
    by auto
  show " \<And>a A. a \<diamondop> \<Union> A = \<Union> {a \<diamondop> x |x. x \<in> A} "
    by fast
qed

locale concurrent_kleene_algebra =
  sequential_quantale : quantale plus seq zero one leq sup +
  parallel_quantale : quantale plus par zero one leq sup for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";;" 70) and
    par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "||" 60) and
    zero :: "'a" and
    one :: "'a" and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<le>" 60) and
    sup :: "'a set \<Rightarrow> 'a" +
  assumes
    exchange_law :
      " ((a || b) ;; (c || d)) \<le> ((a ;; c) || (b ;; d)) "

interpretation
  concurrent_kleene_algebra
    "(\<union>)" "(;)" "language_shuffle" "empty" "{[]}" "(\<subseteq>)" "(\<Union>)"
proof
  show
    " \<And>a b c d. (a \<diamondop> b) ; (c \<diamondop> d) \<subseteq> a ; c \<diamondop> b ; d "
  unfolding language_concat_def
  unfolding language_shuffle_def
  by simp_all fast
qed

end
