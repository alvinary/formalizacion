theory Concurrent_Kleene_Algebra
  imports Main HOL.Rings "Regular-Sets.Regular_Set"
begin

text "We define idempotent semirings and
      a natural ordering over their elements"

locale idempotent_semiring =
  semiring_1 one times plus zero for
    one :: "'a" and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" +
  assumes
    plus_is_idempotent [simp] :
      " a \<oplus> a = a "

locale natural_order_semiring =
  idempotent_semiring one plus times zero for
    one :: "'a" and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 60) +
  assumes
    induced_natural_order :
      " a \<oplus> b = b \<longleftrightarrow> a \<preceq> b " and
    leq_is_antisymmetric :
      " a \<preceq> b \<Longrightarrow> b \<preceq> a \<Longrightarrow> a = b " and
    leq_is_transitive :
      " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> a \<preceq> c " and
    leq_is_reflexive :
      " a \<preceq> a "

text "Now we interpret the locales we defined earlier
      for union and two operations over languages, which 
      are shuffle and concatenation."

interpretation
  union_concat_semiring :
    natural_order_semiring "{[]}" "(\<union>)" "(@@)" "{}" "(\<subseteq>)"
proof
  show
    " \<And>a b c. a \<union> b \<union> c = a \<union> (b \<union> c)"
    unfolding conc_def
    by auto
  show
    " \<And>a b c. (a @@ b) @@ c = a @@ b @@ c "
    unfolding conc_def
    by blast
  show
    " \<And>a. {[]} @@ a = a "
    by auto
  show
    " \<And>a. a @@ {[]} = a "
    by auto
  show
    " \<And>a b. a \<union> b = b \<union> a "
    by auto
  show
    " \<And>a. {} \<union> a = a "
    by auto
  show
    " \<And>a. {} @@ a = {} "
    by auto
  show
    " \<And>a. a @@ {} = {} "
    by auto
  show
    " \<And>a b c. (a \<union> b) @@ c = a @@ c \<union> b @@ c "
    by auto
  show " \<And>a b c. a @@ (b \<union> c) = a @@ b \<union> a @@ c "
    by auto
  show " {} \<noteq> {[]} "
    by auto
  show " \<And>a. a \<union> a = a "
    by auto
  show " \<And>a b. (a \<union> b = b) = (a \<subseteq> b) "
    by auto
  show
    " \<And>a b. a \<subseteq> b \<Longrightarrow> b \<subseteq> a \<Longrightarrow> a = b "
    by auto
  show
    " \<And>a b c. a \<subseteq> b \<and> b \<subseteq> c \<Longrightarrow> a \<subseteq> c "
    by auto
  show
    " \<And>a. a \<subseteq> a "
    by auto
qed

interpretation
  union_shuffle_semiring :
    natural_order_semiring "{[]}" "(\<union>)" "(\<parallel>)" "{}" "(\<subseteq>)"
proof
  show
    " \<And>a b c. (a \<parallel> b) \<parallel> c =  a \<parallel> b \<parallel> c "
    unfolding Shuffle_def
    by simp_all blast
  show
    " \<And>a b c. (a \<union> b) \<parallel> c = a \<parallel> c \<union> b \<parallel> c "
    unfolding Shuffle_def
    by blast
  show
    " \<And>a b c. a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
    unfolding Shuffle_def
    by blast
  show
    " \<And>a. {} \<parallel> a = {} "
    by auto
  show
    "  \<And>a. a \<parallel> {} = {} "
    by auto
  show
    " \<And>a. a \<union> a = a "
    by auto
  show
    " \<And>a b. (a \<union> b = b) = (a \<subseteq> b) "
    by auto
  show 
    " \<And>a. {[]} \<parallel> a = a "
    by auto
  show
    " \<And>a. a \<parallel> {[]} = a "
    by auto
  show
    " \<And>a b. a \<subseteq> b \<Longrightarrow> b \<subseteq> a \<Longrightarrow> a = b "
    by auto
  show
    " \<And>a b c. a \<subseteq> b \<and> b \<subseteq> c \<Longrightarrow> a \<subseteq> c "
    by auto
  show
    "  \<And>a. a \<subseteq> a "
    by auto
qed

text "And here we define Quantales"

locale quantale =
  natural_order_semiring one plus times zero leq for
    one :: "'a" ("1") and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a\<Rightarrow> bool" (infixl "\<sqsubseteq>" 40) and
    sup :: "'a set  \<Rightarrow> 'a" ("\<Squnion>") +
  assumes
    times_distributes_over_suprema :
      "  a \<otimes> (\<Squnion> A) = \<Squnion> ({ a \<otimes> x | x. x : A }) " and
    is_complete_lattice :
      " \<And> x A. (\<And> y . y : A \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> (\<Squnion> A) \<sqsubseteq> x "

locale concurrent_kleene_algebra =
  sequential_quantale : quantale one plus seq zero leq sup +
  parallel_quantale : quantale one plus par zero leq sup for
    one :: "'a" ("1") and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 70) and
    par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "|" 60) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 40) and
    sup :: "'a set \<Rightarrow> 'a" +
  assumes
    exchange_law :
      " a | b ; c | d \<sqsubseteq> a ; c | b ; d "

interpretation union_concatenation_quantale :
  quantale "{[]}" "(\<union>)" "(@@)" "empty" "(\<subseteq>)" "\<Union>"
proof
  show " \<And>a A. a @@ \<Union> A = \<Union> {a @@ x |x. x \<in> A} "
    unfolding conc_def
    by auto
  show " \<And>x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x"
    by auto
qed

interpretation union_shuffle_quantale :
  quantale "{[]}" "(\<union>)" "(\<parallel>)" "empty" "(\<subseteq>)" "\<Union>"
proof
  show " \<And>a A. a \<parallel> \<Union> A =  \<Union> {a \<parallel> x |x. x \<in> A} "
    unfolding Shuffle_def
    by auto
  show "  \<And>x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x "
    unfolding Shuffle_def
    by auto
qed

interpretation shuffle_languages_cka :
  concurrent_kleene_algebra "{[]}" "(\<union>)" "(@@)" "(\<parallel>)" "empty" "(\<subseteq>)" "\<Union>"
proof
  show "  \<And>a b c d. (a \<parallel> (b @@ c)) \<parallel> d \<subseteq> (a @@ c) \<parallel> (b @@ d) "
    unfolding Shuffle_def conc_def
    by simp_all blast
qed

(*
lemma (in concurrent_kleene_algebra)
  par_contains_seq : " a ; b \<sqsubseteq> a | b "
  sorry 
*)

end
