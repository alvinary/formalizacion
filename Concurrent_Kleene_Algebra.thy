theory Concurrent_Kleene_Algebra
  imports Main HOL.Rings "Regular-Sets.Regular_Set"
begin

text "We define idempotent semirings and
      a natural ordering over their elements"

locale idempotent_semiring =
  semiring_0 plus zero times for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" +
  assumes
    plus_is_idempotent [simp] :
      " a \<oplus> a = a "

locale natural_order_semiring =
  idempotent_semiring plus times zero for
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 60) +
  assumes
    induced_natural_order :
      " a \<oplus> b = b \<longleftrightarrow> a \<preceq> b "

text "Now we interpret the locales we defined earlier
      for union and two operations over languages, which 
      are shuffle and concatenation."

interpretation
  union_concat_semiring :
    idempotent_semiring union conc empty
proof
  show
    " \<And>a b c. a \<union> b \<union> c = a \<union> (b \<union> c)"
    unfolding conc_def
    by auto
  show
    " \<And>a b. a \<union> b = b \<union> a "
    by auto
  show
    "\<And>a b c. (a @@ b) @@ c = a @@ b @@ c"
    unfolding conc_def
    by blast
  show
    " \<And>a b c. (a \<union> b) @@ c = a @@ c \<union> b @@ c"
    unfolding conc_def
    by auto
  show "  \<And>a b c. a @@ (b \<union> c) = a @@ b \<union> a @@ c "
    unfolding conc_def
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
    " \<And>a. a \<union> a = a "
    by auto
qed

interpretation
  union_shuffle_semiring :
    idempotent_semiring union Shuffle empty
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
qed

text "And here we define Quantales"

locale quantale =
  idempotent_semiring plus times zero for
    plus :: "'a::ord \<Rightarrow> 'a::ord \<Rightarrow> 'a::ord" (infixl "\<oplus>" 70) and
    times :: "'a::ord \<Rightarrow> 'a::ord \<Rightarrow> 'a::ord" (infixl "\<otimes>" 80) and
    zero :: "'a::ord" ("0") and
    sup :: "'a::ord set  \<Rightarrow> 'a::ord" ("\<Squnion>") +
  assumes
    times_distributes_over_suprema :
      "  a \<otimes> (\<Squnion> A) = \<Squnion> ({ a \<otimes> x | x. x : A }) "

locale concurrent_kleene_algebra =
  sequential_quantale : quantale plus seq zero sup +
  parallel_quantale : quantale plus par zero sup for
    plus :: "'a::ord \<Rightarrow> 'a::ord \<Rightarrow> 'a::ord" and
    seq :: "'a::ord \<Rightarrow> 'a::ord \<Rightarrow> 'a::ord" (infixl ";;" 70) and
    par :: "'a::ord \<Rightarrow> 'a::ord \<Rightarrow> 'a::ord" (infixl "||" 60) and
    zero :: "'a::ord" ("0") and
    sup :: "'a::ord set \<Rightarrow> 'a::ord" +
  assumes
    exchange_law :
      " ((a || b) ;; (c || d)) \<le> ((a ;; c) || (b ;; d)) "

interpretation union_concatenation_quantale :
  quantale "(\<union>)" "(@@)" "empty" "\<Union>"
proof
  show " \<And>a A. a @@ \<Union> A = \<Union> {a @@ x |x. x \<in> A} "
    unfolding conc_def
    by auto
qed

end

