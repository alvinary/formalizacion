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
      for set union and two operations on languages, 
      shuffle and concatenation."

lemma concatenation_is_associative [simp] :
  " (a @ b) @ c = a @ (b @ c) "
  by auto

lemma shuffle_is_commutative [simp] :
  " shuffles \<alpha> \<beta> = shuffles \<beta> \<alpha> "
  by (metis shuffles_commutes)

lemma Shuffle_is_commutative [simp] :
  " Shuffle A B = Shuffle B A "
  sorry

lemma Shuffle_is_associative [simp] :
  " Shuffle (Shuffle A B) C = Shuffle A (Shuffle B C) "
  sorry

(*
proof
  have A_par_B_is_def :
    "Shuffle A B = \<Union> {shuffles \<alpha> \<beta> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B }"
    sorry
  have
    "Shuffle A B = \<Union> {shuffles \<beta> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B }"
    sorry (* definition and commutatitivty *)
  
qed
*)

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
    by (metis conc_assoc conc_def)
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
    by (metis Shuffle_is_associative)
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
  show
    " \<And>a b c. (a \<union> b) \<parallel> c = a \<parallel> c \<union> b \<parallel> c "
    unfolding Shuffle_def
    sorry
  show
    " \<And>a b c. a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
    unfolding Shuffle_def
    sorry
qed

text "And here we define Quantales"

locale quantale =
  natural_order_semiring one plus times zero leq for
    one :: "'a" ("1") and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 40) and
    sup :: "'a set  \<Rightarrow> 'a" ("\<Squnion>") +
  assumes
    times_distributes_over_suprema :
      "  a \<otimes> (\<Squnion> A) = \<Squnion> ({ a \<otimes> x | x. x : A }) " and
    is_complete_lattice :
      " \<And> x A. (\<And> y . y : A \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> (\<Squnion> A) \<sqsubseteq> x "

locale concurrent_kleene_algebra =
  sequential_quantale : quantale one plus seq zero leq sup +
  parallel_quantale : quantale one plus par zero leq sup 
  for
    one :: "'a" ("1") and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 70) and
    par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "||" 60) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 40) and
    sup :: "'a set \<Rightarrow> 'a" +
  assumes
    exchange_law :
      " (a || b) ; (c || d) \<sqsubseteq> (b ; c) || (a ; d) "
begin

lemma one_is_seq_neuter_right [simp] :
  " x ; 1 = x "
  by auto

lemma one_is_seq_neuter_left [simp] :
  " 1 ; x = x "
  by auto

lemma one_is_par_neuter_right [simp] :
  " x || 1 = x "
  by auto

lemma one_is_par_neuter_left [simp] :
  " 1 || x = x "
  by auto

lemma par_is_commutative [simp] :
  " x || y = y || x "
proof -
  have
    replace_by_one :
    " (x || y) ; (1 || 1) \<sqsubseteq> (y ; 1) || (x ; 1) "
    by (metis exchange_law)
  have
    simplify_ones :
    " (x || y ) \<sqsubseteq> (y || x) "
    by (metis
          replace_by_one
          one_is_seq_neuter_right
          one_is_par_neuter_right)
  have 
    swapped_exchange :
    " (y || x) ; (1 || 1) \<sqsubseteq> (x ; 1) || (y ; 1) "
    by (metis exchange_law)
  have 
    swapped_replace_by_one : 
    " (y || x) ; (1 || 1) \<sqsubseteq> (x ; 1) || (y ; 1) "
    by (metis swapped_exchange)
  have 
    swapped_simplify_ones :
    " (y || x ) \<sqsubseteq> (x || y) "
    by (metis
          swapped_replace_by_one
          one_is_seq_neuter_right
          one_is_par_neuter_right)
  have 
    symmetric_order :
    "(y || x ) \<sqsubseteq> (x || y) \<and> (x || y ) \<sqsubseteq> (y || x) "
    by (metis
          swapped_simplify_ones
          simplify_ones)
  show
    " (x || y) = (y || x) "
    by (metis
        symmetric_order
        parallel_quantale.leq_is_antisymmetric)
qed

lemma par_contains_seq :
  " x ; y \<sqsubseteq> x || y "
proof -
  have 
    long_contains :
    " (1 || x) ; (1 || y) \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (metis exchange_law)
  have
    simplify_pars :
    " x ; y  \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (metis long_contains one_is_par_neuter_left one_is_par_neuter_right )
  then show
    simplify_seqs :
    " x ; y  \<sqsubseteq> x || y "
    by (simp)
qed

lemma alternative_exchange :
  "(x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w) "
proof -
  have renamed_exchange :
    "(y || x) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w)"
    by (metis exchange_law)
  show "(x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w)"
    by (metis renamed_exchange par_is_commutative)
qed

lemma par_extraction :
  " (x || y) ; z \<sqsubseteq> x || (y ; z) "
proof -
  have partial_exchange :
    " (x || y) ; (1 || z) \<sqsubseteq> (x ; 1) || (y ; z) "
    by (metis alternative_exchange)
  then show " (x || y) ; z \<sqsubseteq> x || (y ; z) "
    by simp
qed
  

lemma seq_extraction :
  " (x || y) ; z \<sqsubseteq> x || (y ; z) "
proof -
  have partial_alternative :
    " (x || y) ; (1 || z) \<sqsubseteq> (x ; 1) || (y ; z) "
    by (metis alternative_exchange)
  then show " (x || y) ; z \<sqsubseteq> x || (y ; z) "
    by (simp)
qed

lemma par_is_associative [simp] :
  "(x || y) || z = x || (y || z)"
  by (metis local.parallel_quantale.mult_assoc)

end

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
  show " \<And> a A. a \<parallel> \<Union> A =  \<Union> {a \<parallel> x |x. x \<in> A} "
    unfolding Shuffle_def
    by auto
  show "  \<And> x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x "
    unfolding Shuffle_def
    by auto
qed

interpretation shuffle_languages_cka :
  concurrent_kleene_algebra "{[]}" "(\<union>)" "(@@)" "(\<parallel>)" "empty" "(\<subseteq>)" "\<Union>"
proof
  show "  \<And>a b c d. a \<parallel> b @@ c \<parallel> d \<subseteq> (b @@ c) \<parallel> (a @@ d) "
    unfolding Shuffle_def conc_def
    sorry
qed

end

(*
lemma par_contains_seq :
  " x ; w \<sqsubseteq> x | w "
proof -
  assume exchange : " (x | y) ; (z | w) \<sqsubseteq> (x ; z) | (y ; w) "
  assume y_is_one : " y = 1 "
  assume z_is_one : " z = 1 "
    have
    replace_by_one :
    " (x | 1) ; (1 | w) \<sqsubseteq> (x ; 1) | (1 ; w) "
    by (metis
        exchange
        z_is_one
        y_is_one)
  have
    simplify_pars :
    " x ; w  \<sqsubseteq> (x ; 1) | (1 ; w) "
    by (metis
        replace_by_one
        one_is_par_neuter_right
        one_is_par_neuter_left)
  have
    simplify_seqs :
    " x ; w  \<sqsubseteq> x | w "
    by (metis simplify_pars
        one_is_seq_neuter_right
        one_is_seq_neuter_left)
*)

    (* by (metis
          symmetric_order
          leq_is_antisymmetric) *)
