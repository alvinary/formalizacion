theory Concurrent_Kleene_Algebra
  imports Main HOL.Rings "Regular-Sets.Regular_Set"
begin

text " We define idempotent semirings and
      a natural ordering over their elements "

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
  " A \<parallel> B = B \<parallel> A "
proof -
  have " A \<parallel> B = \<Union> {shuffles \<alpha> \<beta> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
    unfolding Shuffle_def
    by auto
  then have swap_alpha_and_beta :
    " A \<parallel> B = \<Union> {shuffles \<beta> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
    by (simp)
  have B_par_A_is_def :
    " B \<parallel> A = \<Union> {shuffles \<beta> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B  } "
    unfolding Shuffle_def
    by blast
  show " A \<parallel> B = B \<parallel> A "
    by (simp add:swap_alpha_and_beta add:B_par_A_is_def)
qed

lemma classifier_disjunction [simp] :
  " { x | x. x \<in> A \<or> x \<in> B} = { x | x. x \<in> A} \<union> { x | x. x \<in> B} "
  by auto

lemma distribute_classifier_disjunction [simp] :
  " { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
    { shuffles x y | x y. (x \<in> A) \<and> (y \<in> C) } \<union> 
    { shuffles x y | x y. (x \<in> B) \<and> (y \<in> C) }"
  by auto

lemma unfolded_set_union [simp] :
  " \<Union> {S | S. S \<in> A} = {x | x. \<exists> S. S \<in> A \<and> x \<in> S } "
  by auto

lemma distribute_folded_classifier_disjunction [simp] :
  " \<Union> { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
    \<Union> { shuffles x y | x y. (x \<in> A) \<and> (y \<in> C) } \<union> 
    \<Union> { shuffles x y | x y. (x \<in> B) \<and> (y \<in> C) }"
proof -
  have rewrite_left_hand :
    " \<Union> { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
        { x | x. \<exists> xs ys. xs \<in> (A \<union> B) \<and> ys \<in> C \<and> x \<in> shuffles xs ys } "
    by auto
  have distribute_rewritten_left_hand :
    " \<Union> { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
        { x | x. \<exists> xs ys. xs \<in> A \<and> ys \<in> C \<and> x \<in> shuffles xs ys } \<union>
        { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> shuffles xs ys } "
    by auto
  have and_what_is_that :
    " \<Union> { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
      \<Union> { shuffles x y | x y. x \<in> A \<and> y \<in> C } \<union>
        { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> shuffles xs ys } "
    by auto
  have how_about_the_rest : 
    "  { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> shuffles xs ys } = 
         \<Union> { shuffles x y | x y. x \<in> B \<and> y \<in> C } "
    by auto
  show
    " \<Union> { shuffles x y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
      \<Union> { shuffles x y | x y. x \<in> A \<and> y \<in> C } \<union>
      \<Union> { shuffles x y | x y. x \<in> B \<and> y \<in> C } "
    by (metis how_about_the_rest and_what_is_that)
qed

lemma left_par_distribution [simp] :
  " a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
proof -
  have " (b \<union> c) \<parallel> a = b \<parallel> a \<union> c \<parallel> a "
    unfolding Shuffle_def
    by (metis distribute_folded_classifier_disjunction)
  then have " (b \<union> c) \<parallel> a = a \<parallel> b \<union> a \<parallel> c "
    by (simp)
  then show " a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
    by (simp)
qed

lemma Shuffles_of_singletons_are_shuffles [simp] :
  " {\<alpha>} \<parallel> {\<beta>} = shuffles \<alpha> \<beta> "
  unfolding Shuffle_def
  by auto

lemma aux :
  " \<alpha> \<in> Shuffle A B \<and> \<gamma> \<in> Shuffle {\<alpha>} {\<beta>} \<Longrightarrow> \<gamma> \<in> (Shuffle (Shuffle A B) {\<beta>}) "
  unfolding Shuffle_def by blast

lemma shuffles_have_sources :
  " \<gamma> \<in> (A \<parallel> B) \<Longrightarrow> \<exists> \<alpha> \<beta>. \<gamma> \<in> shuffles \<alpha> \<beta> \<and> \<alpha> \<in> A \<and> \<beta> \<in> B "
  unfolding Shuffle_def
  by (auto)

lemma nested_shuffles_have_sources :
  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> shuffles \<eta> \<gamma> \<and> 
                              \<eta> \<in> shuffles \<alpha> \<beta> \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
proof -
  have without_nesting :
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<gamma> \<eta>.
                              \<delta> \<in> shuffles \<eta> \<gamma> \<and> 
                              \<eta> \<in> Shuffle A B \<and> 
                              \<gamma> \<in> C "
    by (metis shuffles_have_sources)
  show
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> shuffles \<eta> \<gamma> \<and> 
                              \<eta> \<in> shuffles \<alpha> \<beta> \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis without_nesting shuffles_have_sources)
qed

lemma nested_shuffles_have_singleton_sources :
  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
proof -
  (*
    have with eta
    eta has beta and gamma, by shuffles have sources (the binary one)
    have by {alpha} \<parallel> {beta} = alpha \<parallel> beta

  *)
  have " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> shuffles \<eta> \<gamma> \<and> 
                              \<eta> \<in> shuffles \<alpha> \<beta> \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis nested_shuffles_have_sources)
  then have " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> {\<eta>} \<parallel> {\<gamma>} \<and> 
                              \<eta> \<in> {\<alpha>} \<parallel> {\<beta>} \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (auto)
  then show  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis aux)
qed

(* Esto es impoggtante *)

(* shuffle is shuffle of singletons *)
lemma shuffles_are_shuffles_of_singletons [simp] :
  " A \<parallel> B = \<Union> { {\<alpha>} \<parallel> {\<beta>} | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
  unfolding Shuffle_def
  by auto

lemma unfolded_shuffle_of_nonempty_strings :
  " shuffles (x # xs) (y # ys) = (#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys "
  by auto

lemma nonempty_shuffles [simp] :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = shuffles (a#\<alpha>) (b#\<beta>) "
  unfolding Shuffle_def by auto

lemma ugly_unfolded_shuffle_of_singletons :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = (#) a ` (shuffles \<alpha> (b#\<beta>)) \<union> (#) b ` (shuffles (a#\<alpha>) \<beta>) "
  by (metis nonempty_shuffles unfolded_shuffle_of_nonempty_strings)

lemma concat_aux [simp] :
  " (#) a ` (A) = {[a]} @@ A "
  unfolding conc_def
  by auto

lemma unfolded_shuffle_of_singletons :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = {[a]} @@ (shuffles \<alpha> (b#\<beta>)) \<union> {[b]} @@ (shuffles (a#\<alpha>) \<beta>) "
  by (metis ugly_unfolded_shuffle_of_singletons concat_aux)

lemma singleton_as_concat [simp] :
  " {a#\<alpha>} = {[a]} @@ {\<alpha>} "
  unfolding conc_def
  by auto

lemma shuffle_of_heads_as_union :
  " {[a]} @@ A  \<parallel> {[b]} @@ B = 
      {[a]} @@ (A  \<parallel> {[b]} @@ B ) \<union> 
      {[b]} @@ ({[a]} @@ A  \<parallel> B)"
  sorry

(* Si alguno de todos es [], tooodo el shuffle es [] *)
(* Si ninguno es [], todos son de esta forma *)

(* Y el shuffle de no singletons es la unión de singleton shuffles *)

lemma shuffle_of_singletons_is_associative :
  " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =  ({a#\<alpha>} \<parallel> {b#\<beta>}) \<parallel> {c#\<gamma>} "
proof -
  have lhs_expansion :
    " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
        {a#\<alpha>} \<parallel> ( {[b]} @@ (shuffles \<beta> (c#\<gamma>)) \<union> 
        {[c]} @@ (shuffles (b#\<beta>) \<gamma>)) "
    by (metis unfolded_shuffle_of_singletons)
  then have lhs_distributed :
     " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
          {a#\<alpha>} \<parallel> ({[b]} @@ (shuffles \<beta> (c#\<gamma>))) \<union> 
          {a#\<alpha>} \<parallel> ({[c]} @@ (shuffles (b#\<beta>) \<gamma>)) "
    by (metis left_par_distribution) (* todo: rename with left_shuffle_union_distribution *)
  then have lhs_distributed_conc :
      " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
          {a#\<alpha>} \<parallel> ({[b]} @@ ({\<beta>} \<parallel> {c#\<gamma>})) \<union> 
          {a#\<alpha>} \<parallel> ({[c]} @@ ({b#\<beta>} \<parallel> {\<gamma>})) "
    by (metis Shuffles_of_singletons_are_shuffles)
  then have lhs_distributed_conc_singletons :
      " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
          ({[a]}@@{\<alpha>}) \<parallel> ({[b]} @@ ({\<beta>} \<parallel> {c#\<gamma>})) \<union> 
          ({[a]}@@{\<alpha>}) \<parallel> ({[c]} @@ ({b#\<beta>} \<parallel> {\<gamma>})) "
    by (metis singleton_as_concat)
  then have 
      " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
        {[a]} @@ ({\<alpha>} \<parallel> ({[b]} @@ ({\<beta>} \<parallel> {c#\<gamma>}))) \<union>
        {[b]} @@ ({a#\<alpha>} \<parallel> ({\<beta>} \<parallel> {c#\<gamma>})) \<union>
        {[a]} @@ ({\<alpha>} \<parallel> {[c]} @@ ({b#\<beta>} \<parallel> {\<gamma>})) \<union>
        {[c]} @@ ({a#\<alpha>} \<parallel> ({b#\<beta>} \<parallel> {\<gamma>})) "
    sorry
  show " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =  ({a#\<alpha>} \<parallel> {b#\<beta>}) \<parallel> {c#\<gamma>} "
    sorry
qed

lemma Shuffle_is_associative :
  " (A \<parallel> B) \<parallel> C = A \<parallel> (B \<parallel> C) "
  (* 
    * "shuffles have singleton sources"
    * And the shuffle of singletons is associative
    * So every string in LHS is a string in RHS, and viceversa
    * Hence both sets are equal
  *)

(*
  then have lhs_distributed_expansion :
    " {a#\<alpha>} \<parallel> ({b#\<beta>}  \<parallel> {c#\<gamma>}) =
        ({a#\<alpha>} \<parallel>  ((#) b ` (shuffles \<beta> (c#\<gamma>))) \<union> ({a#\<alpha>} \<parallel> (#) c ` (shuffles (b#\<beta>) \<gamma>))) "
    by (metis left_par_distribution)
  have rhs_flip :
    " ({a#\<alpha>} \<parallel> {b#\<beta>}) \<parallel> {c#\<gamma>} = {c#\<gamma>} \<parallel> ({a#\<alpha>} \<parallel> {b#\<beta>}) "
    by auto
  then have rhs__expansion :
    " ({a#\<alpha>} \<parallel> {b#\<beta>}) \<parallel> {c#\<gamma>} = 
        ((#) a ` (shuffles \<alpha> (b#\<beta>)) \<union> (#) b ` (shuffles (a#\<alpha>) \<beta>)) \<parallel> {c#\<gamma>} "
    by (metis Shuffle_of_singletons_bis)
  then have rhs_distributed_expansion :
    " ({a#\<alpha>} \<parallel> {b#\<beta>}) \<parallel> {c#\<gamma>} = 
        (((#) a ` (shuffles \<alpha> (b#\<beta>)) \<parallel> {c#\<gamma>}) \<union> ((#) b ` (shuffles (a#\<alpha>) \<beta>)) \<parallel> {c#\<gamma>}) "
    by auto
*)


(*
lemma forward_sources :
  " \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> 
      \<forall> \<delta> \<eta>. \<delta> \<in> shuffles \<beta> \<gamma> \<and> \<eta> \<in> shuffles \<alpha> \<delta> \<Longrightarrow> \<eta> \<in> (A \<parallel> (B \<parallel> C)) "


lemma "\<phi> \<in> (A \<parallel> (B \<parallel> C)) \<Longrightarrow> 
        \<exists> \<alpha> \<beta> \<gamma>.  \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> 
          \<exists> \<delta>. \<delta> \<in> (shuffles \<beta> \<gamma>) \<and> \<phi> \<in> shuffles \<delta> \<gamma> "
  unfolding Shuffle_def
proof
*)


interpretation
  union_concat_semiring :
    natural_order_semiring "{[]}" "(\<union>)" "(@@)" "{}" "(\<subseteq>)"
proof
  show " \<And>a b c. a \<union> b \<union> c = a \<union> (b \<union> c)"
    unfolding conc_def by auto
  show " \<And>a b c. (a @@ b) @@ c = a @@ b @@ c "
    unfolding conc_def by (metis conc_assoc conc_def)
  show " \<And>a. {[]} @@ a = a " by auto
  show " \<And>a. a @@ {[]} = a " by auto
  show " \<And>a b. a \<union> b = b \<union> a " by auto
  show " \<And>a. {} \<union> a = a " by auto
  show " \<And>a. {} @@ a = {} " by auto
  show " \<And>a. a @@ {} = {} " by auto
  show " \<And>a b c. (a \<union> b) @@ c = a @@ c \<union> b @@ c " by auto
  show " \<And>a b c. a @@ (b \<union> c) = a @@ b \<union> a @@ c " by auto
  show " {} \<noteq> {[]} " by auto
  show " \<And>a. a \<union> a = a " by auto
  show " \<And>a b. (a \<union> b = b) = (a \<subseteq> b) " by auto
  show " \<And>a b. a \<subseteq> b \<Longrightarrow> b \<subseteq> a \<Longrightarrow> a = b " by auto
  show " \<And>a b c. a \<subseteq> b \<and> b \<subseteq> c \<Longrightarrow> a \<subseteq> c " by auto
  show " \<And>a. a \<subseteq> a " by auto
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
    " \<And>a. a \<parallel> {} = {} "
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
    " \<And>a. a \<subseteq> a "
    by auto
  show
    " \<And>a b c. (a \<union> b) \<parallel> c = a \<parallel> c \<union> b \<parallel> c "
    unfolding Shuffle_def
    by (metis distribute_folded_classifier_disjunction)
  show
    " \<And>a b c. a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
    by (metis left_par_distribution)
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
    exchange :
    " (x || y) ; (1 || 1) \<sqsubseteq> (y ; 1) || (x ; 1) "
    by (metis exchange_law)
  then have
    simplify_ones :
    " (x || y ) \<sqsubseteq> (y || x) "
    by (simp)
  then have 
    swapped_exchange :
    " (y || x) ; (1 || 1) \<sqsubseteq> (x ; 1) || (y ; 1) "
    by (metis exchange_law)
  then have 
    swapped_simplify_ones :
    " (y || x ) \<sqsubseteq> (x || y) "
    by (simp)
  have 
    symmetric_order :
    "(y || x ) \<sqsubseteq> (x || y) \<and> (x || y ) \<sqsubseteq> (y || x) "
    by (metis swapped_simplify_ones simplify_ones)
  then show
    " (x || y) = (y || x) "
    by (metis parallel_quantale.leq_is_antisymmetric)
qed

lemma par_contains_seq :
  " x ; y \<sqsubseteq> x || y "
proof -
  have
    exchange :
    " (1 || x) ; (1 || y) \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (metis exchange_law)
  then have
    simplify_pars :
    " x ; y  \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (simp)
  then show
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
  show " \<And> \<alpha> A. \<alpha> \<parallel> \<Union> A =  \<Union> {\<alpha> \<parallel> \<beta> |\<beta>. \<beta> \<in> A} "
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