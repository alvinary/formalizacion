theory Concurrent_Kleene_Algebra
  imports Main HOL.Rings "Regular-Sets.Regular_Set"
begin

text \<open> Here we prove shuffle languages are concurrent
       Kleene algebras.  \<close>

text \<open> We begin by defining the familiar notation for
       the empty string, which in Isabelle is the empty list. \<close>

definition " \<epsilon> = [] "

text \<open> Next we define idempotent semirings. \<close>

text \<open> These are simply semirings that satisfy the additional
       condition that a \<oplus> a = a. \<close>

locale idempotent_semiring =
  semiring_1 one times plus zero for
    one :: "'a" and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" +
  assumes
    plus_is_idempotent [simp] :
      " a \<oplus> a = a "
begin

lemma plus_is_associative [ac_simps] : "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> c) "
  by (simp add:Groups.ac_simps)

lemma plus_is_commutative [ac_simps] : "a \<oplus> b = b \<oplus> a "
  by (simp add:Groups.ac_simps)

end


text \<open> When a semiring is idempotent, one may define a partial
       ordering over its elements such that a \<preceq> b iff a \<oplus> b = b. \<close>

text \<open> This partial order is called the natural ordering
       of a semiring because, in most familiar settings,
       it coincides with some noteworthy or natural 
       ordering over the underlying set. \<close>

text \<open> For instance, for the max-plus semiring, in which \<oplus> is
       the maximum of two real numbers and \<otimes> is the usual addition,
       the natural order is the usual less-than order, and for semirings
       whose elements are sets whose \<oplus> is set union, the natural order is
       inclusion. \<close>

text \<open> We define naturally ordered semirings as idempotent semirings 
       endowed with a relation \<preceq> that satisfies the expected a \<preceq> b 
       iff a \<oplus> b = b, and show then \<preceq> is a partial order. \<close>

locale natural_order_semiring =
  idempotent_semiring one plus times zero for
    one :: "'a" and
    plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) and
    times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80) and
    zero :: "'a" ("0") and
    leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 60) +
  assumes
    induced_natural_order :
      " a \<oplus> b = b \<longleftrightarrow> a \<preceq> b "
begin

  lemma leq_is_reflexive : " a \<preceq> a "
    by (metis induced_natural_order plus_is_idempotent)

  lemma leq_is_transitive : " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> a \<preceq> c "
    proof -
      have " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> a \<oplus> b = b \<and> b \<oplus> c = c "
        by (metis induced_natural_order)
      then have " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> (a \<oplus> b) \<oplus> c = c "
        by (auto)
      then have " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> a \<oplus> (b \<oplus> c) = c "
        by (metis plus_is_associative)
      then show " a \<preceq> b \<and> b \<preceq> c \<Longrightarrow> a \<preceq> c "
        by (metis induced_natural_order)
    qed

lemma leq_is_antisymmetric : " a \<preceq> b \<and> b \<preceq> a \<Longrightarrow> a = b "
  using leq_is_transitive induced_natural_order
  proof -
    have " a \<preceq> b \<and> b \<preceq> a \<Longrightarrow> a \<oplus> b = b \<and> b \<oplus> a = a " 
      by (metis induced_natural_order)
    then have " a \<preceq> b \<and> b \<preceq> a \<Longrightarrow> a \<oplus> b = b \<and> a \<oplus> b = a "
      by (metis plus_is_commutative)
    then show " a \<preceq> b \<and> b \<preceq> a \<Longrightarrow> a = b " by auto
  qed  
    
end

text \<open> Now we introduce two operations on languages, 
       concatenation and shuffling, and prove a number
       of auxiliary properties about them. \<close>

notation conc (infixl ";" 70)
notation append (infixl "." 60)
notation shuffles (infixl "\<diamondop>" 60)

lemma concatenation_is_associative [simp] :
  " (\<alpha> . \<beta>) . \<gamma> = \<alpha> . (\<beta> . \<gamma>) "
  by auto

lemma shuffle_is_commutative [simp] :
  " \<alpha> \<diamondop> \<beta> = \<beta> \<diamondop> \<alpha> "
  by (metis shuffles_commutes)

lemma Shuffle_is_commutative [simp] :
  " A \<parallel> B = B \<parallel> A "
proof -
  have " A \<parallel> B = \<Union> { \<alpha> \<diamondop> \<beta> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
    unfolding Shuffle_def
    by auto
  then have swap_alpha_and_beta :
    " A \<parallel> B = \<Union> { \<beta> \<diamondop> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
    by (simp)
  have B_par_A_is_def :
    " B \<parallel> A = \<Union> { \<beta> \<diamondop> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B  } "
    unfolding Shuffle_def
    by blast
  show " A \<parallel> B = B \<parallel> A "
    by (simp add:swap_alpha_and_beta add:B_par_A_is_def)
qed

lemma classifier_disjunction :
  " { \<alpha> | \<alpha>. \<alpha> \<in> A \<or> \<alpha> \<in> B} = { \<alpha> | \<alpha>. \<alpha> \<in> A} \<union> { \<alpha> | \<alpha>. \<alpha> \<in> B} "
  by auto

lemma distribute_classifier_disjunction :
  " { \<alpha> \<diamondop> \<beta> | \<alpha> \<beta>. (\<alpha> \<in> A \<union> B) \<and> (\<beta> \<in> C) } = 
    { \<alpha> \<diamondop> \<beta> | \<alpha> \<beta>. (\<alpha> \<in> A) \<and> (\<beta> \<in> C) } \<union> 
    { \<alpha> \<diamondop> \<beta> | \<alpha> \<beta>. (\<alpha> \<in> B) \<and> (\<beta> \<in> C) }"
  by auto

lemma unfolded_set_union :
  " \<Union> {S | S. S \<in> A} = {x | x. \<exists> S. S \<in> A \<and> x \<in> S } "
  by auto

lemma distribute_folded_classifier_disjunction [simp] :
  " \<Union> { x \<diamondop> y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
    \<Union> { x \<diamondop> y | x y. (x \<in> A) \<and> (y \<in> C) } \<union> 
    \<Union> { x \<diamondop> y | x y. (x \<in> B) \<and> (y \<in> C) }"
proof -
  have
    " \<Union> { x \<diamondop> y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
        { x | x. \<exists> xs ys. xs \<in> (A \<union> B) \<and> ys \<in> C \<and> x \<in> xs \<diamondop> ys } "
    by auto
  have
    " \<Union> { x \<diamondop> y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
        { x | x. \<exists> xs ys. xs \<in> A \<and> ys \<in> C \<and> x \<in> xs \<diamondop> ys } \<union>
        { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> xs \<diamondop> ys } "
    by auto
  have and_what_is_that :
    " \<Union> { x \<diamondop> y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
      \<Union> { x \<diamondop> y | x y. x \<in> A \<and> y \<in> C } \<union>
        { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> xs \<diamondop> ys } "
    by auto
  then have how_about_the_rest : 
    "  { x | x. \<exists> xs ys. xs \<in> B \<and> ys \<in> C \<and> x \<in> xs \<diamondop> ys } = 
         \<Union> { x \<diamondop> y | x y. x \<in> B \<and> y \<in> C } "
    by auto
  then show
    " \<Union> { x \<diamondop> y | x y. (x \<in> A \<union> B) \<and> (y \<in> C) } = 
      \<Union> { x \<diamondop> y | x y. x \<in> A \<and> y \<in> C } \<union>
      \<Union> { x \<diamondop> y | x y. x \<in> B \<and> y \<in> C } "
    by (metis how_about_the_rest and_what_is_that)
qed

lemma left_par_distribution :
  " a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
proof -
  have 
    " (b \<union> c) \<parallel> a = b \<parallel> a \<union> c \<parallel> a "
    unfolding Shuffle_def
    by (metis distribute_folded_classifier_disjunction)
  then have 
    " (b \<union> c) \<parallel> a = a \<parallel> b \<union> a \<parallel> c "
    by (simp)
  then show 
    " a \<parallel> (b \<union> c) = a \<parallel> b \<union> a \<parallel> c "
    by (simp)
qed

lemma Shuffles_of_singletons_are_shuffles :
  " {\<alpha>} \<parallel> {\<beta>} = \<alpha> \<diamondop> \<beta> "
  unfolding Shuffle_def
  by auto

lemma aux :
  " \<alpha> \<in> A \<parallel> B \<and> \<gamma> \<in> {\<alpha>} \<parallel> {\<beta>} \<Longrightarrow> \<gamma> \<in> ( (A \<parallel> B) \<parallel> {\<beta>}) "
  unfolding Shuffle_def by blast

lemma shuffles_have_sources :
  " \<gamma> \<in> (A \<parallel> B) \<Longrightarrow> \<exists> \<alpha> \<beta>. \<gamma> \<in> \<alpha> \<diamondop> \<beta> \<and> \<alpha> \<in> A \<and> \<beta> \<in> B "
  unfolding Shuffle_def
  by (auto)

lemma nested_shuffles_have_sources :
  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> \<eta> \<diamondop> \<gamma> \<and> 
                              \<eta> \<in> \<alpha> \<diamondop> \<beta> \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
proof -
  have without_nesting :
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<gamma> \<eta>.
                              \<delta> \<in> \<eta> \<diamondop> \<gamma> \<and> 
                              \<eta> \<in> A \<parallel> B \<and> 
                              \<gamma> \<in> C "
    by (metis shuffles_have_sources)
  show
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> \<eta> \<diamondop> \<gamma> \<and> 
                              \<eta> \<in> \<alpha> \<diamondop> \<beta> \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis without_nesting shuffles_have_sources)
qed

lemma nested_shuffles_have_singleton_sources :
  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
proof -
  have " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> \<eta> \<diamondop> \<gamma> \<and> 
                              \<eta> \<in> \<alpha> \<diamondop> \<beta> \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis nested_shuffles_have_sources)
  then have " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma> \<eta>.
                              \<delta> \<in> {\<eta>} \<parallel> {\<gamma>} \<and> 
                              \<eta> \<in> {\<alpha>} \<parallel> {\<beta>} \<and>
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis Shuffles_of_singletons_are_shuffles)
  then show  " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis aux)
qed

lemma shuffles_are_shuffles_of_singletons :
  " A \<parallel> B = \<Union> { {\<alpha>} \<parallel> {\<beta>} | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
  unfolding Shuffle_def
  by auto

lemma unfolded_shuffle_of_nonempty_strings :
  " (x # xs) \<diamondop> (y # ys) = (#) x ` (xs \<diamondop> (y # ys)) \<union> (#) y ` ( (x # xs) \<diamondop> ys) "
  by auto

lemma nonempty_shuffles [simp] :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = (a#\<alpha>) \<diamondop> (b#\<beta>) "
  unfolding Shuffle_def by auto

lemma ugly_unfolded_shuffle_of_singletons :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = (#) a ` (\<alpha> \<diamondop> (b#\<beta>)) \<union> (#) b ` ((a#\<alpha>) \<diamondop> \<beta>) "
  by (metis nonempty_shuffles unfolded_shuffle_of_nonempty_strings)

lemma concat_aux [simp] :
  " (#) a ` (A) = {[a]} ; A "
  unfolding conc_def
  by auto

lemma unfolded_shuffle_of_singletons :
  " {a#\<alpha>} \<parallel> {b#\<beta>} = {[a]} ; (\<alpha> \<diamondop> (b#\<beta>)) \<union> {[b]} ; ((a#\<alpha>) \<diamondop> \<beta>) "
  by (metis ugly_unfolded_shuffle_of_singletons concat_aux)

lemma singleton_as_concat [simp] :
  " {a#\<alpha>} = {[a]} ; {\<alpha>} "
  unfolding conc_def
  by auto

lemma empty_is_shuffle_neuter : 
  " \<alpha> \<diamondop> \<epsilon> = {\<alpha>} "
  unfolding Shuffle_def \<epsilon>_def by auto

lemma superaux : " A \<parallel> (B \<parallel> C)  = \<Union> { {xs} \<parallel> {ys} | xs ys.
            xs \<in> A \<and>
            ys \<in> \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> B \<and> ys \<in> C } } "
  unfolding Shuffle_def
  by auto

lemma superaux_2 :
  " \<delta> \<in>  \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> A \<and> ys \<in> \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> B \<and> ys \<in> C } }  \<Longrightarrow> 
              \<delta> \<in> A \<parallel> (B \<parallel> C)  "
  unfolding Shuffle_def
  by auto

lemma singleton_sources_are_in_shuffles :
  " \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> \<delta> \<in> A \<parallel> (B \<parallel> C) "
  unfolding Shuffle_def
  by fast

lemma singleton_sources_are_in_shuffles_left :
  " \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> \<delta> \<in> (A \<parallel> B) \<parallel> C "
  unfolding Shuffle_def
  by fast

lemma shuffle_of_singletons_is_associative :
  " {\<alpha>} \<parallel> ({\<beta>}  \<parallel> {\<gamma>}) =  ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} "
  unfolding Shuffle_def
  sorry

lemma subsets_lemma : " (\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B "
  by auto

lemma matching_sets_lemma : " a \<in> A \<and> A = B \<Longrightarrow> a \<in> B "
  by auto

lemma Shuffle_is_associative :
  " (A \<parallel> B) \<parallel> C = A \<parallel> (B \<parallel> C) "
proof
  have " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis nested_shuffles_have_singleton_sources)
  then have haha :
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis shuffle_of_singletons_is_associative)
  then have
    " \<delta> \<in> (A \<parallel> B) \<parallel> C  \<Longrightarrow> \<delta> \<in> A \<parallel> (B \<parallel> C) "
    by (meson singleton_sources_are_in_shuffles)
  then have left_in_right : " (A \<parallel> B) \<parallel> C \<subseteq>  A \<parallel> (B \<parallel> C) " 
    using nested_shuffles_have_singleton_sources 
          shuffle_of_singletons_is_associative
          singleton_sources_are_in_shuffles
    by blast
  have " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    using
      nested_shuffles_have_singleton_sources
    by fastforce
  then have haha :
    " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis shuffle_of_singletons_is_associative)
  then have
    " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<delta> \<in> (A \<parallel> B) \<parallel> C "
     by (meson singleton_sources_are_in_shuffles_left)
   then have right_in_left : 
      " A \<parallel> (B \<parallel> C) \<subseteq>  (A \<parallel> B) \<parallel> C "
     by (smt 
          (verit, ccfv_threshold)
            Shuffle_is_commutative
            nested_shuffles_have_singleton_sources
            shuffle_of_singletons_is_associative
            singleton_sources_are_in_shuffles
            subsets_lemma)
  
   show " (A \<parallel> B) \<parallel> C \<subseteq> A \<parallel> (B \<parallel> C) "
     by (metis left_in_right)
   show " A \<parallel> (B \<parallel> C) \<subseteq> (A \<parallel> B) \<parallel> C "
     by (metis right_in_left)
qed

interpretation
  union_concat_semiring :
    natural_order_semiring "{\<epsilon>}" "(\<union>)" "(;)" "{}" "(\<subseteq>)"
proof
  show " \<And> A B C. A \<union> B \<union> C = A \<union> (B \<union> C)"
    unfolding conc_def by auto
  show " \<And> A B C. (A ; B) ; C = A ; (B ; C) "
    unfolding conc_def by (metis conc_assoc conc_def)
  show " \<And> A. {\<epsilon>} ; A = A " unfolding \<epsilon>_def by auto
  show " \<And> A. A ; {\<epsilon>} = A " unfolding \<epsilon>_def by auto
  show " \<And> A B. A \<union> B = B \<union> A " by auto
  show " \<And> A. {} \<union> A = A " by auto
  show " \<And> A. {} ; A = {} " by auto
  show " \<And> A. A ; {} = {} " by auto
  show " \<And> A B C. (A \<union> B) ; C = A ; C \<union> B ; C " by auto
  show " \<And> A B C. A ; (B \<union> C) = A ; B \<union> A ; C " by auto
  show " {} \<noteq> {\<epsilon>} " by auto
  show " \<And> A. A \<union> A = A " by auto
  show " \<And> A B. (A \<union> B = B) = (A \<subseteq> B) " by auto
qed

interpretation
  union_shuffle_semiring :
    natural_order_semiring "{\<epsilon>}" "(\<union>)" "(\<parallel>)" "{}" "(\<subseteq>)"
proof
  show
    " \<And> A B C. (A \<parallel> B) \<parallel> C =  A \<parallel> B \<parallel> C "
    by (metis Shuffle_is_associative)
  show
    " \<And> A. {} \<parallel> A = {} "
    by auto
  show
    " \<And> A. A \<parallel> {} = {} "
    by auto
  show
    " \<And> A. A \<union> A = A "
    by auto
  show
    " \<And> A B. (A \<union> B = B) = (A \<subseteq> B) "
    by auto
  show 
    " \<And> A. {\<epsilon>} \<parallel> A = A "
    unfolding \<epsilon>_def by auto
  show
    " \<And> A. A \<parallel> {\<epsilon>} = A "
    unfolding \<epsilon>_def by auto
  show
    " \<And>a b c. (a \<union> b) \<parallel> c = a \<parallel> c \<union> b \<parallel> c "
    unfolding Shuffle_def
    by (metis distribute_folded_classifier_disjunction)
  show
    " \<And> A B C. A \<parallel> (B \<union> C) = A \<parallel> B \<union> A \<parallel> C "
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
    " (x || y) ; (1 || 1) \<sqsubseteq> (y ; 1) || (x ; 1) "
    by (metis exchange_law)
  then have
    simplify_ones :
    " (x || y ) \<sqsubseteq> (y || x) "
    by (simp)
  then have " (y || x) ; (1 || 1) \<sqsubseteq> (x ; 1) || (y ; 1) "
    by (metis exchange_law)
  then have swapped_simplify_ones :
    " (y || x ) \<sqsubseteq> (x || y) "
    by (simp)
  have  "(y || x ) \<sqsubseteq> (x || y) \<and> (x || y ) \<sqsubseteq> (y || x) "
    by (metis swapped_simplify_ones simplify_ones)
  then show " (x || y) = (y || x) "
    by (metis parallel_quantale.leq_is_antisymmetric)
qed

lemma par_contains_seq :
  " x ; y \<sqsubseteq> x || y "
proof -
  have " (1 || x) ; (1 || y) \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (metis exchange_law)
  then have " x ; y  \<sqsubseteq> (x ; 1) || (1 ; y) "
    by (simp)
  then show " x ; y  \<sqsubseteq> x || y "
    by (simp)
qed

lemma alternative_exchange :
  "(x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w) "
proof -
  have "(y || x) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w)"
    by (metis exchange_law)
  then show "(x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w)"
    by (metis par_is_commutative)
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
  quantale "{\<epsilon>}" "(\<union>)" "(;)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show " \<And> a A. a ; \<Union> A = \<Union> {a ; x |x. x \<in> A} "
    unfolding conc_def
    by auto
  show  " \<And> x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x"
    by auto
qed

interpretation union_shuffle_quantale :
  quantale "{\<epsilon>}" "(\<union>)" "(\<parallel>)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show  " \<And> \<alpha> A. \<alpha> \<parallel> \<Union> A =  \<Union> {\<alpha> \<parallel> \<beta> |\<beta>. \<beta> \<in> A} "
    unfolding Shuffle_def
    by auto
  show  "  \<And> x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x "
    unfolding Shuffle_def
    by auto
qed

interpretation shuffle_languages_cka :
  concurrent_kleene_algebra "{\<epsilon>}" "(\<union>)" "(;)" "(\<parallel>)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show "  \<And> A B C D. A \<parallel> B ; C \<parallel> D \<subseteq> (B ; C) \<parallel> (A ; D) "
    unfolding Shuffle_def conc_def
    sorry
qed

end