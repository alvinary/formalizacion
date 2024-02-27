theory Concurrent_Kleene_Algebra
  imports Main HOL.Rings "Regular-Sets.Regular_Set" HOL.List
begin

text \<open> Here we prove shuffle languages are concurrent Kleene algebras. \<close>

text \<open> Kleene algebras were early models of program semantics. They are similar to
       dynamic and temporal logics, in that they model any  given program as a set 
       of execution paths. \<close>

text \<open> Unlike dynamic logics, which model properties and execution paths separately
       (and in which both programs and properties are syntactically and semantically
       very different objects), Kleene algebras do not distinguish between facts or
       propositions and programs. \<close>

text \<open> Sequential and concurrent composition - semirings or dioids (some authors
       use the term dioid, some others...) \<close>

text \<open> Sequential and concurrent composition \<close>

text \<open> Concurrent Kleene algebras have two notable models: sets of words and sets of
       traces. \<close>

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
  then have commute_alpha_and_beta :
    " A \<parallel> B = \<Union> { \<beta> \<diamondop> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B } "
    by (simp)
  have B_par_A_is_def :
    " B \<parallel> A = \<Union> { \<beta> \<diamondop> \<alpha> | \<alpha> \<beta> . \<alpha> \<in> A \<and> \<beta> \<in> B  } "
    unfolding Shuffle_def
    by blast
  show " A \<parallel> B = B \<parallel> A "
    by (simp add:commute_alpha_and_beta add:B_par_A_is_def)
qed

lemma classifier_disjunction :
  " { \<alpha> | \<alpha>. \<alpha> \<in> A \<or> \<alpha> \<in> B} = { \<alpha> | \<alpha>. \<alpha> \<in> A} \<union> { \<alpha> | \<alpha>. \<alpha> \<in> B} "
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

lemma singleton_shuffle_union : " A \<parallel> (B \<parallel> C)  = \<Union> { {xs} \<parallel> {ys} | xs ys.
            xs \<in> A \<and>
            ys \<in> \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> B \<and> ys \<in> C } } "
  unfolding Shuffle_def
  by auto

lemma singleton_shuffle_union_elem :
  " \<delta> \<in>  \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> A \<and> ys \<in> \<Union> { {xs} \<parallel> {ys} | xs ys. xs \<in> B \<and> ys \<in> C } }  \<Longrightarrow> 
              \<delta> \<in> A \<parallel> (B \<parallel> C)  "
  unfolding Shuffle_def
  by auto

lemma singleton_sources_are_in_shuffles_right :
  " \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> \<delta> \<in> A \<parallel> (B \<parallel> C) "
  unfolding Shuffle_def
  by fast

lemma singleton_sources_are_in_shuffles_left :
  " \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C \<Longrightarrow> \<delta> \<in> (A \<parallel> B) \<parallel> C "
  unfolding Shuffle_def
  by fast

(* Indexing permutations *)

datatype choice = L | R
datatype mixed_choice = LL | LR | RR

fun chooseOn :: " choice list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list  " where
"chooseOn [] _ _ = []" |
"chooseOn _ [] ys = ys" |
"chooseOn _ xs [] = xs" |
"chooseOn (L#ls) (x#xs) ys = x#(chooseOn ls xs ys)" |
"chooseOn (R#ls) xs (y#ys) = y#(chooseOn ls xs ys)"

fun mixedChooseOn :: " mixed_choice list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list " where
" mixedChooseOn [] _ _ _ = [] " |
" mixedChooseOn (LL#cs) (x#xs) ys zs = x#(mixedChooseOn cs xs ys zs) " |
" mixedChooseOn (LR#cs) xs (y#ys) zs = y#(mixedChooseOn cs xs ys zs) " |
" mixedChooseOn (RR#cs) xs ys (z#zs) = z#(mixedChooseOn cs xs ys zs) " |
" mixedChooseOn _ _ _ _ = [] "

fun factorial :: "nat \<Rightarrow> nat" where
"factorial 0 = 1 " |
"factorial (Suc n) = (Suc n) * (factorial n)"

fun previous_factorial :: "'a list \<Rightarrow> nat" where
" previous_factorial [] = 1 " |
" previous_factorial (x#xs) = (factorial (length xs)) "

fun element_index :: "nat \<Rightarrow> 'a list \<Rightarrow> nat " where
" element_index n xs = (n div (previous_factorial xs)) "

fun insert_in_between :: " nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list " where
" insert_in_between n x xs = take n xs @ [x] @ drop n xs "

fun nth_permutation :: " nat \<Rightarrow> 'a list \<Rightarrow> 'a list " where
" nth_permutation n [] = [] " |
" nth_permutation n (x#xs) =
      insert_in_between
        (element_index n (x#xs))
         x
        (nth_permutation
              (n mod (previous_factorial (x#xs)))
               xs) "

fun base_left :: " 'a list \<Rightarrow> choice list " where
" base_left [] = [] " |
" base_left (a#\<alpha>) = L#(base_left \<alpha>) "

fun base_right :: " 'a list \<Rightarrow> choice list " where
" base_right [] = [] " |
" base_right (a#\<alpha>) = R#(base_right \<alpha>) "

fun base_choice :: " 'a list \<Rightarrow> 'a list \<Rightarrow> choice list " where
" base_choice \<alpha> \<beta> = base_left \<alpha> @ base_right \<beta> "

fun nth_choice :: " nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> choice list " where
" nth_choice n \<alpha> \<beta> = nth_permutation n (base_choice \<alpha> \<beta>) "

(*  *)

fun count_left :: " choice list \<Rightarrow> nat " where
" count_left [] = 0 " |
" count_left (L#cs) = 1 + count_left cs " | 
" count_left (R#cs) = count_left cs "

fun count_right :: " choice list \<Rightarrow> nat " where
" count_right [] = 0 " |
" count_right (L#cs) = count_right cs " | 
" count_right (R#cs) = 1 + count_right cs "

lemma base_left_length :
  fixes \<alpha>
  shows " count_left (base_left \<alpha>) = length \<alpha> "
proof (induct \<alpha>)
  show " count_left (base_left []) = length [] "
    by simp
  show " \<And>a \<alpha>. count_left (base_left \<alpha>) =
           length \<alpha> \<Longrightarrow>
           count_left
            (base_left (a # \<alpha>)) =
           length (a # \<alpha>) "
    by auto
qed

lemma base_right_length :
  fixes \<alpha>
  shows " count_right (base_right \<alpha>) = length \<alpha> "
proof (induct \<alpha>)
  show " count_right (base_right []) = length [] "
    by simp
  show " \<And>a \<alpha>. count_right (base_right \<alpha>) =
           length \<alpha> \<Longrightarrow>
           count_right
            (base_right (a # \<alpha>)) =
           length (a # \<alpha>) "
    by auto
qed

lemma append_left_left_count :
  " (count_left \<alpha>) = n \<Longrightarrow> count_left (L#\<alpha>) = 1 + n "
  by auto

lemma append_right_left_count :
  " (count_left \<alpha>) = n \<Longrightarrow> (count_left (R#\<alpha>)) = n "
  by auto

lemma append_left_right_count :
  " (count_right \<alpha>) = n \<Longrightarrow> count_right (L#\<alpha>) = n"
  by auto

lemma append_right_right_count :
  " (count_right \<alpha>) = n \<Longrightarrow> count_right (R#\<alpha>) = 1 + n"
  by auto

fun match :: " choice list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool " where
  " match [] [] [] = True " |
  " match [] (a#\<alpha>) _ = False " |
  " match [] _ (b#\<beta>) = False " |
  " match (L#cs) [] _ = False " |
  " match (R#cs) _ [] = False " |
  " match (L#cs) (a#\<alpha>) \<beta> = match cs \<alpha> \<beta> " |
  " match (R#cs) \<alpha> (b#\<beta>) = match cs \<alpha> \<beta> "

lemma empty_match :
  " match [] \<alpha> \<beta> \<Longrightarrow> \<alpha> = [] \<and> \<beta> = []"
  using match.elims(2) by auto

lemma choose_on_append_left :
  " chooseOn cs \<alpha> \<beta> \<in> \<alpha> \<diamondop> \<beta> \<Longrightarrow> 
    chooseOn (L#cs) (a#\<alpha>) \<beta> \<in> (a#\<alpha>) \<diamondop> \<beta> "
  by (metis 
        (no_types, opaque_lifting)
        Cons_in_shuffles_leftI  
        \<epsilon>_def
        chooseOn.simps(3)
        chooseOn.simps(4)
        empty_is_shuffle_neuter
        list.exhaust singletonI)

lemma choose_on_append_right :
  " chooseOn cs \<alpha> \<beta> \<in> \<alpha> \<diamondop> \<beta> \<Longrightarrow> 
    chooseOn (R#cs) \<alpha> (b#\<beta>) \<in> \<alpha> \<diamondop> (b#\<beta>) "
  by (metis 
        Cons_in_shuffles_rightI
        chooseOn.simps(2)
        chooseOn.simps(5)
        neq_Nil_conv
        shuffles.simps(1)
        singletonI)

lemma choose_on_plus_cases_l :
  " count_left cs = length \<alpha> \<Longrightarrow> count_left (L#cs) = length (a # \<alpha>)"
  by auto

lemma choose_on_plus_cases_r :
  " count_right cs = length \<alpha> \<Longrightarrow> count_right (R#cs) = length (a # \<alpha>)"
  by auto

lemma matching_choices_in_shuffles :
 " count_left cs = length \<alpha> \<and> count_right cs = length \<beta> \<Longrightarrow> chooseOn cs \<alpha> \<beta> \<in> \<alpha> \<diamondop> \<beta> "
  sorry
(*
proof -
  have " count_left [] = length [] 
       \<and> count_right [] = length []
     \<Longrightarrow> chooseOn [] [] [] \<in> [] \<diamondop> [] "
    by simp
  have "    (count_left cs) = (length \<alpha>)
          \<and> (count_right cs) = (length \<beta>) 
          \<and> chooseOn cs \<alpha> \<beta> \<in> \<alpha> \<diamondop> \<beta> \<Longrightarrow>
            chooseOn (L#cs) (a#\<alpha>) \<beta> \<in> (a#\<alpha>) \<diamondop> \<beta> 
          \<and> count_left (L#cs) = length (a#\<alpha>)
          \<and> count_right (L#cs) = length \<beta>  "
    using choose_on_append_left by fastforce
   have "    (count_left cs) = (length \<alpha>)
          \<and> (count_right cs) = (length \<beta>) 
          \<and> chooseOn cs \<alpha> \<beta> \<in> \<alpha> \<diamondop> \<beta> \<Longrightarrow>
            chooseOn (R#cs) \<alpha> (b#\<beta>) \<in> \<alpha> \<diamondop> (b#\<beta>) 
          \<and> count_left (R#cs) = length \<alpha>
          \<and> count_right (R#cs) = length (b#\<beta>)  "
     using choose_on_append_right by fastforce
*)
    

lemma matching_choices_in_singleton_shuffles :
 " count_left cs = length \<alpha> \<and> count_right cs = length \<beta> \<Longrightarrow> chooseOn cs \<alpha> \<beta> \<in> {\<alpha>} \<parallel> {\<beta>} "
  unfolding Shuffle_def
  using matching_choices_in_shuffles
  by auto

lemma matching_choices_in_nested_shuffles :
  " count_left cs = length \<alpha> + length \<beta> \<and>
        count_right cs = length \<gamma> \<and> 
        count_left ds = length \<alpha> \<and>
        count_right ds = length \<beta> \<Longrightarrow>
        chooseOn cs (chooseOn ds \<alpha> \<beta>) \<gamma> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel>  {\<gamma>} "
proof -
  have " count_left ds = length \<alpha> \<and>
           count_right ds = length \<beta> \<and>
           count_left cs = length \<alpha> + length \<beta> \<and>
           count_right cs = length \<gamma> \<Longrightarrow> (chooseOn ds \<alpha> \<beta>) \<in> ({\<alpha>} \<parallel> {\<beta>}) " 
    using matching_choices_in_singleton_shuffles
    by auto
  then have "count_left ds = length \<alpha> \<and>
           count_right ds = length \<beta> \<and>
           count_left cs = length \<alpha> + length \<beta> \<and>
           count_right cs = length \<gamma> \<Longrightarrow> 
           chooseOn cs (chooseOn ds \<alpha> \<beta>) \<gamma> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel>  {\<gamma>} "
    using
        aux 
        length_shuffles
        matching_choices_in_shuffles
        matching_choices_in_singleton_shuffles
    by metis
  then show " count_left cs =
    length \<alpha> + length \<beta> \<and>
    count_right cs = length \<gamma> \<and>
    count_left ds = length \<alpha> \<and>
    count_right ds = length \<beta> \<Longrightarrow>
    chooseOn cs (chooseOn ds \<alpha> \<beta>) \<gamma>
    \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} "
    by auto
qed

(* End of indexing lemmas *)

lemma associativity_base :
  "  {[]} \<parallel> ({[]}  \<parallel> {[]}) =  ({[]} \<parallel> {[]}) \<parallel> {[]} "
  by simp

(*
lemma associativity_rec :
  "  {a#as} \<parallel> ({b#bs}  \<parallel> {c#cs}) =  ({a#as} \<parallel> {b#bs}) \<parallel> {c#cs} "
proof -
  have " {b#bs}  \<parallel> {c#cs} = {[b]};({bs} \<parallel> {c#cs}) \<union> {[c]};({b#bs} \<parallel> {cs}) "
    by (metis Shuffles_of_singletons_are_shuffles unfolded_shuffle_of_singletons)   
  then have " {a#as} \<parallel> ({b#bs}  \<parallel> {c#cs}) = 
                      {a#as} \<parallel> ({[b]};({bs} \<parallel> {c#cs}) \<union> {[c]};({b#bs} \<parallel> {cs})) "
*)

lemma shuffle_of_singletons_is_associative :
  " {\<alpha>} \<parallel> ({\<beta>}  \<parallel> {\<gamma>}) =  ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} "
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
  then have
    " \<delta> \<in> ((A \<parallel> B) \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis shuffle_of_singletons_is_associative)
  then have
    " \<delta> \<in> (A \<parallel> B) \<parallel> C  \<Longrightarrow> \<delta> \<in> A \<parallel> (B \<parallel> C) "
    by (meson singleton_sources_are_in_shuffles_right)
  then show " (A \<parallel> B) \<parallel> C \<subseteq>  A \<parallel> (B \<parallel> C) " 
    using nested_shuffles_have_singleton_sources 
          shuffle_of_singletons_is_associative
          singleton_sources_are_in_shuffles_right
    by blast
  have " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> {\<alpha>} \<parallel> ({\<beta>} \<parallel> {\<gamma>}) \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    using
      nested_shuffles_have_singleton_sources
    by fastforce
  then have
    " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<exists> \<alpha> \<beta> \<gamma>.
                              \<delta> \<in> ({\<alpha>} \<parallel> {\<beta>}) \<parallel> {\<gamma>} \<and> 
                              \<alpha> \<in> A \<and> \<beta> \<in> B \<and> \<gamma> \<in> C "
    by (metis shuffle_of_singletons_is_associative)
  then have
    " \<delta> \<in> A \<parallel> (B \<parallel> C)  \<Longrightarrow> \<delta> \<in> (A \<parallel> B) \<parallel> C "
     by (meson singleton_sources_are_in_shuffles_left)
   then show right_in_left : 
      " A \<parallel> (B \<parallel> C) \<subseteq>  (A \<parallel> B) \<parallel> C "
     by (smt 
          (verit, ccfv_threshold)
            Shuffle_is_commutative
            nested_shuffles_have_singleton_sources
            shuffle_of_singletons_is_associative
            singleton_sources_are_in_shuffles_right
            subsets_lemma)
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
    unfolding Shuffle_def by (metis distribute_folded_classifier_disjunction)
  show
    " \<And> A B C. A \<parallel> (B \<union> C) = A \<parallel> B \<union> A \<parallel> C "
    using left_par_distribution by auto
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
    using exchange_law by blast
  then have swapped_simplify_ones :
    " (y || x ) \<sqsubseteq> (x || y) "
    by (simp)
  have  "(y || x ) \<sqsubseteq> (x || y) \<and> (x || y ) \<sqsubseteq> (y || x) "
    using swapped_simplify_ones simplify_ones by auto
  then show " (x || y) = (y || x) "
    using parallel_quantale.leq_is_antisymmetric by auto
qed

lemma par_contains_seq :
  " x ; y \<sqsubseteq> x || y "
proof -
  have " (1 || x) ; (1 || y) \<sqsubseteq> (x ; 1) || (1 ; y) "
    using exchange_law by blast
  then have " x ; y  \<sqsubseteq> (x ; 1) || (1 ; y) "
    by simp
  then show " x ; y  \<sqsubseteq> x || y "
    by simp
qed

lemma alternative_exchange :
  " (x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w) "
proof -
  have " (y || x) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w) "
    using exchange_law by auto
  then show " (x || y) ; (z || w) \<sqsubseteq> (x ; z) || (y ; w) "
    using par_is_commutative by auto
qed

lemma par_extraction :
  " (x || y) ; z \<sqsubseteq> x || (y ; z) "
proof -
  have partial_exchange :
    " (x || y) ; (1 || z) \<sqsubseteq> (x ; 1) || (y ; z) "
    using alternative_exchange by blast
  then show " (x || y) ; z \<sqsubseteq> x || (y ; z) "
    by simp
qed

lemma seq_extraction :
  " (x || y) ; z \<sqsubseteq> x || (y ; z) "
proof -
  have partial_alternative :
    " (x || y) ; (1 || z) \<sqsubseteq> (x ; 1) || (y ; z) "
    using alternative_exchange by blast
  then show " (x || y) ; z \<sqsubseteq> x || (y ; z) "
    by simp
qed

lemma par_is_associative [simp] :
  "(x || y) || z = x || (y || z)"
  using parallel_quantale.mult_assoc by auto

end

interpretation union_concatenation_quantale :
  quantale "{\<epsilon>}" "(\<union>)" "(;)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show " \<And> a A. a ; \<Union> A = \<Union> {a ; x |x. x \<in> A} "
    unfolding conc_def by auto
  show  " \<And> x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x"
    by auto
qed

interpretation union_shuffle_quantale :
  quantale "{\<epsilon>}" "(\<union>)" "(\<parallel>)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show  " \<And> \<alpha> A. \<alpha> \<parallel> \<Union> A =  \<Union> {\<alpha> \<parallel> \<beta> | \<beta>. \<beta> \<in> A} "
    unfolding Shuffle_def by auto
  show  "  \<And> x A. (\<And>y. y \<in> A \<Longrightarrow> y \<subseteq> x) \<Longrightarrow> \<Union> A \<subseteq> x "
    unfolding Shuffle_def by auto
qed

interpretation shuffle_languages_cka :
  concurrent_kleene_algebra "{\<epsilon>}" "(\<union>)" "(;)" "(\<parallel>)" "{}" "(\<subseteq>)" "\<Union>"
proof
  show "  \<And> A B C D. A \<parallel> B ; C \<parallel> D \<subseteq> (B ; C) \<parallel> (A ; D) "
    unfolding Shuffle_def conc_def
    sorry
qed

end