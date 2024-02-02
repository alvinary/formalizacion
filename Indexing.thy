theory Indexing
  imports Main HOL.Rings HOL.Set
begin

datatype choice = L | R

fun compose :: " ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b " (infixl "|>" 90) where
" compose f a = f a "

fun chooseOn :: " choice list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list  " where
"chooseOn [] _ _ = []" |
"chooseOn _ [] _ = []" |
"chooseOn _ _ [] = []" |
"chooseOn (L#ls) (x#xs) (y#ys) = x#(chooseOn ls xs (y#ys))" |
"chooseOn (R#ls) (x#xs) (y#ys) = y#(chooseOn ls (x#xs) ys)"

fun list_power :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list " (infixl "^" 70) where
"list_power xs 0 = []" |
"list_power xs (Suc n) = xs @ (list_power xs n)"

fun factorial :: "nat \<Rightarrow> nat" where
"factorial 0 = 1 " |
"factorial (Suc n) = (Suc n) * (factorial n)"

fun previous_factorial :: "'a list \<Rightarrow> nat" where
" previous_factorial [] = 1 " |
" previous_factorial (x#xs) = (factorial (length xs)) "

fun element_index :: "nat \<Rightarrow> 'a list \<Rightarrow> nat " where
" element_index n xs = (n div (previous_factorial xs)) "

fun permutation_head :: " nat \<Rightarrow> 'a list \<Rightarrow> 'a " where
" permutation_head n xs = xs ! (element_index n xs) "

fun permutation_tail :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
" permutation_tail n xs = remove1 (permutation_head n xs) xs "

fun nth_permutation :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
" nth_permutation (0) xs = xs " |
" nth_permutation (Suc n) xs = (permutation_head (Suc n) xs) #
                                  nth_permutation
                                    (n mod (previous_factorial xs))
                                    (permutation_tail (Suc n) xs) "

fun choices :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> choice list" where
"choices n k r = nth_permutation n ([L]^k @ [R]^r)"

fun lala :: "nat \<Rightarrow> nat" where
"lala _ = 1"

fun lele :: "nat \<Rightarrow> nat" where
"lele _ = 2"

fun lulu :: "nat \<Rightarrow> nat" where
"lulu _ = 3"

fun lalo :: "nat \<Rightarrow> nat" where
"lalo n = n"

definition "le_lista = choices (lalo 1) (lalo 2) (lalo 2)"

value " choices (lalo 0) (lalo 2) (lalo 2)"
value " choices (lalo 1) (lalo 2) (lalo 2)"
value " choices (lalo 2) (lalo 2) (lalo 2)"
value " choices (lalo 3) (lalo 2) (lalo 2)"
value " choices (lalo 4) (lalo 2) (lalo 2)"
value " choices (lalo 5) (lalo 2) (lalo 2)"
value " choices (lalo 6) (lalo 2) (lalo 2)"
value " choices (lalo 7) (lalo 2) (lalo 2)"
value " choices (lalo 8) (lalo 2) (lalo 2)"
value " choices (lalo 9) (lalo 2) (lalo 2)"
value " choices (lalo 10) (lalo 2) (lalo 2)"

value " nth_permutation (lalo 0) [lalo 1, lalo 2] "
value " nth_permutation (lalo 1) [lalo 1, lalo 2] "
value " nth_permutation (lalo 2) [lalo 1, lalo 2] "


value " nth_permutation (lalo 0) [lalo 1, lalo 2, lalo 3] "
value " nth_permutation (lalo 1) [lalo 1, lalo 2, lalo 3] "
value " nth_permutation (lalo 2) [lalo 1, lalo 2, lalo 3] "
value " nth_permutation (lalo 3) [lalo 1, lalo 2, lalo 3] "
value " nth_permutation (lalo 4) [lalo 1, lalo 2, lalo 3] "
value " nth_permutation (lalo 5) [lalo 1, lalo 2, lalo 3] "

end