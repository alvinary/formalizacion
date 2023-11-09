theory cka_err
  imports Main
begin

  class concurrent_kleene_algebra =
    fixes zero :: 'a
    fixes one :: 'a
    fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
    fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
    fixes concat :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 75)
    fixes less_or_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<le>" 70)
    assumes
      "class.quantale (zero) (one) (add) (mult)" and
      (* "class.quantale (concat) (add) (zero) (one)" and *)
      "less_or_equal (concat (mult a b) (mult c d)) (mult (concat a c) (concat b d))"

end