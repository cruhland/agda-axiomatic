open import net.cruhland.models.Logic using (¬_)

module net.cruhland.axioms.AbstractAlgebra.Trichotomous where

data OneOfThree (A B C : Set) : Set where
  1st : A → OneOfThree A B C
  2nd : B → OneOfThree A B C
  3rd : C → OneOfThree A B C

data TwoOfThree (A B C : Set) : Set where
  1∧2 : A → B → TwoOfThree A B C
  1∧3 : A → C → TwoOfThree A B C
  2∧3 : B → C → TwoOfThree A B C

record ExactlyOneOfThree (A B C : Set) : Set where
  constructor exactlyOneOfThree
  field
    at-least-one : OneOfThree A B C
    at-most-one : ¬ TwoOfThree A B C
