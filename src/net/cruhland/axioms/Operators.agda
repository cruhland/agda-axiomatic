module net.cruhland.axioms.Operators where

record PlusOp (A : Set) : Set where
  infixl 6 _+_
  field
    _+_ : A → A → A

record StarOp (A : Set) : Set where
  infixl 7 _*_
  field
    _*_ : A → A → A
