open import net.cruhland.axioms.Rationals.BaseDecl using (Base)

module net.cruhland.axioms.Rationals where

record Rationals : Set₁ where
  field
    QB : Base

  open Base QB public
