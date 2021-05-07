open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Ordering (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
import net.cruhland.models.Integers PA as ℤ
open import net.cruhland.models.Rationals.Base PA as ℚ using (ℚ)
import net.cruhland.models.Rationals.Equality PA as ℚ≃
import net.cruhland.models.Rationals.Negation PA as ℚ-

private
  instance
    -- TODO: Remove this after factoring out Decls
    ℤ-positivity : Sign.Positivity 0
    ℤ-positivity = ℤ.positivity

record Positive (q : ℚ) : Set where
  field
    n-pos : Sign.Positive (ℚ.n q)
    d-pos : Sign.Positive (ℚ.d q)

record Negative (q : ℚ) : Set where
  field
    p : ℚ
    p-pos : Positive p
    q≃-p : q ≃ - p
