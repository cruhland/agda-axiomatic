open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Ordering
  (PA : PeanoArithmetic) (Z : Integers PA) where

private module ℕ = PeanoArithmetic PA
private module ℤ = Integers Z
open import net.cruhland.models.Rationals.Base PA Z as ℚ using (ℚ)
import net.cruhland.models.Rationals.Equality PA Z as ℚ≃
import net.cruhland.models.Rationals.Negation PA Z as ℚ-

record Positive (q : ℚ) : Set where
  field
    n-pos : Sign.Positive (ℚ.n q)
    d-pos : Sign.Positive (ℚ.d q)

record Negative (q : ℚ) : Set where
  field
    p : ℚ
    p-pos : Positive p
    q≃-p : q ≃ - p
