open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.ReciprocalDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)
import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z as QR
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

QR : Reciprocal QB
QR = record { QR }
