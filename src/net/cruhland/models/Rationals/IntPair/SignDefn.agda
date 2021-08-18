open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.SignDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.SignDecl PA Z using (Sign)
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.DivisionDefn PA Z using (QD)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)
open import net.cruhland.models.Rationals.IntPair.ReciprocalDefn PA Z using (QR)
import net.cruhland.models.Rationals.IntPair.SignImpl PA Z as QS

QS : Sign QB QA QN QM QR QD
QS = record { QS }
