open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPairDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals PA Z using (Rationals)
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.DivisionDefn PA Z using (QD)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)
open import net.cruhland.models.Rationals.IntPair.ReciprocalDefn PA Z using (QR)
open import net.cruhland.models.Rationals.IntPair.SignDefn PA Z using (QS)

rationals : Rationals
rationals =
  record { QA = QA ; QB = QB ; QD = QD ; QM = QM ; QN = QN ; QR = QR ; QS = QS}
