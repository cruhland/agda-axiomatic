open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.SignDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (ZM)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)
import net.cruhland.models.Integers.NatPair.SignImpl PA as SignImpl
import net.cruhland.models.Integers.NatPair.SignImplLt PA as SignImplLt
import net.cruhland.models.Integers.NatPair.SignImplNat PA as SignImplNat

-- Confirm all impls conform to the decl
signImplLt : Sign ZB ZA ZN ZM
signImplLt = record { SignImplLt }

signImplNat : Sign ZB ZA ZN ZM
signImplNat = record { SignImplNat }

-- Designate the default impl
ZS : Sign ZB ZA ZN ZM
ZS = record { SignImpl }
