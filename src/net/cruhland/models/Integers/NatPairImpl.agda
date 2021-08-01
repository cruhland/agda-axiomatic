open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPairImpl (PA : PeanoArithmetic) where

-- Export all sub-impls
open import net.cruhland.models.Integers.NatPair.AdditionImpl PA public
open import net.cruhland.models.Integers.NatPair.BaseImpl PA public
open import net.cruhland.models.Integers.NatPair.MultiplicationImpl PA public
open import net.cruhland.models.Integers.NatPair.NegationImpl PA public
open import net.cruhland.models.Integers.NatPair.OrderingImpl PA public
open import net.cruhland.models.Integers.NatPair.SignImpl PA public

open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.axioms.Integers.LiteralImpl PA ZB public
