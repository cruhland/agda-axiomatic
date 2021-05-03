open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Integers.Sign.BaseDecl using (SignBase)
import net.cruhland.models.Integers.Sign.BaseImplEq as BaseImplEq
import net.cruhland.models.Integers.Sign.BaseImplLt as BaseImplLt
open import net.cruhland.models.Integers.Sign.PropertiesDecl
  using (SignProperties)
import net.cruhland.models.Integers.Sign.PropertiesImplBase
  as PropertiesImplBase

module net.cruhland.models.Integers.Sign (PA : PeanoArithmetic) where

private
  signBaseImplEq : SignBase PA
  signBaseImplEq = record { BaseImplEq PA }

  signBaseImplLt : SignBase PA
  signBaseImplLt = record { BaseImplLt PA }

  signBase = signBaseImplLt

  signProperties : SignProperties PA signBase
  signProperties = record { PropertiesImplBase PA signBase }

record Sign : Set₁ where
  field
    SB : SignBase PA
    SP : SignProperties PA SB

  open SignBase SB public
  open SignProperties SP public

sign : Sign
sign = record { SB = signBase ; SP = signProperties }

open Sign sign public
