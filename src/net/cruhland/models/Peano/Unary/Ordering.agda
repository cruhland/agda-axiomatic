import net.cruhland.axioms.Peano.Ordering as Ordering
open import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl using (LtBase)
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseImplNeq
  as LtBaseImplNeq
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseImplPosDiff
  as LtBaseImplPosDiff
open import net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesDecl
  using (LtProperties)
import net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesImplBase
  as LtPropertiesImplBase
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  using (LteBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseImplAdd
  as LteBaseImplAdd
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesImplBase
  as LtePropertiesImplBase
open import net.cruhland.axioms.Peano.Ordering.PropertiesDecl as PropertiesDecl
import net.cruhland.axioms.Peano.Ordering.PropertiesImpl as PropertiesImpl
import net.cruhland.models.Peano.Unary.Base as UB
import net.cruhland.models.Peano.Unary.LteBaseImplLeft as LteBaseImplLeft
import net.cruhland.models.Peano.Unary.LteBaseImplRight as LteBaseImplRight

module net.cruhland.models.Peano.Unary.Ordering where

lteBaseImplAdd : LteBase UB.base UB.sign UB.addition
lteBaseImplAdd = record { LteBaseImplAdd UB.base UB.sign UB.addition }

lteBaseImplLeft : LteBase UB.base UB.sign UB.addition
lteBaseImplLeft = record { LteBaseImplLeft }

lteBaseImplRight : LteBase UB.base UB.sign UB.addition
lteBaseImplRight = record { LteBaseImplRight }

lteBase = lteBaseImplAdd

lteProperties : LteProperties UB.base UB.sign UB.addition lteBase
lteProperties =
  record { LtePropertiesImplBase UB.base UB.sign UB.addition lteBase }

ltBaseImplNeq : LtBase UB.base UB.sign UB.addition lteBase
ltBaseImplNeq =
  record { LtBaseImplNeq UB.base UB.sign UB.addition lteBase lteProperties }

ltBaseImplPosDiff : LtBase UB.base UB.sign UB.addition lteBase
ltBaseImplPosDiff =
  record { LtBaseImplPosDiff UB.base UB.sign UB.addition lteBase lteProperties }

ltBase : LtBase UB.base UB.sign UB.addition lteBase
ltBase = ltBaseImplNeq

ltProperties : LtProperties UB.base UB.sign UB.addition lteBase ltBase
ltProperties =
  record { LtPropertiesImplBase UB.base UB.sign UB.addition lteBase ltBase }

module PD = PropertiesDecl UB.base UB.sign UB.addition
module PI =
  PropertiesImpl
    UB.base UB.sign UB.addition lteBase lteProperties ltBase ltProperties

orderingProperties : PD.OrderingProperties lteBase ltBase
orderingProperties = record { PI }

module NO = Ordering UB.base UB.sign UB.addition

ordering : NO.Ordering
ordering = record
  { LTEB = lteBase
  ; LTEP = lteProperties
  ; LTB = ltBase
  ; LTP = ltProperties
  ; OP = orderingProperties
  }
