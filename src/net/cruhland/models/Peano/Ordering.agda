open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplNeq
  as LtBaseImplNeq
import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplPosDiff
  as LtBaseImplPosDiff
open import net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesDecl
  using (LtProperties)
import net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesImplBase
  as LtPropertiesImplBase
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl
  using (LteBase)
import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseImplAdd
  as LteBaseImplAdd
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesImplBase
  as LtePropertiesImplBase
open import net.cruhland.axioms.Peano.NewOrd.PropertiesDecl as PropertiesDecl
import net.cruhland.axioms.Peano.NewOrd.PropertiesImpl as PropertiesImpl
import net.cruhland.models.Peano.LteBaseImplLeft as LteBaseImplLeft
import net.cruhland.models.Peano.LteBaseImplRight as LteBaseImplRight
import net.cruhland.models.Peano.Unary as U

module net.cruhland.models.Peano.Ordering where

lteBaseImplAdd : LteBase U.base U.sign U.addition
lteBaseImplAdd = record { LteBaseImplAdd U.base U.sign U.addition }

lteBaseImplLeft : LteBase U.base U.sign U.addition
lteBaseImplLeft = record { LteBaseImplLeft }

lteBaseImplRight : LteBase U.base U.sign U.addition
lteBaseImplRight = record { LteBaseImplRight }

lteBase = lteBaseImplAdd

lteProperties : LteProperties U.base U.sign U.addition lteBase
lteProperties =
  record { LtePropertiesImplBase U.base U.sign U.addition lteBase }

ltBaseImplNeq : LtBase U.base U.sign U.addition lteBase
ltBaseImplNeq =
  record { LtBaseImplNeq U.base U.sign U.addition lteBase lteProperties }

ltBaseImplPosDiff : LtBase U.base U.sign U.addition lteBase
ltBaseImplPosDiff =
  record { LtBaseImplPosDiff U.base U.sign U.addition lteBase lteProperties }

ltBase : LtBase U.base U.sign U.addition lteBase
ltBase = ltBaseImplNeq

ltProperties : LtProperties U.base U.sign U.addition lteBase ltBase
ltProperties =
  record { LtPropertiesImplBase U.base U.sign U.addition lteBase ltBase }

module PD = PropertiesDecl U.base U.sign U.addition lteBase ltBase
module PI =
  PropertiesImpl
    U.base U.sign U.addition lteBase lteProperties ltBase ltProperties

orderingProperties : PD.OrderingProperties
orderingProperties = record { PI }
