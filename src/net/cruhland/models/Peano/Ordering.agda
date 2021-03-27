open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplNeq
  as LtBaseImplNeq
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

ltBase : LtBase U.base U.sign U.addition lteBase
ltBase = record { LtBaseImplNeq U.base U.sign U.addition lteBase }

module PD = PropertiesDecl U.base U.sign U.addition lteBase ltBase

orderingProperties : PD.OrderingProperties
orderingProperties = record
  { PropertiesImpl U.base U.sign U.addition lteBase lteProperties ltBase }
