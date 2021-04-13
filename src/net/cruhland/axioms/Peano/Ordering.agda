open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl
  as LtBaseDecl
import net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesDecl
  as LtPropertiesDecl
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  as LteBaseDecl
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesDecl
  as LtePropertiesDecl
import net.cruhland.axioms.Peano.Ordering.PropertiesDecl
  as OrderingPropertiesDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.Ordering
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

open LtBaseDecl PB PS PA using (LtBase)
open LtPropertiesDecl PB PS PA using (LtProperties)
open LteBaseDecl PB PS PA using (LteBase)
open LtePropertiesDecl PB PS PA using (LteProperties)
open OrderingPropertiesDecl PB PS PA using (OrderingProperties)

-- Combine all child modules into a single record
record Ordering : Set₁ where
  field
    LTEB : LteBase
    LTEP : LteProperties LTEB
    LTB : LtBase LTEB
    LTP : LtProperties LTEB LTB
    OP : OrderingProperties LTEB LTB

  open LtBase LTB public
  open LtProperties LTP public
  open LteBase LTEB public
  open LteProperties LTEP public
  open OrderingProperties OP public
