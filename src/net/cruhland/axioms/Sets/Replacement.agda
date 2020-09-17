module net.cruhland.axioms.Sets.Replacement where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Setoid using (find)
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any
  using (Any; any) renaming (map to map-any)
open import Function using (_∘_; const)
open import Level using (Setω)
open import Relation.Binary using (DecSetoid)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.PreFinite as PreFinite
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.models.Logic using
  ( ⊤; _∧?_; ∧-intro; uncurry; ∨-introᴸ; ∨-introᴿ
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ⊥-elim; Dec; dec-map
  )
open import net.cruhland.models.Setoid
  using (_⟨$⟩_; DecSetoid₀; El; Equivalence; Setoid; Setoid₀; SRel₀)
  renaming (cong to SRel-cong)

private
  variable
    S T : Setoid₀

module ReplacementDefs (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet; PSet₀)

  record ReplRel (A : PSet₀ S) (T : Setoid₀) : Set₁ where
    open Setoid T renaming (_≈_ to _≈ᵀ_)

    field
      R : SRel₀ S T
      R-most : ∀ {x y} → x ∈ A → R ⟨$⟩ x ⟨$⟩ y → ∀ {z} → R ⟨$⟩ x ⟨$⟩ z → y ≈ᵀ z

  record ReplFun {A : PSet₀ S} (RR : ReplRel A T) : Set where
    open ReplRel RR using (R)
    field
      f : El S → El T
      Rxfx : ∀ {x} → x ∈ A → R ⟨$⟩ x ⟨$⟩ f x

  record ReplMem {A : PSet₀ S} (x : El T) (RR : ReplRel A T) : Set where
    constructor ReplMem-intro
    open ReplRel RR using (R)
    field
      {a} : El S
      a∈A : a ∈ A
      Rax : R ⟨$⟩ a ⟨$⟩ x

record Replacement
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PU : PairwiseUnion SA ES)
    (SS : SingletonSet SA)
      : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open EmptySet ES using (∅; x∉∅)
  open Equality SA using (_≃_; ∈-substᴿ; ≃-sym; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open PairwiseUnion PU using
    (_∪_; x∈A∪B-elim; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴿ)
  open PreFinite SA ES PU SS using
    (∈ᴸ→∈fin; ∈fin→∈ᴸ; Finite; finite; toList; toList⊆A; same-set)
  open ReplacementDefs SA public using
    (ReplFun; ReplMem; ReplMem-intro; ReplRel)
  open SetAxioms SA using (_∈_; PSet; PSet₀)
  open SingletonSet SS using (singleton; x∈sa-elim; x∈sa-intro; a∈sa)
  open Subset SA using (⊆-antisym; ⊆-intro)

  field
    replacement : (A : PSet₀ S) → ReplRel A T → PSet₀ T

    x∈rep↔Rax :
      {x : El T} {A : PSet₀ S} {R : ReplRel A T} →
        x ∈ replacement A R ↔ ReplMem x R

  private
    variable
      A : PSet₀ S
      RR : ReplRel A T

  x∈rep-elim :
    {RR : ReplRel A T} {x : El T} → x ∈ replacement A RR → ReplMem x RR
  x∈rep-elim = ↔-elimᴸ x∈rep↔Rax

  x∈rep-intro :
    {RR : ReplRel A T} {x : El T} → ReplMem x RR → x ∈ replacement A RR
  x∈rep-intro = ↔-elimᴿ x∈rep↔Rax

  ReplRel-subst : {A₁ A₂ : PSet₀ S} → A₁ ≃ A₂ → ReplRel A₁ T → ReplRel A₂ T
  ReplRel-subst A₁≃A₂ record { R = R ; R-most = R-most } = record
    { R = R
    ; R-most = λ x∈A₂ Rxy Rxz → R-most (∈-substᴿ (≃-sym A₁≃A₂) x∈A₂) Rxy Rxz
    }

  ReplFun-subst :
    {A₁ A₂ : PSet₀ S} {RR : ReplRel A₁ T} →
      (A₁≃A₂ : A₁ ≃ A₂) → ReplFun RR → ReplFun (ReplRel-subst A₁≃A₂ RR)
  ReplFun-subst A₁≃A₂ record { f = f ; Rxfx = Rxfx } =
    record { f = f ; Rxfx = λ x∈A₂ → Rxfx (∈-substᴿ (≃-sym A₁≃A₂) x∈A₂) }

  rep-subst :
    {A₁ A₂ : PSet₀ S} {R : ReplRel A₁ T} (A₁≃A₂ : A₁ ≃ A₂) →
      replacement A₁ R ≃ replacement A₂ (ReplRel-subst A₁≃A₂ R)
  rep-subst {A₁ = A₁} {A₂} {R} A₁≃A₂ =
      ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
    where
      fwd :
        ∀ {x} → x ∈ replacement A₁ R →
          x ∈ replacement A₂ (ReplRel-subst A₁≃A₂ R)
      fwd x∈rep₁ =
        let ReplMem-intro a∈A₁ Rax = x∈rep-elim x∈rep₁
         in x∈rep-intro (ReplMem-intro (∈-substᴿ A₁≃A₂ a∈A₁) Rax)

      rev :
        ∀ {x} → x ∈ replacement A₂ (ReplRel-subst A₁≃A₂ R) →
          x ∈ replacement A₁ R
      rev x∈rep₂ =
        let ReplMem-intro a∈A₂ Rax = x∈rep-elim x∈rep₂
         in x∈rep-intro (ReplMem-intro (∈-substᴿ (≃-sym A₁≃A₂) a∈A₂) Rax)

  instance
    rep-∈? :
      {{DS : DecSetoid₀}} {A : PSet₀ (DecSetoid.setoid DS)} {RR : ReplRel A T} →
        let open ReplRel RR using (R)
         in {{_ : Finite A}} {{_ : ∀ {x y} → Dec (R ⟨$⟩ x ⟨$⟩ y)}} →
              DecMembership (replacement A RR)
    rep-∈? {T = T} {{DS}} {A} {RR} {{finA}} {{decR}} =
      ∈?-intro (dec-map x∈rep-intro x∈rep-elim ReplMem?)
        where
          open DecSetoid DS using (_≈_)
          open Setoid T using () renaming (refl to ≈ᵀ-refl)
          open ReplRel RR using (R)

          ReplMem? : ∀ {x} → Dec (ReplMem x RR)
          ReplMem? {x} =
            dec-map fwd rev (any (λ a → decR {a} {x}) (toList A))
              where
                fwd : Any (λ a → R ⟨$⟩ a ⟨$⟩ x) (toList A) → ReplMem x RR
                fwd Rax∈ᴸlA =
                  let S′ = DecSetoid.setoid DS
                      ∧-intro a (∧-intro a∈ᴸlA Rax) = find S′ Rax∈ᴸlA
                      a∈fin[lA] = ∈ᴸ→∈fin {DS = DS} a∈ᴸlA
                   in ReplMem-intro (∈-substᴿ same-set a∈fin[lA]) Rax

                rev : ReplMem x RR → Any (λ a → R ⟨$⟩ a ⟨$⟩ x) (toList A)
                rev record { a = a ; a∈A = a∈A ; Rax = Rax } =
                  let a∈fin[lA] = ∈-substᴿ (≃-sym same-set) a∈A
                      a∈ᴸlA = ∈fin→∈ᴸ {DS = DS} {xs = toList A} a∈fin[lA]
                   in map-any
                     (λ a≈a′ →
                       Equivalence.to (SRel-cong R a≈a′ ≈ᵀ-refl) ⟨$⟩ Rax)
                     a∈ᴸlA

    rep-finite :
      {A : PSet₀ S} {RR : ReplRel A T} →
        {{finA : Finite A}} {{rf : ReplFun RR}} →
          Finite (replacement A RR)
    rep-finite {S = S} {T} {A} {RR} {{finA}} {{rf}} =
      let A≃flA = ≃-sym same-set
          RR′ = ReplRel-subst A≃flA RR
          rf′ = ReplFun-subst A≃flA rf
          fin-map-xs≃rep-fin-xs = same-xs (toList⊆A A) RR′ rf′
       in record
         { elements = elements
         ; same-set = ≃-trans fin-map-xs≃rep-fin-xs (≃-sym (rep-subst A≃flA))
         }
      where
        open Setoid S using () renaming
          (_≈_ to _≈ˢ_; refl to ≈ˢ-refl; sym to ≈ˢ-sym)
        open Setoid T using () renaming (_≈_ to _≈ᵀ_; refl to ≈ᵀ-refl)
        open ReplRel RR using (R)
        f = ReplFun.f rf
        elements = map f (toList A)

        same-xs :
          {xs : List (El S)} (Axs∈A : All (_∈ A) xs)
            (rpl : ReplRel (finite xs) T) (rpf : ReplFun rpl) →
              finite (map (ReplFun.f rpf) xs) ≃ replacement (finite xs) rpl
        same-xs []ᴬ rpl rpf = ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
          where
            fwd : ∀ {x} → x ∈ ∅ → x ∈ replacement ∅ rpl
            fwd x∈∅ = ⊥-elim (x∉∅ x∈∅)

            rev : ∀ {x} → x ∈ replacement ∅ rpl → x ∈ ∅
            rev x∈rep =
              let ReplMem-intro a∈∅ Rax = x∈rep-elim x∈rep
               in ⊥-elim (x∉∅ a∈∅)
        same-xs {x ∷ xs} (x∈A ∷ᴬ xs⊆A) rpl rpf =
          begin
            finite (map rpf-f (x ∷ xs))
          ≃⟨⟩
            finite (rpf-f x ∷ map rpf-f xs)
          ≃⟨⟩
            singleton (rpf-f x) ∪ finite (map rpf-f xs)
          ≃⟨ ∪-substᴿ (same-xs xs⊆A rpl′ rpf′) ⟩
            singleton (rpf-f x) ∪ replacement (finite xs) rpl′
          ≃⟨ ⊆-antisym (⊆-intro fwd) (⊆-intro rev) ⟩
            replacement (finite (x ∷ xs)) rpl
          ∎
          where
            rpl-R = ReplRel.R rpl
            rpl-most = ReplRel.R-most rpl
            rpl′ = record
              { R = rpl-R
              ; R-most = λ w∈fxs Rwy Rwz → rpl-most (x∈A∪B-introᴿ w∈fxs) Rwy Rwz
              }
            rpf-f = ReplFun.f rpf
            rpf′ = record
              { f = ReplFun.f rpf
              ; Rxfx = λ {w} w∈fxs → ReplFun.Rxfx rpf (x∈A∪B-introᴿ w∈fxs)
              }

            fwd :
              ∀ {z} →
                z ∈ singleton (rpf-f x) ∪ replacement (finite xs) rpl′ →
                z ∈ replacement (finite (x ∷ xs)) rpl
            fwd z∈sfx∪rep′ with x∈A∪B-elim z∈sfx∪rep′
            ... | ∨-introᴸ z∈sfx =
              let fx≈z = x∈sa-elim z∈sfx
                  Rxfx = ReplFun.Rxfx rpf (x∈A∪B-introᴸ a∈sa)
                  Rxz = Equivalence.to (SRel-cong rpl-R ≈ˢ-refl fx≈z) ⟨$⟩ Rxfx
               in x∈rep-intro (ReplMem-intro (x∈A∪B-introᴸ a∈sa) Rxz)
            ... | ∨-introᴿ z∈rep′ =
              let ReplMem-intro x∈fxs Rxz = x∈rep-elim z∈rep′
               in x∈rep-intro (ReplMem-intro (x∈A∪B-introᴿ x∈fxs) Rxz)

            rev :
              ∀ {z} →
                z ∈ replacement (finite (x ∷ xs)) rpl →
                z ∈ singleton (rpf-f x) ∪ replacement (finite xs) rpl′
            rev z∈rep with x∈rep-elim z∈rep
            ... | ReplMem-intro a∈f[x∷xs] Raz with x∈A∪B-elim a∈f[x∷xs]
            ... | ∨-introᴸ a∈sx =
              let x≈a = x∈sa-elim a∈sx
                  Raz⇔Rxz = SRel-cong rpl-R (≈ˢ-sym x≈a) ≈ᵀ-refl
                  Rxz = Equivalence.to Raz⇔Rxz ⟨$⟩ Raz
                  Rx[fx] = ReplFun.Rxfx rpf (x∈A∪B-introᴸ a∈sa)
                  fx≈z = ReplRel.R-most rpl (x∈A∪B-introᴸ a∈sa) Rx[fx] Rxz
               in x∈A∪B-introᴸ (x∈sa-intro fx≈z)
            ... | ∨-introᴿ a∈fxs =
              x∈A∪B-introᴿ (x∈rep-intro (ReplMem-intro a∈fxs Raz))
