------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module Progress where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Fin hiding (cast)
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ ; ⊤ to ⊤ˢ ; ⊥ to ⊥ˢ)
open import Data.Fin.Subset.Properties
open import Data.List hiding (_++_ ; length)
open import Data.List.Relation.Unary.All
open import Data.Vec hiding (_++_ ; length)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Sum
open import Relation.Nullary.Decidable
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All renaming (All to Allᵐ)
open import Data.Maybe.Relation.Unary.Any renaming (Any to Anyᵐ)
open import Data.Unit using (⊤)
open import Size renaming (↑_ to ↑ˡ)

open import Syntax
open import Substitution
open import Typing-Semantics
open import Aux

------------------------------------------------------------------------
-- To eliminate the possible typing judgement (LabAEx) for case expressions,
-- we need [] ≢ Γ' ++ ⟨ D , Γ ⟩. Agda does not know that no possible constructor
-- for this equality exists, because _++_ is an arbitrary function and therefore
-- "green slime" (see the link @ (LabAEx) rule).
--
-- Workaround: Argue with length of environments

env-len-++ : {n : ℕ} {Γ Γ' : TEnv {n}} → length (Γ ++ Γ') ≡ length Γ +ᴺ length Γ'
env-len-++ {n} {[]} {Γ'} = refl
env-len-++ {n} {⟨ T , Γ ⟩} {Γ'} = cong ℕ.suc (env-len-++ {n} {Γ} {Γ'})

env-len-> : {n : ℕ} {Γ : TEnv {n}} {T : Ty {n}} → length ⟨ T , Γ ⟩ >ᴺ 0
env-len-> {n} {Γ} {T} = s≤s z≤n

env-len->-++ : {n : ℕ} {Γ Γ' : TEnv {n}} → length Γ' >ᴺ 0 → length (Γ ++ Γ') >ᴺ 0
env-len->-++ {n} {Γ} {⟨ T , Γ' ⟩} gt rewrite (env-len-++ {n} {Γ} {⟨ T , Γ' ⟩})= Data.Nat.Properties.≤-trans gt (m≤n+m (length ⟨ T , Γ' ⟩) (length Γ))

env-len-eq : {n : ℕ} {Γ : TEnv {n}} {Γ' : TEnv {n}} → Γ ≡ Γ' → length Γ ≡ length Γ'
env-len-eq {n} {Γ} {.Γ} refl = refl

env-empty-++ : {n : ℕ} {Γ' Γ : TEnv {n}} {D : Ty {n}} → ¬ ([] ≡ Γ' ++ ⟨ D , Γ ⟩)
env-empty-++ {n} {Γ} {Γ'} {D} eq = contradiction (env-len-eq eq) (Data.Nat.Properties.<⇒≢ (env-len->-++ (env-len->{T = D})))

------------------------------------------------------------------------
-- Lemmas for cast function & expressions

cast-result : {n : ℕ} {A' A B : Ty {n}} → (cast A' A B ≡ B) ⊎ (∃[ e ](cast A' A B ≡ Single e B)) ⊎ (cast A' A B ≡ Bot)
cast-result {n} {Single e A'} {A} {B}
  with A ≡ᵀ? A'
...  | no ¬eq = inj₁ refl
...  | yes eq
     with evaluate-full (gas 1000) (Cast e A B)
...     | fst , result (RValue x) = inj₂ (inj₁ (fst , refl))
...     | .Blame , result RBlame = inj₂ (inj₂ refl)
...     | fst , stuck = inj₂ (inj₂ refl)
...     | fst , out-of-gas = inj₂ (inj₂ refl)

cast-result {n} {UnitT} {A} {B} = inj₁ refl
cast-result {n} {Label x} {A} {B} = inj₁ refl
cast-result {n} {Pi A' A''} {A} {B} = inj₁ refl
cast-result {n} {Sigma A' A''} {A} {B} = inj₁ refl
cast-result {n} {CaseT x f} {A} {B} = inj₁ refl
cast-result {n} {Bot} {A} {B} = inj₁ refl
cast-result {n} {Dyn} {A} {B} = inj₁ refl

cast-ineq-singleton : {n : ℕ} {A' A B : Ty {n}} {e : Exp {n}} → A ≢ A' → cast (Single e A') A B ≡ B
cast-ineq-singleton {n} {A'} {A} {B} {e} neq
  with A ≡ᵀ? A'
...  | yes eq = contradiction eq neq
...  | no ¬eq = refl

cast-invert-single : {n : ℕ} {A' A B : Ty {n}} → Σ (Exp {n}) (λ e → (Σ (Ty {n}) (λ C → (cast A' A B ≡ Single e C))))
                                               → Σ (Exp {n}) (λ e → (Σ (Ty {n}) (λ C → (A' ≡ Single e C)))) ⊎
                                                 Σ (Exp {n}) (λ e → (Σ (Ty {n}) (λ C → (B ≡ Single e C))))
cast-invert-single {n} {Single x A'} {A} {B} (fst , snd , eq) = inj₁ (x , (A' , refl))

cast-invert-single {n} {UnitT} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {Label x} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {Pi A' A''} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {Sigma A' A''} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {CaseT x f} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {Bot} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))
cast-invert-single {n} {Dyn} {A} {Single e B} (fst , snd , eq) = inj₂ (e , (B , refl))

cast-invert-bot : {n : ℕ} {A B : Ty {n}} {A' : Ty {n}} → Bot ≢ B → Bot ≡ cast A' A B → Σ (Exp {n}) (λ e → A' ≡ Single e A)
cast-invert-bot {n} {A} {B} {Single x A'} neq eq
  with A ≡ᵀ? A'
...  | yes eq' rewrite eq' = x , refl
...  | no ¬eq'
     with cast-ineq-singleton{A' = A'}{A = A}{B = B}{e = x} ¬eq'
...     | eq'' = contradiction eq neq
cast-invert-bot {n} {A} {B} {UnitT} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {Label x} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {Pi A' A''} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {Sigma A' A''} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {CaseT x f} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {Bot} neq eq = contradiction eq neq
cast-invert-bot {n} {A} {B} {Dyn} neq eq = contradiction eq neq

special-casts : {n : ℕ} {e : Exp {n}} {A G : Ty {n}} → (∀ e' A B → ¬ (e ≡ Cast e' A B)) → Val e → ([] ⊢ Cast e Dyn G ▷ A) → A ≡ G
special-casts {n} {(Cast e A' B')} {A} {G} ncast W (CastA (CastA j x₁) x) = contradiction refl (ncast e A' B')
special-casts {n} {.UnitE} {A} {G} ncast W (CastA (UnitAI x₁) x) = x
special-casts {n} {.(LabI _)} {A} {G} ncast W (CastA (LabAI x₁) x) = x
special-casts {n} {.(Abs _)} {A} {G} ncast W (CastA (PiAI j) x) = x
special-casts {n} {.(ProdV _ _)} {A} {G} ncast W (CastA (PairAI j j₁) x) = x

no-reduce-nftype-step : {n : ℕ} {T : Ty {n}} → (nfT : TyNf T) → (evaluate-step-type T) ≡ (result (RNf nfT))
no-reduce-nftype-step {n} {.Dyn} NfDyn = refl
no-reduce-nftype-step {n} {.UnitT} NfUnit = refl
no-reduce-nftype-step {n} {.(Label _)} NfLabel = refl
no-reduce-nftype-step {n} {.(Pi _ _)} NfPi = refl
no-reduce-nftype-step {n} {.(Sigma _ _)} NfSigma = refl
no-reduce-nftype-step {n} {Single e A} (NfSingle{V = V}{tybB = tybB})
  with Val? e
...  | no ¬v = contradiction V ¬v
no-reduce-nftype-step {n} {Single e .UnitT} (NfSingle {V = V} {tybB = BUnit}) | yes v rewrite Val-uniqueness V v = refl
no-reduce-nftype-step {n} {Single e .(Label _)} (NfSingle {V = V} {tybB = BLabel}) | yes v rewrite Val-uniqueness V v = refl

ground-type-not-dyn : {n : ℕ} {G : Ty {n}} → TyG G → G ≢ Dyn
ground-type-not-dyn {n} {.UnitT} GUnit = λ ()
ground-type-not-dyn {n} {.(Label _)} GLabel = λ ()
ground-type-not-dyn {n} {.(Pi Dyn Dyn)} GPi = λ ()
ground-type-not-dyn {n} {.(Sigma Dyn Dyn)} GSigma = λ ()
ground-type-not-dyn {n} {.(Single _ (Label _))} GSingleLabel = λ ()
ground-type-not-dyn {n} {.(Single _ UnitT)} GSingleUnit = λ ()

no-reduce-value-step : {n : ℕ} {e : Exp {n}} → (V : Val e) → (evaluate-step-expr e) ≡ (result (RValue V))
no-reduce-value-step {n} {.UnitE} VUnit = refl
no-reduce-value-step {n} {.(LabI _)} VLab = refl
no-reduce-value-step {n} {.(Abs _)} VFun = refl
no-reduce-value-step {n} {(ProdV e e')} (VProd V V₁)
  with Val? e
...  | no ¬v = contradiction V ¬v
...  | yes v
     with no-reduce-value-step {n} {e'} V₁
...     | eq rewrite eq | Val-uniqueness v V = refl
no-reduce-value-step {n} {(Cast e G Dyn)} (VCast V x)
  with no-reduce-value-step {n} {e} V
...  | eq rewrite eq
     with no-reduce-nftype-step (TyG⊂TyNf x)
...     | eq' rewrite eq'
        with G ≡ᵀ? Dyn
...        | yes eq'' = contradiction eq'' (ground-type-not-dyn x) -- Ground type no dyn
...        | no ¬eq''
           with TyG? G
...           | no ¬tyg = contradiction x ¬tyg
...           | yes tyg rewrite TyG-uniqueness tyg x = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V)
  with no-reduce-value-step {n} {e} V
...  | eq rewrite eq
     with TyG? Pi A B | TyG? Pi A' B'
...     | yes GPi | yes GPi = refl
...     | yes GPi | no ¬tyg
        with A' ≡ᵀ? Dyn
...        | yes eq'
           with B' ≡ᵀ? Dyn
...           | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg
...           | no ¬eq'' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | yes GPi | no ¬tyg | no ¬eq' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | yes GPi
  with A ≡ᵀ? Dyn
...  | yes eq'
     with B ≡ᵀ? Dyn
...     | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg
...     | no ¬eq'' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | yes GPi | no ¬eq' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg'
  with A ≡ᵀ? Dyn
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | yes eq'
  with B ≡ᵀ? Dyn
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | yes eq' | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | yes eq' | no ¬eq''
  with A' ≡ᵀ? Dyn
...  | yes eq'''
     with B' ≡ᵀ? Dyn
...     | yes eq'''' rewrite eq''' | eq'''' = contradiction GPi ¬tyg' 
...     | no ¬eq'''' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | yes eq' | no ¬eq'' | no ¬eq''' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | no ¬eq'
  with B ≡ᵀ? Dyn
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | no ¬eq' | yes eq''
  with A' ≡ᵀ? Dyn
...  | yes eq'''
     with B' ≡ᵀ? Dyn
...     | yes eq'''' rewrite eq''' | eq'''' = contradiction GPi ¬tyg' 
...     | no ¬eq'''' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | no ¬eq' | yes eq'' | no ¬eq''' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | no ¬eq' | no ¬eq''
  with A' ≡ᵀ? Dyn
...  | yes eq'''
     with B' ≡ᵀ? Dyn
...     | yes eq'''' rewrite eq''' | eq'''' = contradiction GPi ¬tyg' 
...     | no ¬eq'''' = refl
no-reduce-value-step {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | eq | no ¬tyg | no ¬tyg' | no ¬eq' | no ¬eq'' | no ¬eq''' = refl

no-reduce-value : {n : ℕ} {e : Exp {n}} → Val e → proj₁ (evaluate-full (gas 1000) e) ≡ e
no-reduce-value {n} {.UnitE} VUnit = refl
no-reduce-value {n} {.(LabI _)} VLab = refl
no-reduce-value {n} {.(Abs _)} VFun = refl
no-reduce-value {n} {(ProdV e e')} (VProd V V₁)
  with Val? e
...  | no ¬v = contradiction V ¬v
...  | yes v
     with Val? e'
...     | no ¬v₁ = contradiction V₁ ¬v₁
...     | yes v₁ rewrite (no-reduce-value-step v₁) = refl
no-reduce-value {n} {(Cast e G Dyn)} (VCast V x) rewrite (no-reduce-value-step V) | (no-reduce-nftype-step (TyG⊂TyNf x))
  with G ≡ᵀ? Dyn
...  | yes eq rewrite eq = contradiction x (λ ())
...  | no ¬eq
     with TyG? G
...     | yes tygg = refl
...     | no ¬tygg = contradiction x ¬tygg
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V)
  rewrite (no-reduce-value-step V)
  with TyG? (Pi A B) | TyG? (Pi A' B')
...  | yes GPi | yes GPi = refl
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | yes GPi | no ¬tyg
  with A' ≡ᵀ? Dyn
...  | no ¬eq = refl
...  | yes eq
     with B' ≡ᵀ? Dyn
...     | no ¬eq' = refl
...     | yes eq' rewrite eq | eq' = contradiction GPi ¬tyg
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | yes GPi
  with A ≡ᵀ? Dyn
...  | no ¬eq = refl
...  | yes eq
     with B ≡ᵀ? Dyn
...     | no ¬eq' = refl
...     | yes eq' rewrite eq | eq' = contradiction GPi ¬tyg
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg'
  with A ≡ᵀ? Dyn
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | no ¬eq
  with A' ≡ᵀ? Dyn
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | no ¬eq | no ¬eq' = refl
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | no ¬eq | yes eq'
  with B' ≡ᵀ? Dyn
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | no ¬eq | yes eq' | no ¬eq'' = refl  
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | no ¬eq | yes eq' | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg'
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | yes eq
  with B ≡ᵀ? Dyn
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | yes eq | yes eq' rewrite eq | eq' = contradiction GPi ¬tyg
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | yes eq | no ¬eq'
  with A' ≡ᵀ? Dyn
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | yes eq | no ¬eq' | no ¬eq'' = refl
no-reduce-value {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) | no ¬tyg | no ¬tyg' | yes eq | no ¬eq' | yes eq''
  with B' ≡ᵀ? Dyn
...  | yes eq''' rewrite eq'' | eq''' = contradiction GPi ¬tyg'
...  | no ¬eq''' = refl

cast-value-ground-dyn : {n : ℕ} {e : Exp {n}} {G : Ty {n}} → Val e → TyG G → cast (Single e G) G Dyn ≡ Single (Cast e G Dyn) Dyn
cast-value-ground-dyn {n} {e} {G} V tyg
  with G ≡ᵀ? G
...  | no ¬eq = contradiction refl ¬eq
...  | yes eq rewrite (no-reduce-value-step V) | (no-reduce-nftype-step (TyG⊂TyNf tyg))
     with G ≡ᵀ? Dyn
...     | yes eq' rewrite eq' = contradiction tyg (λ ())
...     | no ¬eq'
        with TyG? G
...        | no ¬tygg = contradiction tyg ¬tygg
...        | yes tygg = refl

single-always-value-cast-pi : {n : ℕ} {e : Exp {n}} {A'' T : Ty {n}} {A B A' B' : Ty {n}} → cast A'' (Pi A B) (Pi A' B') ≡ Single e T → ∃[ e' ](A'' ≡ Single e' (Pi A B) × Val e)
single-always-value-cast-pi {n} {e} {Single e' A''} {T} {A} {B} {A'} {B'} eq
  with (Pi A B) ≡ᵀ? A''
...  | no ¬eq' = contradiction eq λ ()
...  | yes eq'
     with evaluate-full (gas 1000) (Cast e' (Pi A B) (Pi A' B'))
single-always-value-cast-pi {n} {.fst} {Single e' A''} {.(Pi A' B')} {A} {B} {A'} {B'} refl | yes eq' | fst , result (RValue x) rewrite eq' = e' , (refl , x)

single-always-value-cast : {n : ℕ} {e : Exp {n}} {A T : Ty {n}} {G : Ty {n}} {tyg : TyG G} → cast A G Dyn ≡ Single e T → ∃[ e' ](A ≡ Single e' G × Val e)
single-always-value-cast {n} {e} {Single e' A} {T} {G} {tyg} eq
  with G ≡ᵀ? A
...  | no ¬eq' = contradiction eq (λ ())
...  | yes eq'
     with evaluate-full (gas 1000) (Cast e' G Dyn)
single-always-value-cast {n} {.fst} {Single e' A} {.Dyn} {G} {tyg} refl | yes eq' | fst , result (RValue x) rewrite eq' = e' , (refl , x)

single-always-value : {n : ℕ} {e e' : Exp {n}} {T : Ty {n}} → Val e → [] ⊢ e ▷ Single e' T → Val e'
single-always-value {n} {(Cast e G Dyn)} {e'} {T} (VCast V x₁) (CastA{A' = A'} j x)
  with single-always-value-cast{A = A'}{G = G}{tyg = x₁} (sym x)
...  | fst , fst₁ , snd = snd
single-always-value {n} {(Cast e (Pi A B) (Pi A' B'))} {e'} {T} (VCastFun V) (CastA{A' = A''} j x)
  with (cast-result{A' = A''}{A = Pi A B}{B = Pi A' B'})
...  | inj₁ x₁ = contradiction (≡-trans x x₁) (λ ())
...  | inj₂ (inj₂ y) = contradiction (≡-trans x y) λ ()
...  | inj₂ (inj₁ x₁)
     with single-always-value-cast-pi{A'' = A''}{A = A}{B = B}{A' = A'}{B' = B'} (sym x)
...     | fst , fst₁ , snd = snd
single-always-value {n} {.UnitE} {.UnitE} {.UnitT} V (UnitAI x) = VUnit
single-always-value {n} {.(LabI _)} {.(LabI _)} {.(Label ⁅ _ ⁆)} V (LabAI x) = VLab

cast-value-ground-dyn-type : {n : ℕ} {e : Exp {n}} {G T : Ty {n}} → Val e → TyG G → [] ⊢ Cast e G Dyn ▷ T → (T ≡ Dyn ⊎ ∃[ e' ](T ≡ Single e' Dyn))
cast-value-pi-type : {n : ℕ} {e : Exp {n}} {A B A' B' : Ty {n}} {T : Ty {n}} → Val e → [] ⊢ Cast e (Pi A B) (Pi A' B') ▷ T → (T ≡ (Pi A' B') ⊎ ∃[ e' ](T ≡ Single e' (Pi A' B') × Val e'))

-- no-reduce-value : {n : ℕ} {e : Exp {n}} → Val e → proj₁ (evaluate-full (gas 1000) e) ≡ e
-- (evaluate-full (gas 1000) (Cast fst (Pi A'' B'') (Pi A' B'))
cast-value-pi-type {n} {.(Cast _ _ Dyn)} {A} {B} {A'} {B'} (VCast V x₂) (CastA (CastA{ok = ok}{ok' = ok'} j x₁) x)
  with (cast-value-ground-dyn-type V x₂ (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ x₃ rewrite x₃ = inj₁ x
...  | inj₂ (fst , snd) rewrite snd = inj₁ x
cast-value-pi-type {n} {.(Cast _ (Pi _ _) (Pi _ _))} {A} {B} {A'} {B'} (VCastFun{A = A₁}{A' = A''}{B = B₁}{B' = B''} V) (CastA (CastA{ok = ok}{ok' = ok'} j x₁) x)
  with (cast-value-pi-type V (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ x₂ rewrite x₂ = inj₁ x
...  | inj₂ (fst , snd , thd) rewrite snd
     with (Pi A B ≡ᵀ? Pi A'' B'')
...     | no ¬eq = inj₁ x
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl
  rewrite (no-reduce-value-step thd)
  with TyG? Pi A'' B'' | TyG? Pi A' B'
...  | yes GPi | yes GPi = inj₂ ((Cast fst (Pi Dyn Dyn) (Pi Dyn Dyn)) , (x , VCastFun thd))
...  | yes GPi | no ¬tyg
     with A' ≡ᵀ? Dyn
...     | yes eq
        with B' ≡ᵀ? Dyn
...        | yes eq' rewrite eq | eq' = contradiction GPi ¬tyg
...        | no ¬eq' = inj₂ ((Cast fst (Pi Dyn Dyn) (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | yes GPi | no ¬tyg | no ¬eq = inj₂ ((Cast fst (Pi Dyn Dyn) (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | yes GPi
  with A'' ≡ᵀ? Dyn
...  | yes eq
     with B'' ≡ᵀ? Dyn
...     | yes eq' rewrite eq | eq' = contradiction GPi ¬tyg
...     | no ¬eq' = inj₂ ((Cast fst (Pi A'' B'') (Pi Dyn Dyn)) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | yes GPi | no ¬eq = inj₂ ((Cast fst (Pi A'' B'') (Pi Dyn Dyn)) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | no ¬tyg'
  with A'' ≡ᵀ? Dyn | A' ≡ᵀ? Dyn
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | no ¬tyg' | yes eq | yes eq'
  with B'' ≡ᵀ? Dyn | B' ≡ᵀ? Dyn
...  | yes eq'' | yes eq''' rewrite eq | eq'' = contradiction GPi ¬tyg 
...  | yes eq'' | no ¬eq''' rewrite eq | eq'' = contradiction GPi ¬tyg 
...  | no ¬eq'' | yes eq''' rewrite eq' | eq''' = contradiction GPi ¬tyg'
...  | no ¬eq'' | no ¬eq''' = inj₂ ((Cast fst (Pi A'' B'') (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | no ¬tyg' | yes eq | no ¬eq'
  with B'' ≡ᵀ? Dyn
...  | yes eq'' rewrite eq | eq'' = contradiction GPi ¬tyg
...  | no ¬eq'' = inj₂ ((Cast fst (Pi A'' B'') (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | no ¬tyg' | no ¬eq | yes eq'
  with B' ≡ᵀ? Dyn
...  | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg'
...  | no ¬eq'' = inj₂ ((Cast fst (Pi A'' B'') (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {Cast _ (Pi _ _) (Pi _ _)} {_} {_} {A'} {B'} (VCastFun {_} {_} {A''} {_} {B''} V) (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes refl | no ¬tyg | no ¬tyg' | no ¬eq | no ¬eq' = inj₂ ((Cast fst (Pi A'' B'') (Pi A' B')) , (x , (VCastFun thd)))
cast-value-pi-type {n} {.UnitE} {A} {B} {A'} {B'} V (CastA (UnitAI x₁) x) = inj₁ x
cast-value-pi-type {n} {.(LabI _)} {A} {B} {A'} {B'} V (CastA (LabAI x₁) x) = inj₁ x
cast-value-pi-type {n} {.(Abs _)} {A} {B} {A'} {B'} V (CastA (PiAI j) x) = inj₁ x
cast-value-pi-type {n} {.(ProdV _ _)} {A} {B} {A'} {B'} V (CastA (PairAI j j₁) x) = inj₁ x

-- cast-value-pi-type : {n : ℕ} {e : Exp {n}} {A B A' B' : Ty {n}} {T : Ty {n}} → Val e → [] ⊢ Cast e (Pi A B) (Pi A' B') ▷ T → (T ≡ (Pi A' B') ⊎ ∃[ e' ](T ≡ Single e' (Pi A' B') × Val e'))
cast-value-ground-dyn-type {n} {.(Cast _ _ Dyn)} {G} {T} (VCast V x₂) tygg (CastA (CastA{ok = ok}{ok' = ok'} j x₁) x)
  with cast-value-ground-dyn-type V x₂ (CastA{ok = ok}{ok' = ok'} j x₁)
...  | inj₁ eq rewrite eq = inj₁ x
...  | inj₂ (fst , eq) rewrite eq
     with G ≡ᵀ? Dyn
...     | yes eq' rewrite eq' = contradiction tygg (λ ())
...     | no ¬eq' = inj₁ x
cast-value-ground-dyn-type {n} {.(Cast _ (Pi _ _) (Pi _ _))} {G} {T} (VCastFun{A = A}{A' = A'}{B = B}{B' = B'} V) tygg (CastA (CastA{ok = ok}{ok' = ok'} j x₁) x)
  with (cast-value-pi-type V (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ eq rewrite eq = inj₁ x
...  | inj₂ (fst , snd , thd) rewrite snd
     with G ≡ᵀ? Pi A' B'
...     | no ¬eq = inj₁ x
cast-value-ground-dyn-type {n} {Cast _ (Pi _ _) (Pi _ _)} {.(Pi Dyn Dyn)} {T} (VCastFun {_} {_} {_} {_} {_} V) GPi (CastA (CastA j x₁) x) | inj₂ (fst , snd , thd) | yes eq
  rewrite (no-reduce-value-step thd) = inj₂ (((Cast fst (Pi Dyn Dyn) Dyn)) , x)
cast-value-ground-dyn-type {n} {.UnitE} {G} {T} V tygg (CastA (UnitAI x₁) x)
  with G ≡ᵀ? UnitT
...  | yes eq rewrite eq | x = inj₂ ((Cast UnitE UnitT Dyn) , refl)
...  | no ¬eq rewrite x = inj₁ refl
cast-value-ground-dyn-type {n} {(LabI l)} {G} {T} V tygg (CastA (LabAI x₁) x)
  with G ≡ᵀ? (Label ⁅ l ⁆)
...  | yes eq rewrite eq | x = inj₂ (((Cast (LabI l) (Label ⁅ l ⁆) Dyn)) , refl)
...  | no ¬eq rewrite x = inj₁ refl
cast-value-ground-dyn-type {n} {.(Abs _)} {G} {T} V tygg (CastA (PiAI j) x) rewrite x = inj₁ refl
cast-value-ground-dyn-type {n} {.(ProdV _ _)} {G} {T} V tygg (CastA (PairAI j j₁) x) rewrite x = inj₁ refl

------------------------------------------------------------------------
-- Canonical forms

cf-label◁ : {n : ℕ} {s : Subset n} {e : Exp {n}} → [] ⊢ e ◁ Label s → Val e → ∃[ l ]((e ≡ LabI l) × l ∈ s)
cf-label◁ {n} {s} {.(LabI _)} (SubTypeA (LabAI {l = l} x) (ASubSingle (ASubLabel x₁) x₂ x₃)) VLab = (l , refl , ([l]⊆L⇒l∈L x₁))
cf-label◁ {n} {s} {.UnitE} (SubTypeA (UnitAI empty) (ASubSingle () x x₂)) v
cf-label◁ {n} {s} {(Cast e G Dyn)} (SubTypeA (CastA{A' = A'}{ok = ok}{ok' = ok'} x x₂) leq) (VCast v x₁)
  with (cast-value-ground-dyn-type v x₁ (CastA{A' = A'}{ok = ok}{ok' = ok'} x x₂))
...  | inj₁ z rewrite z = contradiction leq (λ ())
...  | inj₂ (fst , snd) rewrite snd = contradiction leq ϱ
     where ϱ : ¬ ([] ⊢ Single fst Dyn ≤ᵀ Label s)
           ϱ (ASubSingle () x z)
cf-label◁ {n} {s} {(Cast e (Pi A B) (Pi A' B'))} (SubTypeA (CastA{ok = ok}{ok' = ok'} x x₂) leq) (VCastFun v)
  with (cast-value-pi-type v (CastA{ok = ok}{ok' = ok'} x x₂))
...  | inj₁ z rewrite z = contradiction leq (λ ())
...  | inj₂ (fst , snd , thd) rewrite snd = contradiction leq ϱ
     where ϱ : ¬ ([] ⊢ Single fst (Pi A' B') ≤ᵀ Label s)
           ϱ (ASubSingle () x z)

cf-pi : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → [] ⊢ e ▷ (Pi A B) → Val e → ∃[ e' ](e ≡ Abs e') ⊎ ∃[ e' ](∃[ A' ](∃[ B' ](e ≡ Cast e' (Pi A' B') (Pi A B))))
cf-pi {n} {(Cast e G Dyn)} {A} {B} (CastA{A' = A'} j x) (VCast V x₁)
  with cast-result{A' = A'}{A = G}{B = Dyn}
...  | inj₁ x₂ = contradiction (≡-trans x x₂) λ () 
...  | inj₂ (inj₁ (fst , snd)) = contradiction (≡-trans x snd) λ ()
...  | inj₂ (inj₂ y) = contradiction (≡-trans x y) λ ()
cf-pi {n} {(Cast e (Pi A' B') (Pi A'' B''))} {A} {B} (CastA{A' = A°} j x) (VCastFun V)
  with cast-result{A' = A°}{A = (Pi A' B')}{B = (Pi A'' B'')}
...  | inj₁ x₁ rewrite (≡-trans x x₁) = inj₂ (e , (A' , (B' , refl)))
...  | inj₂ (inj₁ (fst , snd)) = contradiction (≡-trans x snd) λ ()
...  | inj₂ (inj₂ y) = contradiction (≡-trans x y) λ ()
cf-pi {n} {(Abs e)} {A} {B} (PiAI j) VFun = inj₁ (e , refl)

cf-pi-⇓ : {n : ℕ} {e : Exp {n}} {D A B : Ty {n}} → [] ⊢ e ▷ D → [] ⊢ D ⇓ Pi A B → Val e → ∃[ e' ](e ≡ Abs e') ⊎ ∃[ e' ](∃[ A' ](∃[ B' ](e ≡ Cast e' (Pi A' B') (Pi A B))))
cf-pi-⇓ {n} {e} {.(Pi A B)} {A} {B} j AURefl-P v = cf-pi j v
cf-pi-⇓ {n} {.(Cast _ _ Dyn)} {.(CaseT _ _)} {A} {B} (CastA{ok = ok}{ok' = ok'} j x₁) (AUCaseL-P x ins unf) (VCast v x₂)
  with (cast-value-ground-dyn-type v x₂ (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ ()
...  | inj₂ ()
cf-pi-⇓ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(CaseT _ _)} {A} {B} (CastA{ok = ok}{ok' = ok'} j x₁) (AUCaseL-P x ins unf) (VCastFun v)
  with (cast-value-pi-type v (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ ()
...  | inj₂ ()
cf-pi-⇓ {n} {e} {.(CaseT (Var (length _)) _)} {.(CaseT (Var (length _)) _)} {.(CaseT (Var (ℕ.suc (length _))) _)} j (AUCaseX-P{eq = eq} x x₁ x₂) v = contradiction eq env-empty-++
cf-pi-⇓ {n} {e} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} j (AUCaseXDyn-P{eq = eq} x) v = contradiction eq env-empty-++

cf-sigma : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → [] ⊢ e ▷ (Sigma A B) → Val e → ∃[ e' ](∃[ e'' ]( e ≡ ProdV e' e'' ))
cf-sigma {n} {.(Cast _ _ Dyn)} {A} {B} (CastA{ok = ok}{ok' = ok'} j x) (VCast v x₁)
  with (cast-value-ground-dyn-type v x₁ (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()
cf-sigma {n} {.(Cast _ (Pi _ _) (Pi _ _))} {A} {B} (CastA{ok = ok}{ok' = ok'} j x) (VCastFun v)
  with (cast-value-pi-type v (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()
cf-sigma {n} {.(ProdV _ _)} {A} {B} (PairAI{e = e}{N = N} j j₁) v = e , (N , refl)

cf-sigma-⇓ : {n : ℕ} {e : Exp {n}} {D A B : Ty {n}} → [] ⊢ e ▷ D → [] ⊢ D ⇓ Sigma A B → Val e → ∃[ e' ](∃[ e'' ]( e ≡ ProdV e' e'' ))
cf-sigma-⇓ {n} {e} {.(Sigma A B)} {A} {B} j AURefl-S v = cf-sigma j v
cf-sigma-⇓ {n} {.(Cast _ _ Dyn)} {.(CaseT _ _)} {A} {B} (CastA{ok = ok}{ok' = ok'} j x₁) (AUCaseL-S x ins unf) (VCast v x₂)
  with (cast-value-ground-dyn-type v x₂ (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ ()
...  | inj₂ ()
cf-sigma-⇓ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(CaseT _ _)} {A} {B} (CastA{ok = ok}{ok' = ok'} j x₁) (AUCaseL-S x ins unf) (VCastFun v)
  with (cast-value-pi-type v (CastA{ok = ok}{ok' = ok'} j x₁))
...  | inj₁ ()
...  | inj₂ ()
cf-sigma-⇓ {n} {e} {.(CaseT (Var (length _)) _)} {.(CaseT (Var (length _)) _)} {.(CaseT (Var (ℕ.suc (length _))) _)} j (AUCaseX-S{eq = eq} x x₁ x₂) v = contradiction eq env-empty-++
cf-sigma-⇓ {n} {e} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} j (AUCaseXDyn-S{eq = eq} x) v = contradiction eq env-empty-++

cf-not-bot : {n : ℕ} {e : Exp {n}} → Val e → ¬ ([] ⊢ e ▷ Bot)
cf-not-bot {n} {.(Cast _ _ Dyn)} (VCast V x₁) (CastA{ok = ok}{ok' = ok'} j x)
  with (cast-value-ground-dyn-type V x₁ (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()
cf-not-bot {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun V) (CastA{ok = ok}{ok' = ok'} j x)
  with (cast-value-pi-type V (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()

------------------------------------------------------------------------
-- Progress

data Progress-Type {n : ℕ} (A : Ty {n}) {j : [] ⊢ A} : Set where
  step : {A' : Ty {n}} → A ↠ A' → Progress-Type A
  result : ResultType A → Progress-Type A

data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ▷ T} : Set where
  step : {e' : Exp{n}} → e ⇨ e' → Progress e
  result : Result e → Progress e

progress-types : {n : ℕ} {A : Ty {n}} → (j : [] ⊢ A) → Progress-Type A {j}
progress : {n : ℕ} {e : Exp {n}} {T : Ty} → (j : [] ⊢ e ▷ T) → Progress e {T} {j}

progress-types {n} {.Dyn} (DynF x) = result (RNf NfDyn)
progress-types {n} {.UnitT} (UnitF x) = result (RNf NfUnit)
progress-types {n} {.Bot} (BotF x) = result RBot
progress-types {n} {.(Label _)} (LabF x) = result (RNf NfLabel)
progress-types {n} {.(Pi _ _)} (PiF j j₁) = result (RNf NfPi)
progress-types {n} {.(Sigma _ _)} (SigmaF j j₁) = result (RNf NfSigma)
progress-types {n} {(Single e A)} (SingleF{V = V} env-ok chk tybA) = result (RNf (NfSingle{V = V}{tybB = tybA}))
progress-types {n} {CaseT e f} (CaseF{U = U} (SubTypeA x x₁))
  with progress x
...  | step s = step (ξ-Case{U = U}{U' = ⇨-ValU-closed U s} s)
...  | result RBlame = step Case-Bot
...  | result (RValue x₂)
     with cf-label◁ (SubTypeA x x₁) x₂
...     | fst , snd , thd rewrite snd = step (β-Case{ins = thd})

progress {n} {.Blame} {.Bot} (BlameA x) = result RBlame
progress {n} {.UnitE} {.(Single UnitE UnitT)} (UnitAI x) = result (RValue VUnit)
progress {n} {.(LabI _)} {.(Single (LabI _) (Label ⁅ _ ⁆))} (LabAI x) = result (RValue VLab)
progress {n} {CaseE e f} {T} (LabAEl{L = L}{L' = L'}{l = l}{U = U} j subs ins j₁)
  with progress j
...  | step x = step (ξ-Case{U = U}{U' = ⇨-ValU-closed U x} x)
...  | result (RValue v)
     with cf-label◁ (SubTypeA j (ASubSingle{V = VLab} (ASubLabel subs) BLabel (notsingle (λ e B → λ ())))) v
...     | fst , fst₁ , snd rewrite fst₁ = step (β-LabE snd)
progress {n} {.(CaseE _ _)} {.Bot} (LabAEl-Bot{U = U} j)
  with progress j
...  | step x = step (ξ-Case{U = U}{U' = ⇨-ValU-closed U x} x)
...  | result RBlame = step Case-Blame
...  | result (RValue x) = contradiction j (cf-not-bot x)
progress {n} {.(Abs _)} {.(Pi _ _)} (PiAI j) = result (RValue VFun)
progress {n} {(App e e')} {T} (PiAE j x x₁ x₂)
  with progress j
...  | step x₄ = step (ξ-App₁ x₄)
...  | result RBlame = step (App₁-Blame)
progress {n} {App e e'} {T} (PiAE j x (SubTypeA x₁ x₅) x₂) | result (RValue V)
  with progress x₁
...  | step s = step (ξ-App₂{v = V} s)
...  | result RBlame = step (App₂-Blame{v = V})
...  | result (RValue W)
     with cf-pi-⇓ j x V
...     | inj₁ (fst , snd) rewrite snd = step (β-App W)
...     | inj₂ (fst , snd , thd , fth) rewrite fth
        with V
...        | VCastFun V' = step (Cast-Func{v = V'}{w = W})
progress {n} {.(Prod _ _)} {.(Sigma _ _)} (SigmaAI (SubTypeA x x₁) j)
  with progress x
...  | step r = step (ξ-Prod r)
...  | result RBlame = step (Prod-Blame)
...  | result (RValue V) = step (β-Prod{v = V})
progress {n} {.(ProdV _ _)} {.(Sigma _ _)} (PairAI{V = V} j j₁)
  with progress j₁
...  | step r = step (ξ-ProdV{v = V} r)
...  | result RBlame = step (ProdV-Blame{v = V})
...  | result (RValue W) = result (RValue (VProd V W))
progress {n} {.(LetP _ _)} {T} (SigmaAE j x j₁ x₁)
  with progress j
...  | step r = step (ξ-LetP r)
...  | result RBlame = step (LetP-Blame)
...  | result (RValue V)
     with cf-sigma-⇓ j x V
...     | fst , snd , thd rewrite thd
        with V
...        | VProd v w = step (β-LetP v w)
progress {n} {.(LetE _ _)} {T} (LetA x j j₁)
  with progress j
...  | step r = step (ξ-LetE r)
...  | result RBlame = step (LetE-Blame)
...  | result (RValue V) = step (β-LetE V)

progress {n} {.(CaseE (Var (length _)) _)} {.(CaseT (Var (length _)) _)} (LabAEx{eq = eq} x x₁ x₂) = contradiction eq env-empty-++
progress {n} {.(CaseE (Cast (Var (length _)) _ (Label _)) _)} {.(CaseT (Cast (Var (length _)) _ (Label _)) _)} (LabAExDyn{eq = eq} x x₁) = contradiction eq env-empty-++

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x)
  with progress j
...  | step st = step (ξ-Cast st)
...  | result RBlame = step Cast-Blame
...  | result (RValue v)
     with progress-types ok
...     | step st = step (Cast-Reduce-L{v = v} st)
...     | result RBot = step (Cast-Bot-L{v = v})
...     | result (RNf nfA)
        with progress-types ok'
...        | step st = step (Cast-Reduce-R{v = v} nfA st)
...        | result RBot = step (Cast-Bot-R{v = v} nfA)
...        | result (RNf nfB)
           with A ≡ᵀ? Dyn | B ≡ᵀ? Dyn
...           | yes eq | yes eq' rewrite eq | eq' = step (Cast-Dyn{v = v})
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | yes eq' rewrite eq'
  with TyG? A
...  | yes tyga = result (RValue (VCast v tyga))
...  | no ¬tyga = step (Cast-Factor-L{v = v}{nfA = nfA} ¬eq (A≢B→B≢A (¬TyG×TyNf-in⇒match-inequiv ¬tyga nfA)))
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' rewrite eq
  with TyG? B
...  | no ¬tygb = step (Cast-Factor-R{v = v}{nfB = nfB} ¬eq' (A≢B→B≢A (¬TyG×TyNf-in⇒match-inequiv ¬tygb nfB)))
progress {n} {Cast .UnitE A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue VUnit) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb = step (Cast-Fail-Dyn{v = VUnit} tygb (λ e G → λ()))
progress {n} {Cast .(LabI _) A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue VLab) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb = step (Cast-Fail-Dyn{v = VLab} tygb (λ e G → λ()))
progress {n} {Cast .(Abs _) A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue VFun) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb = step (Cast-Fail-Dyn{v = VFun} tygb (λ e G → λ()))
progress {n} {Cast .(ProdV _ _) A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue (VProd v v₁)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb = step (Cast-Fail-Dyn{v = VProd v v₁} tygb (λ e G → λ()))
progress {n} {Cast .(Cast _ (Pi _ _) (Pi _ _)) A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue (VCastFun v)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb = step (Cast-Fail-Dyn{v = (VCastFun v)} tygb λ e G → λ ())
progress {n} {Cast .(Cast _ _ Dyn) A B} {T} (CastA {ok = ok} {ok' = ok'} j x) | result (RValue (VCast v tygg)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' | yes tygb
  with []⊢ tygg ≤ᵀ? tygb
...  | yes leq = step (Cast-Collapse{v = v}{tygG = tygg}{tygH = tygb} leq)
...  | no ¬leq = step (Cast-Collide{v = v}{tygG = tygg}{tygH = tygb} ¬leq)

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq'
  with TyG? A | TyG? B
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB = ?



{-
------------------------------------------------------------------------------------------------
-----------------------------------------  Cast  -----------------------------------------------
------------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------------
-- Congruence rules
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok'} j x x₁ y)
  with  progress{e = e} j | progress-types ok | progress-types ok'
...  | step r | _ | _ = step (ξ-Cast r)
...  | result RBlame | _ | _ = step Cast-Blame
...  | result (RValue W) | step r | _ = step (Cast-Reduce-L{v = W} r)
...  | result (RValue W) | result NfBot | _ = step Cast-Bot-L
...  | result (RValue W) | result NfDyn | step r = step (Cast-Reduce-R {v = W} NfDyn r λ ())
...  | result (RValue W) | result NfUnit | step r = step (Cast-Reduce-R {v = W} NfUnit r λ ())
...  | result (RValue W) | result NfLabel | step r = step (Cast-Reduce-R {v = W} NfLabel r λ ())
...  | result (RValue W) | result (NfPi{nfA = nfA}) | step r = step (Cast-Reduce-R {v = W} (NfPi{nfA = nfA}) r λ ())
...  | result (RValue W) | result (NfSigma{nfA = nfA}) | step r = step (Cast-Reduce-R {v = W} (NfSigma{nfA = nfA}) r λ ())
...  | result (RValue W) | result NfDyn | result NfBot = step (Cast-Bot-R NfDyn λ ())
...  | result (RValue W) | result NfUnit | result NfBot = step (Cast-Bot-R NfUnit λ ())
...  | result (RValue W) | result NfLabel | result NfBot = step (Cast-Bot-R NfLabel λ ())
...  | result (RValue W) | result (NfPi{nfA = nfA})  | result NfBot = step (Cast-Bot-R (NfPi{nfA = nfA}) λ ())
...  | result (RValue W) | result (NfSigma{nfA = nfA})  | result NfBot = step (Cast-Bot-R (NfSigma{nfA = nfA}) λ ())
------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB)
  with castView e
------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A = Dyn
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn}
  with A ≡ᵀ? Dyn 
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq
  rewrite eq
------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A = Dyn
------ TyG B
  with TyG? B
...  | yes tyg
-------- (V : G => *) : * => H --> V or Blame
     with G₁ ≡ᵀ? B
...     | yes eq' rewrite eq' = step (Cast-Collapse{v = W}{g = x₂})
...     | no ¬eq' = step (Cast-Collide{v = W}{g = x₂}{h = tyg} ¬eq')
------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A = Dyn
------ ¬ TyG B
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg
  with nf-not-g-⊆ {n} {B} nfB ¬tyg
------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A = Dyn
------ ¬ TyG B (and Nf B)
-------- B = Dyn
---------- (V : G => *) : * => * --> (V : G => *)
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | dyn = step (Cast-Dyn{v =(VCast W x₂)})
-------- B = Pi A B
---------- (V : G => *) : * => Pi A B --> ((V : G => *) : * => G') : G' => Pi A B
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | pi z z'
  with produce-ground-ng {n} {B} (pi z z') (λ ()) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
-------- B = Sigma A B
---------- (V : G => *) : * => Sigma A B --> ((V : G => *) : * => G') : G' => Sigma A B
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | sigma z z'
  with produce-ground-ng {n} {B} (sigma z z') (λ ()) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
-------- B = Bot
---------- (V : G => *) : * => Bot --> Bot
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | bot = step (Cast-Bot-R nfA λ ())

------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A ≠ Dyn
------ (V : G => *) ▷ A'
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq
  with cast-lemma-3 {n} {e₁} {A'} {G₁} W j
-------- A' = Dyn
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} (CastA{A' = A''} j' x' x₁' y') x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq | inj₁ eq' rewrite eq'
  with cast-trivial-just-inv{A = Dyn}{B = A}{C = B} x₁
---------- Dyn = A' = A, contradiction, A ≠ Dyn
...  | inj₁ eq'' = contradiction (sym eq'') ¬eq
---------- Dyn = A' = S{V : A}, contradiction, S{V : A} ≠ Dyn
...  | inj₂ (fst , snd , ())
-------- A' = S{V : Dyn}
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq | inj₂ (fst , snd , thd) rewrite thd
  with cast-trivial-just-inv{A = Single snd Dyn}{B = A}{C = B} x₁
---------- S{V : Dyn} = A' = A, contradiction, A is in Nf, Single not Nf
...  | inj₁ eq'' = contradiction (sym eq'') (¬Single-nf nfA fst snd Dyn)
---------- S{V : Dyn} = A' = S{W : A}, contradiction, Dyn ≠ A
...  | inj₂ (fst' , snd' , thd') = contradiction (sym (proj₂ (Single-equiv thd'))) ¬eq
------------------------------------------------------------------------------------------------
-- (V : Pi A° B° => Pi A°° B°°) : A => B
---- (V : Pi A° B° => Pi A°° B°°) ▷ A'
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)}
  with cast-lemma-3 {n} {e₁} {A'} {Pi A° B°} {Pi A°° B°°} W j
------ Pi A°° B°° = A'
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ rewrite x₂
  with cast-trivial-just-inv{A = Pi A°° B°°}{B = A}{C = B} x₁
-------- Pi A°° B°° = A' = A
...  | inj₁ x₃ rewrite (sym x₃)
     with B ≡ᵀ? Dyn
---------- B = Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | yes eq
  rewrite eq
  with TyG? (Pi A°° B°°)
------------ TyG (Pi A°° B°°)
-------------- Value: (V : Pi A° B° => Pi * *) : Pi * * => *
...  | yes tyg = result (RValue (VCast (VCastFun{nfA = nfA°}{nfA' = nfA°°} W) tyg))
------------ ¬ TyG (Pi A°° B°°) (and in Nf)
...  | no ¬tyg
     with nf-not-g-⊆ {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with produce-ground-ng {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ((λ ())) ok
-------------- (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => * --> ((V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => G) : G => *
...        | fst , snd , thd , fth = step (Cast-Factor-L{v = VCastFun{nfA = nfA°}{nfA' = nfA°°} W}{g = snd}{nfA = NfPi{nfA = nfA°°}} thd ok fth (λ ()))
-- (V : Pi A° B° => Pi A°° B°°) : A => B
---- (V : Pi A° B° => Pi A°° B°°) ▷ A'
------ Pi A°° B°° = A'
-------- Pi A°° B°° = A' = A
---------- B ≠ Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result nfB | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq
------------ Pi A°° B°° ~ B
  with x
... | AConsDynR x₄ = contradiction refl ¬eq
... | AConsRefl x₄ = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
... | AConsPi unf unf₁
    with nfB
...    | NfPi{nfA = nfA'} = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA'} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
------------------------------------------------------------------------------------------------
-- (V : Pi A° B° => Pi A°° B°°) : A => B
---- (V : Pi A° B° => Pi A°° B°°) ▷ A'
------ S{V : Pi A°° B°°} = A'
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) rewrite thd
  with cast-trivial-just-inv{A = Single snd (Pi A°° B°°)}{B = A}{C = B} x₁
-------- S{V : Pi A°° B°°} = A' = A
---------- contradiction, A nf, Single not nf
...  | inj₁ x₂ = contradiction (sym x₂) (¬Single-nf nfA fst snd (Pi A°° B°°))
-------- S{V : Pi A°° B°°} = A' = S{V : A}
-------- => Pi A°° B°° = A, hence analogous to cases for Pi A°° B°° = A' = A
...  | inj₂ (fst' , snd' , thd')
     rewrite (sym (proj₂ (Single-equiv thd')))
     with B ≡ᵀ? Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)}
                                                                                                        | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | yes eq
  rewrite eq
  with TyG? (Pi A°° B°°)
...  | yes tyg = result (RValue (VCast (VCastFun{nfA = nfA°}{nfA' = nfA°°} W) tyg))
...  | no ¬tyg
     with nf-not-g-⊆ {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with produce-ground-ng {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ((λ ())) ok
...        | fst° , snd° , thd° , fth° = step (Cast-Factor-L{v = VCastFun{nfA = nfA°}{nfA' = nfA°°} W}{g = snd°}{nfA = NfPi{nfA = nfA°°}} thd° ok fth° (λ ()))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq
  with x
... | AConsDynR x₄ = contradiction refl ¬eq
... | AConsRefl x₄ = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
... | AConsPi unf unf₁
    with nfB
...    | NfPi{nfA = nfA'} = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA'} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))                                                                                                     
------------------------------------------------------------------------------------------------
-- V : A => B, V ≠ W : C => D
progress {n} {Cast e nA nB} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue W) | result nfA | result nfB | other-v {e = e} {neq}
  with nA ≡ᵀ? Dyn
---- A can't be Dyn
...  | yes eq rewrite eq = contradiction (CastA{ok = ok}{ok'} j x x₁ y) (cast-lemma-1 {n} {e} {T} neq W)
...  | no ¬eq
     with nB ≡ᵀ? Dyn
------ B = Dyn
...     | yes eq' rewrite eq'
-------- Tyg A
        with TyG? nA
---------- Value (V : A => *)
...        | yes tyg = result (RValue (VCast W tyg))
---------- ¬ TyG A (and in nf)
...        | no ¬tyg
           with (nf-not-g-⊆ {n} {nA} nfA ¬tyg)
------------ A = Dyn contradicts A ≠ Dyn
...           | dyn = contradiction refl ¬eq
------------ V : Bot => * --> Blame
...           | bot = step Cast-Bot-L
...           | pi x₂ x₃
              with produce-ground-ng {n} {nA} (pi x₂ x₃) (λ ()) (λ ()) ok
------------ V : Pi A B => * --> (V : Pi A B => G) : G => *              
...              | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | sigma x₂ x₃
  with produce-ground-ng {n} {nA} (sigma x₂ x₃) (λ ()) (λ ()) ok
------------ V : Sigma A B => * --> (V : Sigma A B => G) : G => *    
...  | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))
-- V : A => B, V ≠ W : C => D, A ≠ *, B ≠ *
---- (V : Bot => Bot) --> Blame
progress {n} {Cast e Bot .Bot} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Bot-L)
---- Contradictions to A ≠ * and B ≠ *
progress {n} {Cast e .Dyn nB} {T} (CastA {ok = ok} {ok'} j (AConsDynL x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq
progress {n} {Cast e nA .Dyn} {T} (CastA {ok = ok} {ok'} j (AConsDynR x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq'
progress {n} {Cast e Dyn .Dyn} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq
---- (V : UnitT => UnitT) --> V
progress {n} {Cast e UnitT .UnitT} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Unit{v = W})

---- (V : Label s => Label s) --> V
progress {n} {Cast e (Label x₂) .(Label x₂)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Label{v = W} (λ x → x))
---- Value: (V : Pi A B => Pi A B)
progress {n} {Cast e (Pi nA nA₁) .(Pi nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (NfPi{nfA = nfA}) | result (NfPi{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = result (RValue (VCastFun{nfA = nfA}{nfA' = nfA'} W))
---- Value: (V : Pi A B => Pi A' B')
progress {n} {Cast e .(Pi _ _) .(Pi _ _)} {T} (CastA {ok = ok} {ok'} j (AConsPi x x₂) x₁ y) | result (RValue W) | result (NfPi{nfA = nfA}) | result (NfPi{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = result (RValue (VCastFun{nfA = nfA}{nfA' = nfA'} W))
---- (V : Sigma A B => Sigma A B)
------ V = ⟨⟨ V' , W' ⟩⟩
progress {n} {Cast e (Sigma nA nA₁) .(Sigma nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} |  no ¬eq | no ¬eq'
  with cast-lemma-2 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y)
progress {n} {Cast e (Sigma nA nA₁) .(Sigma nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue (VProd V W)) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' | (fst , snd , thd , fth)
-------- ⟨⟨ V' , W' ⟩⟩ : Sigma A B => Sigma A B --> let x = (V' : A => A) in ⟨⟨ x , W' : (B[V'/x] => B) ⟩⟩
  = step (Cast-Pair{w = W})
---- (V : Sigma A B => Sigma A' B')
------ V = ⟨⟨ V' , W' ⟩⟩
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue W) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq'
  with cast-lemma-2 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y)
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue (VProd V W)) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' |  (fst , snd , thd , fth)
-------- ⟨⟨ V' , W' ⟩⟩ : Sigma A B => Sigma A B --> let x = (V' : A => A') in ⟨⟨ x , W' : (B[V'/x] => B') ⟩⟩  
  = step (Cast-Pair{w = W})

-}
