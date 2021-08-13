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

cast-result : {n : ℕ} {A' A B : Ty {n}} → Is-just (cast A' A B) → (Data.Maybe.fromMaybe Bot (cast A' A B) ≡ B) ⊎ (∃[ e ](Data.Maybe.fromMaybe Bot (cast A' A B) ≡ Single e B × Val e)) ⊎ (Data.Maybe.fromMaybe Bot (cast A' A B) ≡ Bot)
cast-result {n} {Single e A'} {A} {B} isjust
  with A ≡ᵀ? A'
cast-result {n} {Single e A'} {A} {B} () | no ¬eq
...  | yes eq
     with evaluate-full (gas 1000) (Cast e A B)
...     | fst , result (RValue x) = inj₂ (inj₁ (fst , refl , x)) -- inj₂ (inj₁ (fst , refl))
...     | .Blame , result RBlame = inj₂ (inj₂ refl)
...     | fst , stuck = inj₂ (inj₂ refl)
...     | fst , out-of-gas = inj₂ (inj₂ refl)

cast-result {n} {UnitT} {A} {B} isjust
  with A ≡ᵀ? UnitT
cast-result {n} {UnitT} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {Label x} {A} {B} isjust
  with A ≡ᵀ? Label x
cast-result {n} {Label x} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {Pi A' A''} {A} {B} isjust
  with A ≡ᵀ? Pi A' A''
cast-result {n} {Pi A' A''} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {Sigma A' A''} {A} {B} isjust
  with A ≡ᵀ? Sigma A' A''
cast-result {n} {Sigma A' A''} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {CaseT x f} {A} {B} isjust
  with A ≡ᵀ? CaseT x f
cast-result {n} {CaseT x f} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {Bot} {A} {B} isjust
  with A ≡ᵀ? Bot
cast-result {n} {Bot} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl
cast-result {n} {Dyn} {A} {B} isjust
  with A ≡ᵀ? Dyn
cast-result {n} {Dyn} {A} {B} () | no ¬eq
...  | yes eq = inj₁ refl

dyn-nf-st : {n : ℕ} {e e' : Exp {n}} → Val e → [] ⊢ e ▷ (Single e' Dyn) → ∃[ e' ](∃[ G ](e ≡ Cast e' G Dyn × Val e' × TyG G))
dyn-nf-st {n} {(Cast e G Dyn)} {e'} (VCast V x₁) (CastA j (fst , snd)) = e , G , refl , V , x₁
dyn-nf-st {n} {(Cast e (Pi A B) (Pi A' B'))} {e'} (VCastFun V) (CastA{A' = A°} j (fst , snd))
  with cast-result{A' = A°}{A = Pi A B}{B = Pi A' B'} fst
... | inj₁ x = contradiction (≡-trans snd x) (λ ())
... | inj₂ (inj₁ (fst₁ , snd₁ , thd₁)) = contradiction (≡-trans snd snd₁) λ ()
... | inj₂ (inj₂ y) = contradiction (≡-trans snd y) (λ ())

dyn-nf : {n : ℕ} {e : Exp {n}} → Val e → [] ⊢ e ▷ Dyn → ∃[ e' ](∃[ G ](e ≡ Cast e' G Dyn × Val e' × TyG G))
dyn-nf {n} {(Cast e G Dyn)} (VCast V x₁) (CastA j (fst , snd)) = e , G , refl , V , x₁
dyn-nf {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) (CastA{A' = A°} j (fst , snd))
  with cast-result{A' = A°}{A = Pi A B}{B = Pi A' B'} fst
... | inj₁ x = contradiction (≡-trans snd x) (λ ())
... | inj₂ (inj₁ (fst₁ , snd₁ , thd₁)) = contradiction (≡-trans snd snd₁) λ ()
... | inj₂ (inj₂ y) = contradiction (≡-trans snd y) (λ ())

prod-nf : {n : ℕ} {A B A' B' : Ty {n}} {C : Ty {n}} {e : Exp {n}} → Val e → [] ⊢ Cast e (Sigma A B) (Sigma A' B') ▷ C
                                                                  → ∃[ e' ](∃[ e'' ](e ≡ ProdV e' e''))
prod-nf {n} {A} {B} {A'} {B'} {C} {.UnitE} VUnit (CastA (UnitAI x) (() , snd))
prod-nf {n} {A} {B} {A'} {B'} {C} {.(LabI _)} VLab (CastA (LabAI x) (() , snd))
prod-nf {n} {A} {B} {A'} {B'} {C} {.(Abs _)} VFun (CastA (PiAI j) (() , snd))
prod-nf {n} {A} {B} {A'} {B'} {C} {(ProdV e e')} (VProd V V₁) (CastA j (fst , snd)) = e , e' , refl
prod-nf {n} {A} {B} {A'} {B'} {C} {(Cast e G Dyn)} (VCast V x) (CastA (CastA{A' = A''} j (fst' , snd')) (fst , snd))
  rewrite snd'
  with cast-result{A' = A''}{A = G}{B = Dyn} fst'
prod-nf {n} {A} {B} {A'} {B'} {C} {(Cast e G Dyn)} (VCast V x) (CastA (CastA{A' = A''} j (fst' , snd')) (fst , snd)) | inj₁ x₁ rewrite x₁
  with fst
...  | ()  
prod-nf {n} {A} {B} {A'} {B'} {C} {(Cast e G Dyn)} (VCast V x) (CastA (CastA{A' = A''} j (fst' , snd')) (fst , snd)) | inj₂ (inj₁ (fst* , snd* , thd*)) rewrite snd*
  with fst
...  | ()  
prod-nf {n} {A} {B} {A'} {B'} {C} {(Cast e G Dyn)} (VCast V x) (CastA (CastA{A' = A''} j (fst' , snd')) (fst , snd)) | inj₂ (inj₂ y) rewrite y
  with fst
...  | ()  
prod-nf {n} {A} {B} {A'} {B'} {C} {(Cast e (Pi A` B`) (Pi A`` B``))} (VCastFun V) (CastA (CastA{A' = A''} j (fst' , snd')) (fst , snd))
  rewrite snd'
  with cast-result{A' = A''}{A = Pi A` B`}{B = Pi A`` B``} fst'
prod-nf {n} {A} {B} {A'} {B'} {C} {Cast e (Pi A` B`) (Pi A`` B``)} (VCastFun V) (CastA {A' = A'''} (CastA {A' = A''} j (fst' , snd')) (fst , snd)) | inj₁ x rewrite x
  with fst
... | ()
prod-nf {n} {A} {B} {A'} {B'} {C} {Cast e (Pi A` B`) (Pi A`` B``)} (VCastFun V) (CastA {A' = A'''} (CastA {A' = A''} j (fst' , snd')) (fst , snd)) | inj₂ (inj₁ (fst* , snd* , thd*)) rewrite snd*
  with fst
... | ()
prod-nf {n} {A} {B} {A'} {B'} {C} {Cast e (Pi A` B`) (Pi A`` B``)} (VCastFun V) (CastA {A' = A'''} (CastA {A' = A''} j (fst' , snd')) (fst , snd)) | inj₂ (inj₂ y) rewrite y
  with fst
... | ()

cast-invert' : {n : ℕ} {A' : Ty {n}} {A B : Ty {n}} → Is-just (cast A' A B) → (A' ≡ A ⊎ ∃[ e ](A' ≡ Single e A))
cast-invert' {n} {Single x A'} {A} {B} isjust
  with A ≡ᵀ? A'
cast-invert' {n} {Single x A'} {A} {B} () | no ¬eq
...  | yes eq rewrite eq = inj₂ (x , refl)
cast-invert' {n} {UnitT} {A} {B} isjust
  with A ≡ᵀ? UnitT
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {UnitT} {A} {B} () | no ¬eq
cast-invert' {n} {Label x} {A} {B} isjust
  with A ≡ᵀ? Label x
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {Label x} {A} {B} () | no ¬eq
cast-invert' {n} {Pi A' A''} {A} {B} isjust
  with A ≡ᵀ? Pi A' A''
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {Pi A' A''} {A} {B} () | no ¬eq
cast-invert' {n} {Sigma A' A''} {A} {B} isjust
  with A ≡ᵀ? Sigma A' A''
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {Sigma A' A''} {A} {B} () | no ¬eq
cast-invert' {n} {CaseT x f} {A} {B} isjust
  with A ≡ᵀ? CaseT x f
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {CaseT x f} {A} {B} () | no ¬eq
cast-invert' {n} {Bot} {A} {B} isjust
  with A ≡ᵀ? Bot
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {Bot} {A} {B} () | no ¬eq
cast-invert' {n} {Dyn} {A} {B} isjust
  with A ≡ᵀ? Dyn
...  | yes eq = inj₁ (sym eq)
cast-invert' {n} {Dyn} {A} {B} () | no ¬eq

cast-invert : {n : ℕ} {B : Ty {n}} {A C : Ty {n}} {e : Exp {n}} → Val e → [] ⊢ Cast e A B ▷ C → (C ≡ B ⊎ (∃[ e ](C ≡ Single e B)) ⊎ C ≡ Bot)
cast-invert {n} {B} {A} {C} {e} V (CastA{A = A}{B = B}{A' = A'} j (fst , snd))
  with cast-result{n}{A'}{A}{B} fst
...  | inj₁ x = inj₁ (≡-trans snd x)
...  | inj₂ (inj₁ (fst₁ , snd₁ , thd₁)) = inj₂ (inj₁ (fst₁ , (≡-trans snd snd₁)))
...  | inj₂ (inj₂ y) = inj₂ (inj₂ (≡-trans snd y))

cast-invert-bot : {n : ℕ} {A B : Ty {n}} {A' : Ty {n}} → Bot ≢ B → Is-just (cast A' A B) → Bot ≡ Data.Maybe.fromMaybe Bot (cast A' A B) → Σ (Exp {n}) (λ e → A' ≡ Single e A)
cast-invert-bot {n} {A} {B} {Single x A'} neq isjust eq
  with A ≡ᵀ? A'
...  | yes eq' rewrite eq' = x , refl
cast-invert-bot {n} {A} {B} {Single x A'} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {UnitT} neq isjust eq
  with A ≡ᵀ? UnitT
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {UnitT} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {Label x} neq isjust eq
  with A ≡ᵀ? Label x
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {Label x} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {Pi A' A''} neq isjust eq
  with A ≡ᵀ? Pi A' A''
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {Pi A' A''} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {Sigma A' A''} neq isjust eq
  with A ≡ᵀ? Sigma A' A''
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {Sigma A' A''} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {CaseT x f} neq isjust eq
  with A ≡ᵀ? CaseT x f
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {CaseT x f} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {Bot} neq isjust eq
  with A ≡ᵀ? Bot
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {Bot} neq () eq | no ¬eq'
cast-invert-bot {n} {A} {B} {Dyn} neq isjust eq
  with A ≡ᵀ? Dyn
...  | yes eq' = contradiction eq neq
cast-invert-bot {n} {A} {B} {Dyn} neq () eq | no ¬eq'

no-reduce-nftype-step : {n : ℕ} {T : Ty {n}} → (nfT : TyNf T) → (evaluate-step-type T) ≡ (result (RNf nfT))
no-reduce-nftype-step {n} {.Bot} NfBot = refl
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

cast-value-ground-dyn : {n : ℕ} {e : Exp {n}} {G : Ty {n}} → Val e → TyG G → Is-just (cast (Single e G) G Dyn) → Data.Maybe.fromMaybe Bot (cast (Single e G) G Dyn) ≡ Single (Cast e G Dyn) Dyn
cast-value-ground-dyn {n} {e} {G} V tyg isjust
  with G ≡ᵀ? G
...  | no ¬eq = contradiction refl ¬eq
...  | yes eq rewrite (no-reduce-value-step V) | (no-reduce-nftype-step (TyG⊂TyNf tyg))
     with G ≡ᵀ? Dyn
...     | yes eq' rewrite eq' = contradiction tyg (λ ())
...     | no ¬eq'
        with TyG? G
...        | no ¬tygg = contradiction tyg ¬tygg
...        | yes tygg = refl

single-always-value-cast-pi : {n : ℕ} {e : Exp {n}} {A'' T : Ty {n}} {A B A' B' : Ty {n}} → Is-just (cast A'' (Pi A B) (Pi A' B'))
                                                                                          → Data.Maybe.fromMaybe Bot (cast A'' (Pi A B) (Pi A' B')) ≡ Single e T → ∃[ e' ](A'' ≡ Single e' (Pi A B) × Val e)
single-always-value-cast-pi {n} {e} {Single e' A''} {T} {A} {B} {A'} {B'} isjust eq
  with (Pi A B) ≡ᵀ? A''
...  | no ¬eq' = contradiction eq λ ()
...  | yes eq'
     with evaluate-full (gas 1000) (Cast e' (Pi A B) (Pi A' B'))
single-always-value-cast-pi {n} {.fst} {Single e' A''} {.(Pi A' B')} {A} {B} {A'} {B'} isjust refl | yes eq' | fst , result (RValue x) rewrite eq' = e' , (refl , x)
single-always-value-cast-pi {n} {e} {Pi A'' B''} {T} {A} {B} {A'} {B'} isjust eq
  with (Pi A B ≡ᵀ? Pi A'' B'')
...  | yes eq' = contradiction eq (λ ())
single-always-value-cast-pi {n} {e} {Pi A'' B''} {T} {A} {B} {A'} {B'} () eq | no ¬eq'

single-always-value-cast : {n : ℕ} {e : Exp {n}} {A T : Ty {n}} {G : Ty {n}} {tyg : TyG G} → Is-just (cast A G Dyn)
                                                                                           → Data.Maybe.fromMaybe Bot (cast A G Dyn) ≡ Single e T → ∃[ e' ](A ≡ Single e' G × Val e)
single-always-value-cast {n} {e} {Single e' A} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? A
...  | no ¬eq' = contradiction eq (λ ())
...  | yes eq'
     with evaluate-full (gas 1000) (Cast e' G Dyn)
single-always-value-cast {n} {.fst} {Single e' A} {.Dyn} {G} {tyg} isjust refl | yes eq' | fst , result (RValue x) rewrite eq' = e' , (refl , x)
single-always-value-cast {n} {e} {UnitT} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? UnitT
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {UnitT} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {Label x} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? Label x
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {Label x} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {Pi A A₁} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? Pi A A₁
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {Pi A A₁} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {Sigma A A₁} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? Sigma A A₁
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {Sigma A A₁} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {CaseT x f} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? CaseT x f
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {CaseT x f} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {Bot} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? Bot
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {Bot} {T} {G} {tyg} () eq | no ¬eq'
single-always-value-cast {n} {e} {Dyn} {T} {G} {tyg} isjust eq
  with G ≡ᵀ? Dyn
...  | yes eq' = contradiction eq λ ()
single-always-value-cast {n} {e} {Dyn} {T} {G} {tyg} () eq | no ¬eq'

single-always-value : {n : ℕ} {e e' : Exp {n}} {T : Ty {n}} → Val e → [] ⊢ e ▷ Single e' T → Val e'
single-always-value {n} {(Cast e G Dyn)} {e'} {T} (VCast V x₁) (CastA{A' = A'} j (fst , snd))
  with single-always-value-cast{A = A'}{G = G}{tyg = x₁} fst (sym snd)
...  | fst' , fst₁' , snd' = snd'
single-always-value {n} {(Cast e (Pi A B) (Pi A' B'))} {e'} {T} (VCastFun V) (CastA{A' = A''} j (fst , snd))
  with (cast-result{A' = A''}{A = Pi A B}{B = Pi A' B'} fst)
...  | inj₁ x₁ = contradiction (≡-trans snd x₁) λ ()
...  | inj₂ (inj₂ y) = contradiction (≡-trans snd y) λ ()
...  | inj₂ (inj₁ x₁)
     with single-always-value-cast-pi{A'' = A''}{A = A}{B = B}{A' = A'}{B' = B'} fst (sym snd)
...     | fst' , fst₁' , snd' = snd'
single-always-value {n} {.UnitE} {.UnitE} {.UnitT} V (UnitAI x) = VUnit
single-always-value {n} {.(LabI _)} {.(LabI _)} {.(Label ⁅ _ ⁆)} V (LabAI x) = VLab

cast-value-pi-type : {n : ℕ} {e : Exp {n}} {A B A' B' : Ty {n}} {T : Ty {n}} → Val e → [] ⊢ Cast e (Pi A B) (Pi A' B') ▷ T → (T ≡ (Pi A' B') ⊎ ∃[ e' ](T ≡ Single e' (Pi A' B') × Val e'))
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = A''} j (fst , snd))
  with (cast-result{A' = A''}{A = Pi A B}{B = Pi A' B'} fst)
...  | inj₁ x = inj₁ (≡-trans snd x)
...  | inj₂ (inj₁ (fst₁ , fst₂ , snd₁)) = inj₂ (fst₁ , ((≡-trans snd fst₂) , snd₁))
...  | inj₂ (inj₂ x)
     with (cast-invert-bot{A = (Pi A B)}{B = (Pi A' B')}{A' = A''} (λ ()) fst (sym x))
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl
  with (Pi A B ≡ᵀ? Pi A B)
...  | no ¬eq = contradiction refl ¬eq
...  | yes eq
     with (single-always-value V j)
...     | V'
        rewrite (no-reduce-value-step V')
        with TyG? (Pi A B) | TyG? (Pi A' B')
...        | yes GPi | yes GPi = contradiction x (λ ())
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | yes GPi | no ¬tyg'
  with A' ≡ᵀ? Dyn
...  | no ¬eq' = inj₂ (((Cast fst' (Pi Dyn Dyn) (Pi A' B'))) , (snd , (VCastFun V')))
...  | yes eq'
     with B' ≡ᵀ? Dyn
...     | no ¬eq'' = inj₂ (((Cast fst' (Pi Dyn Dyn) (Pi A' B'))) , (snd , (VCastFun V')))
...     | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg'
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | yes GPi
  with A ≡ᵀ? Dyn
...  | no ¬eq' = inj₂ (((Cast fst' (Pi A B) (Pi Dyn Dyn))) , (snd , (VCastFun V')))
...  | yes eq'
     with B ≡ᵀ? Dyn
...     | no ¬eq'' = inj₂ (((Cast fst' (Pi A B) (Pi Dyn Dyn))) , (snd , (VCastFun V')))
...     | yes eq'' rewrite eq' | eq'' = contradiction GPi ¬tyg
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | no ¬tyg'
  with A ≡ᵀ? Dyn | A' ≡ᵀ? Dyn
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | no ¬tyg' | yes eq' | yes eq''
  with B ≡ᵀ? Dyn | B' ≡ᵀ? Dyn
...  | yes eq''' | yes eq'''' rewrite eq' | eq'' | eq''' | eq'''' = contradiction GPi ¬tyg
...  | yes eq''' | no ¬eq'''' rewrite eq' | eq'' | eq''' = contradiction GPi ¬tyg
...  | no ¬eq''' | yes eq'''' rewrite eq' | eq'' | eq'''' = contradiction GPi ¬tyg'
...  | no ¬eq''' | no ¬eq'''' = inj₂ (((Cast fst' (Pi A B) (Pi A' B'))) , (snd , (VCastFun V')))  
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | no ¬tyg' | yes eq' | no ¬eq''
  with B ≡ᵀ? Dyn | B' ≡ᵀ? Dyn
...  | yes eq''' | yes eq'''' rewrite eq' | eq''' | eq'''' = contradiction GPi ¬tyg
...  | yes eq''' | no ¬eq'''' rewrite eq' | eq''' = contradiction GPi ¬tyg
...  | no ¬eq''' | yes eq'''' rewrite eq' | eq'''' = inj₂ (((Cast fst' (Pi Dyn B) (Pi A' Dyn))) , (snd , (VCastFun V')))
...  | no ¬eq''' | no ¬eq''''  = inj₂ (((Cast fst' (Pi A B) (Pi A' B'))) , (snd , (VCastFun V')))  
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | no ¬tyg' | no ¬eq' | yes eq''
  with B ≡ᵀ? Dyn | B' ≡ᵀ? Dyn
...  | yes eq''' | yes eq'''' rewrite eq'' | eq''' | eq'''' = contradiction GPi ¬tyg'
...  | yes eq''' | no ¬eq'''' rewrite eq'' | eq''' = inj₂ ((Cast fst' (Pi A Dyn) (Pi Dyn B')) , (snd , (VCastFun V')))
...  | no ¬eq''' | yes eq'''' rewrite eq'' | eq'''' = contradiction GPi ¬tyg'
...  | no ¬eq''' | no ¬eq'''' = inj₂ ((Cast fst' (Pi A B) (Pi A' B')) , (snd , VCastFun V'))  
cast-value-pi-type {n} {e} {A} {B} {A'} {B'} {T} V (CastA{A' = Single fst' (Pi A B)} j (fst , snd)) | inj₂ (inj₂ x) | fst' , refl | yes eq | V' | no ¬tyg | no ¬tyg' | no ¬eq' | no ¬eq'' = inj₂ (((Cast fst' (Pi A B) (Pi A' B'))) , (snd , (VCastFun V')))

cast-value-ground-dyn-type : {n : ℕ} {e : Exp {n}} {G T : Ty {n}} → Val e → TyG G → [] ⊢ Cast e G Dyn ▷ T → (T ≡ Dyn ⊎ ∃[ e' ](T ≡ Single e' Dyn))
cast-value-ground-dyn-type {n} {e} {G} {T} V tyg (CastA{A' = A'} j (fst , snd))
  with (cast-result{A' = A'}{A = G}{B = Dyn} fst)
...  | inj₁ x = inj₁ (≡-trans snd x)
...  | inj₂ (inj₁ (fst₁ , fst₂ , snd₁)) = inj₂ (fst₁ , (≡-trans snd fst₂))
-- cast-invert-bot : {n : ℕ} {A B : Ty {n}} {A' : Ty {n}} → Bot ≢ B → Is-just (cast A' A B) → Bot ≡ Data.Maybe.fromMaybe Bot (cast A' A B) → Σ (Exp {n}) (λ e → A' ≡ Single e A)
...  | inj₂ (inj₂ y)
     with cast-invert-bot{A = G}{B = Dyn}{A' = A'} (λ ()) fst (sym y)
cast-value-ground-dyn-type {n} {e} {G} {T} V tyg (CastA{A' = Single fst₁ G} j (fst , snd)) | inj₂ (inj₂ y) | fst₁ , refl
  with G ≡ᵀ? G
cast-value-ground-dyn-type {n} {e} {G} {T} V tyg (CastA{A' = Single fst₁ G} j (() , snd)) | inj₂ (inj₂ y) | fst₁ , refl | no ¬eq
...  | yes eq
     with (single-always-value V j)
...     | V'
        rewrite (no-reduce-value-step V') | (no-reduce-nftype-step (TyG⊂TyNf tyg))
        with G ≡ᵀ? Dyn
...        | yes eq' rewrite eq' = contradiction tyg (λ ())
...        | no ¬eq'
           with TyG? G
...           | no ¬tyg' = contradiction tyg ¬tyg'
...           | yes tyg' = inj₂ ((Cast fst₁ G Dyn) , snd)

------------------------------------------------------------------------
-- Canonical forms

cf-not-bot : {n : ℕ} {e : Exp {n}} → Val e → ¬ ([] ⊢ e ▷ Bot)
cf-not-bot {n} {.(Cast _ _ Dyn)} (VCast V x₁) (CastA{ok = ok}{ok' = ok'} j x)
  with (cast-value-ground-dyn-type V x₁ (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()
cf-not-bot {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun V) (CastA{ok = ok}{ok' = ok'} j x)
  with (cast-value-pi-type V (CastA{ok = ok}{ok' = ok'} j x))
...  | inj₁ ()
...  | inj₂ ()

cf-not-bot-single : {n : ℕ} {e : Exp {n}} → Val e → (e' : Exp {n}) → ¬ ([] ⊢ e ▷ Single e' Bot)
cf-not-bot-single {n} {.(Cast _ _ Dyn)} (VCast v x) e' (CastA {A' = A'}{ok = ok}{ok' = ok'} j (fst , snd))
  with cast-invert v (CastA {ok = ok}{ok' = ok'}  j (fst , snd))
...  | inj₂ (inj₁ ())
...  | inj₂ (inj₂ ())
cf-not-bot-single {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun v) e' (CastA {A' = A'}{ok = ok}{ok' = ok'}  j (fst , snd))
  with cast-invert v (CastA{ok = ok}{ok' = ok'} j (fst , snd))
...  | inj₂ (inj₁ ())
...  | inj₂ (inj₂ ())

cf-not-bot-corollary : {n : ℕ} {e : Exp {n}} {B : Ty {n}} → Val e → (A : Ty {n}) → ¬ ([] ⊢ Cast e Bot B ▷ A)
cf-not-bot-corollary {n} {e} {B} V A (CastA {A' = Single x₁ A'} j x)
  with Bot ≡ᵀ? A'
cf-not-bot-corollary {n} {e} {B} V A (CastA {_} {_} {_} {Single x₁ A'} j ()) | no ¬eq
cf-not-bot-corollary {n} {e} {B} V A (CastA {A' = Single x₁ Bot} j x) | yes refl = contradiction j (cf-not-bot-single V x₁)
cf-not-bot-corollary {n} {e} {B} V A (CastA {A' = Bot} j x) = contradiction j (cf-not-bot V)


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
cf-pi {n} {(Cast e G Dyn)} {A} {B} (CastA{A' = A'} j (fst* , snd*)) (VCast V x₁)
  with cast-result{A' = A'}{A = G}{B = Dyn} fst*
...  | inj₁ x₂ = contradiction (≡-trans snd* x₂) λ () 
...  | inj₂ (inj₁ (fst , snd , thd)) = contradiction (≡-trans snd* snd) λ ()
...  | inj₂ (inj₂ y) = contradiction (≡-trans snd* y) λ ()
cf-pi {n} {(Cast e (Pi A' B') (Pi A'' B''))} {A} {B} (CastA{A' = A°} j (fst* , snd*)) (VCastFun V)
  with cast-result{A' = A°}{A = (Pi A' B')}{B = (Pi A'' B'')} fst*
...  | inj₁ x₁ rewrite (≡-trans snd* x₁) = inj₂ (e , (A' , (B' , refl)))
...  | inj₂ (inj₁ (fst , snd , thd)) = contradiction (≡-trans snd* snd) λ ()
...  | inj₂ (inj₂ y) = contradiction (≡-trans snd* y) λ ()
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
progress-types {n} {.Bot} (BotF x) = result (RNf NfBot)
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

progress {n} {(Cast e A B)} {T} (CastA{B' = B'}{ok = ok}{ok' = ok'} j x)
  with progress j
...  | step st = step (ξ-Cast st)
...  | result RBlame = step Cast-Blame
...  | result (RValue v)
     with progress-types ok
...     | step st = step (Cast-Reduce-L{v = v} st)
...     | result (RNf nfA)
        with progress-types ok'
...        | step st = step (Cast-Reduce-R{v = v} nfA st)
...        | result (RNf nfB)
           with A ≡ᵀ? Dyn | B ≡ᵀ? Dyn
...           | yes eq | yes eq' rewrite eq | eq' = step (Cast-Dyn{v = v})
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | yes eq' rewrite eq'
  with TyG? A
...  | yes tyga = result (RValue (VCast v tyga))
...  | no ¬tyga
     with A ≡ᵀ? Bot
...     | yes eq` rewrite eq` = contradiction (CastA{ok = ok}{ok' = ok'} j x) (cf-not-bot-corollary v T)
...     | no ¬eq` = step (Cast-Factor-L{v = v}{nfA = TyNf×¬DynBot→TyNf-lim nfA (¬eq , ¬eq`)} ((A≢B→B≢A (¬TyG×TyNf-lim-in⇒match-inequiv ¬tyga (TyNf×¬DynBot→TyNf-lim nfA (¬eq , ¬eq`))))))
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq' rewrite eq
  with TyG? B
...  | no ¬tygb
     with B ≡ᵀ? Bot
...     | yes eq` rewrite eq` = step (Cast-Bot-R{v = v} nfA)
...     | no ¬eq` = step (Cast-Factor-R {v = v} {nfB = TyNf×¬DynBot→TyNf-lim nfB (¬eq' , ¬eq`)} (A≢B→B≢A (¬TyG×TyNf-lim-in⇒match-inequiv ¬tygb (TyNf×¬DynBot→TyNf-lim nfB (¬eq' , ¬eq`)))))
progress {n} {Cast e Dyn B} {T} (CastA {A' = A'} {ok = ok} {ok' = ok'} j (fst , snd)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes refl | no ¬eq' | yes tygb
  with (cast-invert'{A' = A'}{A = Dyn}{B = B} fst)
progress {n} {Cast e Dyn B} {T} (CastA {A' = A'} {ok = ok} {ok' = ok'} j (fst , snd)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes refl | no ¬eq' | yes tygb | inj₁ x rewrite x
  with (dyn-nf v j)
...  | fst' , snd' , thd' , fth' , sxth' rewrite thd'
  with []⊢ sxth' ≤ᵀ? tygb
...  | yes leq = step (Cast-Collapse{v = fth'}{tygG = sxth'}{tygH = tygb} leq)
...  | no ¬leq = step (Cast-Collide{v = fth'}{tygG = sxth'}{tygH = tygb} ¬leq)
progress {n} {Cast e Dyn B} {T} (CastA {A' = A'} {ok = ok} {ok' = ok'} j (fst , snd)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes refl | no ¬eq' | yes tygb | inj₂ (fst₁ , snd₁) rewrite snd₁
  with (dyn-nf-st v j)
...  | fst' , snd' , thd' , fth' , sxth' rewrite thd'
  with []⊢ sxth' ≤ᵀ? tygb
...  | yes leq = step (Cast-Collapse{v = fth'}{tygG = sxth'}{tygH = tygb} leq)
...  | no ¬leq = step (Cast-Collide{v = fth'}{tygG = sxth'}{tygH = tygb} ¬leq)

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq'
  with TyG? A | TyG? B
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB
  with A ≡ᵀ? Pi Dyn Dyn | B ≡ᵀ? Pi Dyn Dyn
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | yes eq₁ | yes eq₁'
  rewrite eq₁ | eq₁' = result (RValue (VCastFun v))
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | yes eq₁ | no ¬eq₁'
  rewrite eq₁
  with tygB
... | GUnit = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfUnit} λ ())
... | GLabel = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfLabel} λ ())
... | GPi = contradiction refl ¬eq₁'
... | GSigma = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma} λ ())
... | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BLabel}} λ ())
... | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BUnit}} λ ())
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | yes eq₁'
  rewrite eq₁'
  with tygA
... | GUnit = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfPi} λ ())
... | GLabel = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfPi} λ ())
... | GPi = contradiction refl ¬eq₁
... | GSigma = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi} λ ())
... | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfPi} ϱ)
    where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Pi Dyn Dyn)
          ϱ (ASubSingle () x x₁)
... | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfPi} ϱ)
    where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Pi Dyn Dyn)
          ϱ (ASubSingle () x x₁)
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | no ¬eq₁'
  with A ≡ᵀ? Sigma Dyn Dyn | B ≡ᵀ? Sigma Dyn Dyn
progress {n} {(Cast e (Sigma Dyn Dyn) (Sigma Dyn Dyn))} {T} (CastA{A' = A'}{ok = ok}{ok' = ok'} j (fst , snd)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | no ¬eq₁' | yes refl | yes refl
  with prod-nf v (CastA{ok = ok}{ok' = ok'} j (fst , snd))
...  | e` , e`` , eq rewrite eq
     with v
...     | VProd w w₁ = step (Cast-Pair{v = w}{w = w₁})

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | no ¬eq₁' | yes eq₂ | no ¬eq₂'
  rewrite eq₂
  with tygB
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfUnit} λ ())
...  | GLabel = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfLabel} λ ())
...  | GPi = contradiction refl ¬eq₁'
...  | GSigma = contradiction refl ¬eq₂'
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BLabel}} λ ())
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BUnit}} λ ())
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | no ¬eq₁' | no ¬eq₂ | yes eq₂'
  rewrite eq₂'
  with tygA
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfSigma} λ ())
...  | GLabel =  step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfSigma} λ ())
...  | GPi = contradiction refl ¬eq₁
...  | GSigma = contradiction refl ¬eq₂
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfSigma} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Sigma Dyn Dyn)
           ϱ (ASubSingle () x x₁)
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfSigma} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Sigma Dyn Dyn)
           ϱ (ASubSingle () x x₁)
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | yes tygB | no ¬eq₁ | no ¬eq₁' | no ¬eq₂ | no ¬eq₂'
  with []⊢ tygA ≤ᵀ? tygB
...  | yes leq = step (Cast-Sub{v = v}{tygG = tygA}{tygH = tygB}{neqG = ¬eq₁ , ¬eq₂}{neqH = ¬eq₁' , ¬eq₂'} leq)
...  | no ¬leq
     with (λ leqq → (Cast-Fail{v = v}{tynfA = TyG⊂TyNf-lim tygA}{tynfB = TyG⊂TyNf-lim tygB} leqq))
...     | w rewrite (TyG×TyNf-lim⇒match-equiv tygA (TyG⊂TyNf-lim tygA)) | (TyG×TyNf-lim⇒match-equiv tygB (TyG⊂TyNf-lim tygB)) = step (w ¬leq)

{-
        with (λ leqq → (Cast-Fail{v = v}{tynfA = nfA}{tynfB = nfB}{neq = (¬eq , (TyG-notBot tygA)) , ¬eq' , (TyG-notBot tygB)} leqq))
...        | w rewrite (TyG×TyNf⇒match-equiv{neq = (¬eq , (TyG-notBot tygA))} tygA nfA) | (TyG×TyNf⇒match-equiv{neq = ¬eq' , (TyG-notBot tygB)} tygB nfB) = step (w ¬leq)
-}

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} j x) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq' | yes tygA | no ¬tygB
  with ¬TyG×TyNf-in ¬tygB nfB
...  | Dyn = contradiction refl ¬eq'
...  | Bot = step (Cast-Bot-R{v = v} nfA)
-- A = Pi
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x
  with v | tygA
progress {n} {(Cast e UnitT (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfUnit) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfPi} λ ())
progress {n} {(Cast e (Label s) (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfLabel) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfPi} λ ())
progress {n} {(Cast e (Sigma Dyn Dyn) (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSigma
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi} λ ())
progress {n} {(Cast e (Single e' G) (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSingleLabel{s = s}
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfPi} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Pi Dyn Dyn)
        ϱ (ASubSingle constr () x₁)       
progress {n} {(Cast e (Single e' G) (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSingleUnit
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfPi} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Pi Dyn Dyn)
        ϱ (ASubSingle constr () x₁)   

progress {n} {(Cast e (Pi Dyn Dyn) (Pi A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GPi = result (RValue (VCastFun v))
-- A = Sigma
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x
  with v | tygA
progress {n} {(Cast e UnitT (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfUnit) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfSigma} λ ())
progress {n} {(Cast e (Label s) (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfLabel) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfSigma} λ ())
progress {n} {(Cast e (Pi Dyn Dyn) (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GPi
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma} λ ())
progress {n} {(Cast e (Single e' G) (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSingleLabel{s = s}
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfSigma} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Sigma Dyn Dyn)
        ϱ (ASubSingle constr () x₁)  
progress {n} {(Cast e (Single e' G) (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSingleUnit
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfSigma} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Sigma Dyn Dyn)
        ϱ (ASubSingle constr () x₁)
progress {n} {(Cast e (Sigma Dyn Dyn) (Sigma A B))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSigma
  with (prod-nf w (CastA{ok = ok}{ok' = ok'} z z'))
...  | e` , e`` , eq` rewrite eq`
     with w
...     | VProd w' w₁' = step (Cast-Pair{v = w'}{w = w₁'})     

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB
  with ¬TyG×TyNf-in ¬tygA nfA
...  | Dyn = contradiction refl ¬eq
...  | Bot = contradiction (CastA{ok = ok}{ok' = ok'} z z') ((cf-not-bot-corollary v T))
-- A = Pi
progress {n} {(Cast e (Pi A B) C)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x
  with tygB
progress {n} {(Cast e (Pi A B) UnitT)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfUnit} λ ())
progress {n} {(Cast e (Pi A B) (Label s))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfLabel} λ ())
progress {n} {(Cast e (Pi A B) (Sigma Dyn Dyn))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSigma
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma} λ ())
progress {n} {(Cast e (Pi A B) (Single e' G))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSingleLabel{s = s}
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BLabel{s = s}}} λ ())
progress {n} {(Cast e (Pi A B) (Single e' G))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSingleUnit
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BUnit}} λ ())

progress {n} {(Cast e (Pi A B) (Pi Dyn Dyn))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GPi
 = result (RValue (VCastFun v))
-- A = Sigma
progress {n} {(Cast e (Sigma A B) C)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x
  with tygB
progress {n} {(Cast e (Sigma A B) UnitT)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfUnit} λ ())
progress {n} {(Cast e (Sigma A B) (Label s))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfLabel} λ ())
progress {n} {(Cast e (Sigma A B) (Pi Dyn Dyn))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GPi
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi} λ ())
progress {n} {(Cast e (Sigma A B) (Single e' G))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSingleLabel{s = s}
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BLabel{s = s}}} λ ())
progress {n} {(Cast e (Sigma A B) (Single e' G))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSingleUnit
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BUnit}} λ ())

progress {n} {(Cast e (Sigma A B) (Sigma Dyn Dyn))} {T} (CastA{ok = ok}{ok' = ok'} z z') | result (RValue v) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma
  with (prod-nf v (CastA{ok = ok}{ok' = ok'} z z'))
...  | e` , e`` , eq` rewrite eq`
     with v
...     | VProd w w' = step (Cast-Pair{v = w}{w = w'})     

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB
  with ¬TyG×TyNf-in ¬tygA nfA | ¬TyG×TyNf-in ¬tygB nfB
...  | Bot | Pi x = contradiction (CastA{ok = ok}{ok' = ok'} z z') ((cf-not-bot-corollary v T))
...  | Bot | Sigma x = contradiction (CastA{ok = ok}{ok' = ok'} z z') ((cf-not-bot-corollary v T))
...  | Bot | Dyn = contradiction (CastA{ok = ok}{ok' = ok'} z z') ((cf-not-bot-corollary v T))
...  | Bot | Bot = step (Cast-Bot-R{v = v} nfA)
...  | Dyn | Bot = step (Cast-Bot-R{v = v} nfA)
...  | Pi x | Bot = step (Cast-Bot-R{v = v} nfA)
...  | Sigma x | Bot = step (Cast-Bot-R{v = v} nfA)
...  | Dyn | Dyn = contradiction refl ¬eq
...  | Dyn | Pi x = contradiction refl ¬eq
...  | Pi x | Dyn = contradiction refl ¬eq₁
...  | Dyn | Sigma x = contradiction refl ¬eq
...  | Sigma x | Dyn = contradiction refl ¬eq₁
progress {n} {(Cast e (Pi A B) (Sigma A' B'))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Pi x | Sigma x₁
  = step (Cast-Fail {v = v} {tynfA = NfPi} {tynfB = NfSigma}
             (λ ()))
progress {n} {(Cast e (Sigma A B) (Pi A' B'))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Pi x₁
  = step (Cast-Fail {v = v} {tynfA = NfSigma} {tynfB = NfPi}
             (λ ()))
progress {n} {(Cast e (Pi A B) (Pi A' B'))} {T} (CastA{ok = ok}{ok' = ok'} z z') | (result (RValue v)) | result (RNf NfPi) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Pi x | Pi x₁ = result (RValue (VCastFun v))
progress {n} {(Cast e (Sigma A B) (Sigma A' B'))} {T} (CastA{ok = ok}{ok' = ok'} z z') | result (RValue v) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁
  with (prod-nf v (CastA{ok = ok}{ok' = ok'} z z'))
...  | e` , e`` , eq` rewrite eq`
     with v
...     | VProd w w' = step (Cast-Pair{v = w}{w = w'})     
