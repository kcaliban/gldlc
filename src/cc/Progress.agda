------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
{-# OPTIONS --show-implicit #-}
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
-- Lemmas for cast function

-- evaluate-full (gas 1000) (Cast e A B)
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

cast-ineq-singleton : {n : ℕ} {i : Size} {A' A B : Ty {n} {i}} {e : Exp {n} {i}} → A ≢ A' → cast (Single e A') A B ≡ B
cast-ineq-singleton {n} {i} {A'} {A} {B} {e} neq
  with A ≡ᵀ? A'
...  | yes eq = contradiction eq neq
...  | no ¬eq = {!!}

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

cast-invert-bot : {n : ℕ} {i : Size} {A B : Ty {n} {i}} {A' : Ty {n} {↑ˡ i}} → Bot ≢ B → Bot ≡ cast A' A B → Σ (Exp {n}) (λ e → A' ≡ Single e A)
cast-invert-bot {n} {i} {A} {B} {Single x A'} neq eq
  with A ≡ᵀ? A'
...  | yes eq' rewrite eq' = x , refl
...  | no ¬eq'
     with cast-ineq-singleton{A' = A'}{A = A}{B = B} {!¬eq'!}
...     | eq'' = {!!}

-- cast-ineq-singleton : {n : ℕ} {A' A B : Ty {n}} {e : Exp {n}} → A ≢ A' → cast (Single e A') A B ≡ B

cast-invert-bot {n} {i} {A} {B} {UnitT} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {Label x} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {Pi A' A''} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {Sigma A' A''} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {CaseT x f} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {Bot} neq eq = {!!}
cast-invert-bot {n} {i} {A} {B} {Dyn} neq eq = {!!}

singleton-values : {n : ℕ} {e : Exp {n}} {A : Ty {n}} → Val e → [] ⊢ e ▷ A → Σ (Exp {n}) (λ e' → (Σ (Ty {n}) (λ B → ( A ≡ Single e' B)))) → (A ≡ Single UnitE UnitT) ⊎ (∃[ l ](A ≡ Single (LabI l) (Label ⁅ l ⁆)))
singleton-values {n} {.UnitE} {.(Single UnitE UnitT)} V (UnitAI x) (fst , snd , eq) = inj₁ refl
singleton-values {n} {.(LabI _)} {.(Single (LabI _) (Label ⁅ _ ⁆))} V (LabAI{l = l} x) (fst , snd , eq) = inj₂ (l , refl)
singleton-values {n} {(Cast e G Dyn)} {A} (VCast V x₁) (CastA{A' = A'} j x) (fst , snd , eq)
  with cast-invert-single{A' = A'}{A = G}{B = Dyn}  (fst , snd , ≡-trans (sym x) eq)
...   | inj₁ (fst' , snd' , eq')
      with singleton-values V j (fst' , snd' , eq')
...      | inj₁ eq'' = {!!}
...      | inj₂ (l , eq'') = {!!}
singleton-values {n} {.(Cast _ (Pi _ _) (Pi _ _))} {A} (VCastFun V) (CastA j x) (fst , snd , eq) = {!!}

-- cast-result : {n : ℕ} {A' A B : Ty {n}} → (cast A' G Dyn ≡ B) ⊎ (∃[ e ](cast A' A B ≡ Single e B)) ⊎ (cast A' A B ≡ Bot)

------------------------------------------------------------------------
-- Canonical forms

cf-label◁ : {n : ℕ} {s : Subset n} {e : Exp {n}} → [] ⊢ e ◁ Label s → Val e → ∃[ l ]((e ≡ LabI l) × l ∈ s)
cf-label◁ {n} {s} {.(LabI _)} (SubTypeA (LabAI {l = l} x) (ASubSingle (ASubLabel x₁) x₂ x₃)) VLab = (l , refl , ([l]⊆L⇒l∈L x₁))
cf-label◁ {n} {s} {.UnitE} (SubTypeA (UnitAI empty) (ASubSingle () x x₂)) v

-- cast-invert-bot : {n : ℕ} {i : Size} {A B : Ty {n} {i}} {A' : Ty {n} {↑ˡ i}} → Bot ≢ B → Bot ≡ cast A' A B → Σ (Exp {n}) (λ e → A' ≡ Single e A)
cf-label◁ {n} {s} {(Cast e G Dyn)} (SubTypeA (CastA{A' = A'} x x₂) ASubBot) (VCast v x₁)
  with cast-invert-bot{A = G}{B = Dyn}{A' = A'} (λ ()) x₂
...  | fst , snd = {!!}
cf-label◁ {n} {s} {.(Cast _ (Pi _ _) (Pi _ _))} (SubTypeA (CastA x x₂) ASubBot) (VCastFun v) = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubLabel x₁)) v = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubSingle x₁ x₃ x₄)) v = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubCaseLL x₁ ins x₃)) v = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubCaseXL x₁ x₃ x₄ x₅)) v = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubCaseBL x₁)) v = {!!}
cf-label◁ {n} {s} {.(Cast _ _ _)} (SubTypeA (CastA x x₂) (ASubCaseCL x₁)) v = {!!}



{-
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA{A = A}{A' = A'} j x x₁ y) (ASubLabel{L = s'} x₃)) (VCast v x₂)
  with (cast-result{n}{A'}{A}{Dyn} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym eq) y) λ () 
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) y) λ ()
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA{A = A}{A' = A'}{B' = Single V A₁} j x x₁ y) (ASubSingle leq x₃ x₄)) (VCast v x₂)
  with (cast-result{n}{A'}{A}{Dyn} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym eq) y) (λ ())
...  | inj₂ (fst , snd , thd)
     with A₁
...     | Single x₅ A'' = contradiction (≡-trans (sym thd) y) (λ ())
...     | Label x₅ = contradiction (≡-trans (sym thd) y) (λ ())
...     | CaseT x₅ f = contradiction (≡-trans (sym thd) y) (λ ())
...     | Bot = contradiction (≡-trans (sym thd) y) (λ ())
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA{A = A}{A' = A'} j x x₁ y) (ASubCaseLL x₃ x₄ leq)) (VCast v x₂)
  with (cast-result{n}{A'}{A}{Dyn} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym eq) y) (λ ())
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) y) λ ()  
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA j x x₁ y) (ASubCaseXL{eq = eq} leq x₃)) (VCast v x₂) = contradiction eq env-empty-++
-- cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA j x x₁ y) (ASubCaseXLDyn{eq = eq} x₃)) (VCast v x₂) = contradiction eq env-empty-++
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA{A = A}{A' = A'} j x x₁ y) ASubBot) (VCast v x₂)
  with (cast-result{n}{A'}{A}{Dyn} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym eq) y) (λ ())
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) y) (λ ())
cf-label◁ {n} {s} {.(Cast _ (Pi _ _) (Pi _ _))} (SubTypeA (CastA{A = Pi nA B}{A' = A'}{B' = A₁} j x x₁ y) leq) (VCastFun{nA' = nA'}{B' = B'} v)
  with (cast-result{n}{A'}{Pi nA B}{Pi nA' B'} x₁) | A₁
... | inj₁ x₂ | Single x₃ lol = contradiction (≡-trans (sym x₂) y) (λ ())
... | inj₁ x₂ | Label x₃ = contradiction (≡-trans (sym x₂) y) (λ ())
... | inj₁ x₂ | CaseT x₃ f = contradiction (≡-trans (sym x₂) y) (λ ())
... | inj₁ x₂ | Bot = contradiction (≡-trans (sym x₂) y) (λ ())
... | inj₂ (fst , snd , thd) | Label x₂ = contradiction (≡-trans (sym thd) y) (λ ())
... | inj₂ (fst , snd , thd) | CaseT x₂ f = contradiction (≡-trans (sym thd) y) (λ ())
... | inj₂ (fst , snd , thd) | Bot = contradiction (≡-trans (sym thd) y) (λ ())
... | inj₂ (fst , snd , thd) | Single x₂ A''
    with leq
...    | ASubSingle leq' x₃ x₄
       with A''
...       | Single x₅ A* = contradiction (≡-trans (sym thd) y) (λ ())
...       | Label x₅ = contradiction (≡-trans (sym thd) y) (λ ())
...       | CaseT x₅ f = contradiction (≡-trans (sym thd) y) (λ ())
...       | Bot = contradiction (≡-trans (sym thd) y) (λ ())
-}
{-
cf-pi : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → [] ⊢ e ▷ (Pi A B) → Val e → ∃[ e' ](e ≡ Abs e') ⊎ ∃[ N ](∃[ nA ](∃[ B' ](e ≡ Cast N (Pi nA B') (Pi A B))))
cf-pi {n} {.(Var _)} {A} {B} (VarA x ()) VVar
cf-pi {n} {(Abs e)} {A} {B} (PiAI j) VFun = inj₁ (e , refl)
cf-pi {n} {.(Cast _ _ Dyn)} {A} {B} (CastA{A = A'}{A' = A₁} j x₁ x₂ x₃) (VCast v x)
  with (cast-result{A' = A₁}{A = A'}{B = Dyn} x₂)
...  | inj₁ eq = contradiction (≡-trans (sym eq) x₃) (λ ())
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₃) (λ ())
cf-pi {n} {(Cast e (Pi nA B) (Pi nA' B'))} {A°} {B°} (CastA{A = Pi .nA .B}{B = Pi .nA' .B'}{A' = A'} j x x₁ x₂) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi nA B}{B = Pi nA' B'} x₁)
...  | inj₁ eq rewrite (≡-trans (sym eq) x₂) = inj₂ (e , nA , (B , refl))
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₂) (λ ())

cf-pi-⇓ : {n : ℕ} {e : Exp {n}} {D A B : Ty {n}} → [] ⊢ e ▷ D → [] ⊢ D ⇓ (Pi A B) → Val e → ∃[ e' ](e ≡ Abs e') ⊎ ∃[ N ](∃[ nA ](∃[ B' ](e ≡ Cast N (Pi nA B') (Pi A B))))
cf-pi-⇓ {n} {e} {.(Pi A B)} {A} {B} j AURefl-P v = cf-pi j v

cf-pi-⇓ {n} {.(Var _)} {.(Single _ _)} {A} {B} (VarA x ()) (AUSingle unf) VVar
cf-pi-⇓ {n} {.(Var _)} {.(CaseT _ _)} {A} {B} (VarA y ()) (AUCaseL x x₁ unf) VVar

cf-pi-⇓ {n} {.(LabI _)} {.(Single _ _)} {A} {B} (LabAI x) (AUSingle ()) VLab
cf-pi-⇓ {n} {.(Cast _ _ Dyn)} {.(Single _ _)} {A} {B} (CastA{A = A₁}{B = Dyn}{A' = A'} j x₁ x₂ x₃) (AUSingle unf) (VCast v x)
  with (cast-result{A' = A'}{A = A₁}{B = Dyn} x₂)
...  | inj₁ x₄ = contradiction (≡-trans (sym x₄) x₃) (λ ())
...  | inj₂ (fst , snd , thd) rewrite (proj₂ (Single-equiv (≡-trans (sym x₃) thd)))
     with unf
...     | ()
cf-pi-⇓ {n} {(Cast M .(Pi _ _) .(Pi _ _))} {.(Single _ _)} {A°} {B°} (CastA{A = Pi nA B}{B = Pi nA' B'}{A' = A'} j x x₁ x₂) (AUSingle unf) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi nA B}{B = Pi nA' B'} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym x₂) eq) λ ()
...  | inj₂ (fst , snd , thd) rewrite (proj₂ (Single-equiv (≡-trans (sym x₂) thd)))
     with unf
...     | AURefl-P = inj₂ (M , nA , (B , refl))

cf-pi-⇓ {n} {.(Cast _ _ Dyn)} {.(CaseT _ _)} {A} {B} (CastA{A = A₁}{B = Dyn}{A' = A'} j x₃ x₄ x₅) (AUCaseL x x₁ unf) (VCast v x₂)
  with (cast-result{A' = A'}{A = A₁}{B = Dyn} x₄)
...  | inj₁ eq = contradiction (≡-trans (sym x₅) eq) λ ()
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₅) λ ()

cf-pi-⇓ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(CaseT _ _)} {A°} {B°} (CastA{A = Pi nA B}{B = Pi nA' B'}{A' = A'} j x₂ x₃ x₄) (AUCaseL x x₁ unf) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi nA B}{B = Pi nA' B'} x₃)
...  | inj₁ eq = contradiction (≡-trans (sym x₄) eq) λ ()
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₄) λ () 

cf-pi-⇓ {n} {e} {.(CaseT (UVal VVar) _)} {_} {.(CaseT (UVal VVar) _)} j (AUCaseX-P {eq = eq} x x₁) v = contradiction eq env-empty-++
cf-pi-⇓ {n} {e} {.(CaseT (UCast VVar GLabel) _)} {_} {.(CaseT (UCast VVar GLabel) _)} j (AUCaseXDyn-P {eq = eq} x) v = contradiction eq env-empty-++

cf-sigma : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → [] ⊢ e ▷ (Sigma A B) → Val e → ∃[ e' ](∃[ V ](∃[ e'' ](e ≡ ProdV{e = e'} V e'')))
cf-sigma {n} {.(Var _)} {A} {B} (VarA x ()) VVar
cf-sigma {n} {.(ProdV v _)} {A} {B} j (VProd{e = e}{e' = e'} v v₁) = e , v , e' , refl
cf-sigma {n} {.(Cast _ _ Dyn)} {A} {B} (CastA{A = A'}{A' = A₁} j x₁ x₂ x₃) (VCast v x)
  with (cast-result{A' = A₁}{A = A'}{B = Dyn} x₂)
...  | inj₁ eq = contradiction (≡-trans (sym eq) x₃) (λ ())
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₃) (λ ())
cf-sigma {n} {.(Cast _ (Pi _ _) (Pi _ _))} {A} {B} (CastA{A = Pi nA' B'}{B = Pi nA'' B''}{A' = A'} j x x₁ x₂) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi nA' B'}{B = Pi nA'' B''} x₁)
...  | inj₁ eq = contradiction (≡-trans (sym eq) x₂) (λ ())
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₂) (λ ())

cf-sigma-⇓ : {n : ℕ} {e : Exp {n}} {D A B : Ty {n}} → [] ⊢ e ▷ D → [] ⊢ D ⇓ (Sigma A B) → Val e → ∃[ e' ](∃[ V ](∃[ e'' ](e ≡ ProdV{e = e'} V e'')))
cf-sigma-⇓ {n} {e} {.(Sigma A B)} {A} {B} j AURefl-S v = cf-sigma j v 

cf-sigma-⇓ {n} {.(Var _)} {.(Single _ _)} {A} {B} (VarA x ()) (AUSingle unf) VVar
cf-sigma-⇓ {n} {.(Var _)} {.(CaseT _ _)} {A} {B} (VarA y ()) (AUCaseL x x₁ unf) VVar

cf-sigma-⇓ {n} {.(LabI _)} {.(Single VLab (Label ⁅ _ ⁆))} {A} {B} (LabAI x) (AUSingle ()) VLab
cf-sigma-⇓ {n} {.(Cast _ _ Dyn)} {.(Single _ _)} {A} {B} (CastA{A = A₁}{B = Dyn}{A' = A'} j x₁ x₂ x₃) (AUSingle unf) (VCast v x)
  with (cast-result{A' = A'}{A = A₁}{B = Dyn} x₂)
...  | inj₁ x₄ = contradiction (≡-trans (sym x₄) x₃) (λ ())
...  | inj₂ (fst , snd , thd) rewrite (proj₂ (Single-equiv (≡-trans (sym x₃) thd)))
     with unf
...     | ()
cf-sigma-⇓ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(Single _ _)} {A} {B} (CastA{A = Pi A° B°}{B = Pi A°° B°°}{A' = A'} j x₁ x₂ x₃) (AUSingle unf) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi A° B°}{B = Pi A°° B°°} x₂)
...  | inj₁ eq = contradiction (≡-trans (sym eq) x₃) λ ()
...  | inj₂ (fst , snd , thd) rewrite (proj₂ (Single-equiv (≡-trans (sym x₃) thd)))
     with unf
...     | ()
cf-sigma-⇓ {n} {.(Cast _ _ Dyn)} {.(CaseT _ _)} {A} {B} (CastA{A = A₁}{B = Dyn}{A' = A'} j x₃ x₄ x₅) (AUCaseL x x₁ unf) (VCast v x₂)
  with (cast-result{A' = A'}{A = A₁}{B = Dyn} x₄)
...  | inj₁ eq = contradiction (≡-trans (sym x₅) eq) λ ()
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₅) λ ()
cf-sigma-⇓ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(CaseT _ _)} {A} {B} (CastA{A = Pi A° B°}{B = Pi A°° B°°}{A' = A'} j x₂ x₃ x₄) (AUCaseL x x₁ unf) (VCastFun v)
  with (cast-result{A' = A'}{A = Pi A° B°}{B = Pi A°° B°°} x₃)
...  | inj₁ eq = contradiction (≡-trans (sym x₄) eq) λ ()
...  | inj₂ (fst , snd , thd) = contradiction (≡-trans (sym thd) x₄) λ ()

cf-sigma-⇓ {n} {e} {.(CaseT (UVal VVar) _)} {_} {.(CaseT (UVal VVar) _)} j (AUCaseX-S {eq = eq} x x₁) v = contradiction eq env-empty-++
cf-sigma-⇓ {n} {e} {.(CaseT (UCast VVar GLabel) _)} {_} {.(CaseT (UCast VVar GLabel) _)} j (AUCaseXDyn-S {eq = eq} x) v = contradiction eq env-empty-++ 

------------------------------------------------------------------------
-- Progress

data Result {n : ℕ} : Exp {n} → Set where
  RValue : {e : Exp {n}} → Val {n} e → Result {n} e
  RBlame :  Result {n} Blame

data Progress-Type {n : ℕ} (A : Ty {n}) {j : [] ⊢ A} : Set where
  step : {A' : Ty {n}} → A ↠ A' → Progress-Type A
  result : TyNf A → Progress-Type A

data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ▷ T} : Set where
  step : {e' : Exp{n}} → e ⇨ e' → Progress e
  result : Result e → Progress e

progress-types : {n : ℕ} {A : Ty {n}} → (j : [] ⊢ A) → Progress-Type A {j}
progress : {n : ℕ} {e : Exp {n}} {T : Ty} → (j : [] ⊢ e ▷ T) → Progress e {T} {j}

progress-types {n} {.Dyn} (DynF x) = result (NfDyn)
progress-types {n} {.UnitT} (UnitF x) = result (NfUnit)
progress-types {n} {.Bot} (BotF x) = result NfBot
progress-types {n} {.(Label _)} (LabF x) = result (NfLabel)
progress-types {n} {.(Pi _ _)} (PiF j j₁)
  with progress-types {n} j
...  | step x = step (ξ-Pi x)
...  | result x = result ((NfPi{nfA = x}))
progress-types {n} {.(Sigma _ _)} (SigmaF j j₁)
  with progress-types {n} j
...  | step x = step (ξ-Sigma x)
...  | result x = result ((NfSigma{nfA = x})) 
progress-types {n} {.(Single _ _)} (SingleF x x₁ x₂) = step β-Single
progress-types {n} {(CaseT U f)} (CaseF (SubTypeA j leq))
  with progress j
...  | step r = step (ξ-Case{U' = valu-closed U r} r)
...  | result RBlame
     with U
...     | UBlame = step Case-Bot
progress-types {n} {(CaseT U f)} (CaseF (SubTypeA j leq)) | result (RValue v)
  with cf-label◁ (SubTypeA j leq) v
...  | fst , snd , thd
     rewrite snd
     with U
...     | UVal (VLab{x = fst}) = step (β-Case{ins = thd})

------------------------------------------------------------------------------------------------
------------------------------  Cases requiring canonical forms  -------------------------------
------------------------------------------------------------------------------------------------

progress {n} {CaseE (UVal x₁) f} {T} (LabAEl j x j₁)
  with cf-label◁ (SubTypeA j (ASubSingle (ASubLabel x) notsingle-label notcase-label)) x₁
... | (fst , fst₁ , snd) rewrite fst₁
    with x₁
...    | (VLab{x = l}) = step (β-LabE snd)
progress {n} {CaseE (UCast{e = e} x₁ x₂) f} {T} (LabAEl j x j₁)
  with castView e
progress {n} {CaseE (UCast{e = Cast e₁ G Dyn}{G = H} (VCast V g) x₂) f} {T} (LabAEl j x j₁) | cast-v
  with G ≡ᵀ? H
...  | yes eq rewrite eq = step (ξ-Case {U' = UVal V} (Cast-Collapse{v = V}{g = g}))
...  | no ¬eq = step (ξ-Case {U' = UBlame} (Cast-Collide{v = V}{g = g}{h = x₂} ¬eq))
progress {n} {CaseE (UCast {_} (VCastFun v) x₂) f} {T} (LabAEl (CastA{A = Dyn}{B = G}{A' = A'} (CastA{A = Pi nA B}{B = Pi nA' B'}{A' = A''} j x₅ x₆ x₇) x₁ x₃ x₄) x j₁) | cast-v
  with cast-result{A' = A''}{A = (Pi nA B)}{B = (Pi nA' B')} x₆
...  | inj₁ eq = contradiction x₃ (isnothing⇒¬isjust (cast-nothing{A = A'}{B = Dyn}{C = G} (notsingle λ e₁ B₁ W x₈ → contradiction (≡-trans (sym (≡-trans (sym x₇) eq)) x₈) (λ ()))
                                                                                                      λ x₈ → contradiction (≡-trans (sym (≡-trans (sym x₇) eq)) x₈) (λ ())))
...  | inj₂ (fst , snd , thd)
     with (sym (≡-trans (sym thd) x₇))
...     | eq' rewrite eq' = contradiction x₃ (isnothing⇒¬isjust (cast-nothing-single{A = Pi nA' B'}{B = Dyn}{C = G}{e = fst}{V = snd} (λ ()) (λ ())))
progress {n} {CaseE (UCast {e = e} x₁ x₂) f} {T} (LabAEl j x j₁) | (other-v{neq = neq}) = contradiction j (cast-lemma-1 neq x₁)

progress {n} {App N M} {.([ 0 ↦ M ]ᵀ _)} (PiAE j x (SubTypeA x₁ x₃) x₂)
  with progress {n} {N} j
...  | step r = step (ξ-App r)
...  | result RBlame = step App-Blame
...  | result (RValue v)
     with cf-pi-⇓ {n} {N} j x v
...     | inj₁ (fst , snd) rewrite snd = step (β-App M)
...     | inj₂ (fst , snd , thd , fth) rewrite fth
        with v
...        | (VCastFun v*) = step (Cast-Func{v = v*})
progress {n} {(LetP N M)} {T} (SigmaAE j x j₁ x₁)
  with progress {n} {N} j
...  | step r = step (ξ-LetP r)
...  | result RBlame = step LetP-Blame
...  | result (RValue v)
     with cf-sigma-⇓ {n} {N} j x v
...     | (fst , snd , thd , fth)
          rewrite fth
          with v
...          | VProd v* w = step (β-LetP snd w)

------------------------------------------------------------------------------------------------
-------------------------------------  Trivial cases  ------------------------------------------
------------------------------------------------------------------------------------------------

progress {n} {Blame} {T} (BlameA x) = result RBlame
progress {n} {(LetE M N)} {T} (LetA x j j₁)
  with progress {n} {M} j
...  | step r = step (ξ-LetE r)
...  | result RBlame = step (LetE-Blame)
...  | result (RValue V) = step (β-LetE V)
progress {n} {(ProdV V N)} {.(Sigma _ _)} (PairAI j j₁)
  with progress {n} {N} j₁
...  | step r = step (ξ-ProdV r)
...  | result RBlame = step ProdV-Blame
...  | result (RValue W) = result (RValue (VProd V W))
progress {n} {.(Abs _)} {.(Pi _ _)} (PiAI j) = result (RValue VFun)
progress {n} {.UnitE} {.UnitT} (UnitAI x) = result (RValue VUnit)
progress {n} {.(LabI _)} {.(Single VLab (Label ⁅ _ ⁆))} (LabAI x) = result (RValue VLab)
progress {n} {Prod N M} {.(Sigma _ _)} (SigmaAI (SubTypeA x x₁) j)
  with progress {n} {N} x
...  | step r = step (ξ-Prod r)
...  | result RBlame = step Prod-Blame
...  | result (RValue W) = step (β-Prod{v = W})

------------------------------------------------------------------------------------------------
------------------------------------  Impossible cases  ----------------------------------------
------------------------------------------------------------------------------------------------

progress {n} {.(CaseE (UVal VVar) _)} {.(CaseT (UVal VVar) _)} (LabAEx {eq = eq} x x₁) = contradiction eq env-empty-++
progress {n} {.(CaseE (UCast VVar GLabel) _)} {.(CaseT (UCast VVar GLabel) _)} (LabAExDyn {eq = eq} x) = contradiction eq env-empty-++

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
