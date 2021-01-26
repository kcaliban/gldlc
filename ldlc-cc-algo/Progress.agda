------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

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
-- Lemmas for cast case in progress

-- Type that is in normal form but not ground type
data nf-not-g {n : ℕ} : Ty {n} → Set where
  dyn : nf-not-g Dyn
  bot : nf-not-g Bot
  pi : {A B : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) ⊎ ¬ (B ≡ Dyn) → nf-not-g (Pi A B)
  sigma : {A B : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) ⊎ ¬ (B ≡ Dyn) → nf-not-g (Sigma A B)

-- types that are nf but not ground
cast-lemma-1 : {n : ℕ} {T : Ty {n}} → TyNf T → ¬ (TyG T) → nf-not-g T
cast-lemma-1 {n} {.Bot} NfBot ntyg = bot
cast-lemma-1 {n} {.UnitT} NfUnit ntyg = contradiction GUnit ntyg
cast-lemma-1 {n} {.(Label _)} NfLabel ntyg = contradiction GLabel ntyg
cast-lemma-1 {n} {.Dyn} NfDyn ntyg = dyn  
cast-lemma-1 {n} {.(Pi _ _)} (NfPi{A = A}{B}{nfA = nfA}) ntyg
  with A ≡ᵀ? Dyn
...  | no ¬p = pi nfA (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬p' = pi nfA (inj₂ ¬p')
...     | yes p' rewrite p | p' = contradiction GPi ntyg
cast-lemma-1 {n} {.(Sigma _ _)} (NfSigma{A = A}{B}{nfA = nfA}) ntyg
  with A ≡ᵀ? Dyn
...  | no ¬p = sigma nfA (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬p' = sigma nfA (inj₂ ¬p')
...     | yes p' rewrite p | p' = contradiction GSigma ntyg  

-- (V : * => G), V ≠ Cast, untypable in empty env.
cast-lemma-3 : {n : ℕ} {e : Exp {n}} {A G : Ty {n}} → (∀ e' A B → ¬ (e ≡ Cast e' A B)) → Val e → TyG G → ¬ ([] ⊢ Cast e Dyn G ▷ A)
cast-lemma-3 {n} {(LabI l)} {G} ncast W tyg (CastA (LabAI x₃) x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing-single{A = Label ⁅ l ⁆}{B = Dyn}{C = G}{e = LabI l}{V = VLab{x = l}} (λ ()) λ ())) 
cast-lemma-3 {n} {(Cast e y z)} {G} ncast W tyg (CastA (CastA j x₃ x₄ x₅) x x₁ x₂) = contradiction refl (ncast e y z)
cast-lemma-3 {n} {.UnitE} {G} ncast W tyg (CastA (UnitAI x₃) x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = UnitT} {Dyn} {C = G} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-3 {n} {.(Abs _)} {G} ncast W tyg (CastA (PiAI{A = A}{B = B} j) x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Pi A B} {Dyn} {C = G} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-3 {n} {.(ProdV _ _)} {G} ncast W tyg (CastA (PairAI{A = A}{B = B} j j₁) x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Sigma A B} {Dyn} {C = G} (notsingle (λ e B W → λ ())) (λ ())))

-- V : Σ => Σ well-typed in empty env. means V is a product
cast-lemma-4 : {n : ℕ} {e : Exp {n}} {A nA nA' B B' : Ty {n}} {nfA : TyNf nA} {nfA' : TyNf nA'} → (∀ e' A B → ¬ (e ≡ Cast e' A B))
                                                                                                 → Val e → [] ⊢ Cast e (Sigma nA B) (Sigma nA' B') ▷ A
                                                                                                 → (∃[ e' ](∃[ V ](∃[ e'' ](e ≡ ProdV{e = e'} V e''))))
cast-lemma-4 {n} {ProdV{e = e} x₃ e'} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Sigma A' A''} j x x₁ x₂) = (e , x₃ , (e' , refl))

cast-lemma-4 {n} {Var x₄} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Single x₃ A'} (VarA x₅ ()) x x₁ x₂)

cast-lemma-4 {n} {LabI x₄} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Single .VLab .(Label ⁅ x₄ ⁆)} (LabAI x₃) x x₁ x₂)
  = contradiction x₁ (isnothing⇒¬isjust (cast-nothing-single{A = Label ⁅ x₄ ⁆}{B = Sigma nA B}{C = Sigma nA' B'}{V = VLab{x = x₄}}  (λ ()) λ ()))
cast-lemma-4 {n} {Cast e x₄ x₅} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Single x₃ A'} j x x₁ x₂) = contradiction refl (ncast e x₄ x₅)

cast-lemma-4 {n} {Var x₃} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Sigma A' A''} (VarA x₄ ()) x x₁ x₂)
cast-lemma-4 {n} {Cast e x₃ x₄} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Sigma A' A''} j x x₁ x₂) = contradiction refl (ncast e x₃ x₄)
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Bot} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Bot} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = UnitT} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = UnitT} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Dyn} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Dyn} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Label x₃} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Label x₃} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = Pi A' A''} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = Pi A' A''} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))
cast-lemma-4 {n} {e} {A} {nA} {nA'} {B} {B'} {nfA} {nfA'} ncast V (CastA {A' = CaseT x₃ f} j x x₁ x₂) = contradiction x₁ (isnothing⇒¬isjust (cast-nothing {A = CaseT x₃ f} {Sigma nA B} {Sigma nA' B'} (notsingle (λ e B W → λ ())) (λ ())))

-- Produce ground type for normal form
cast-lemma-5 : {n : ℕ} {A : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) → ¬ (A ≡ Bot) → [] ⊢ A → ∃[ G ](TyG G × ([] ∣ [] ⊢ G ~ A))
cast-lemma-5 {n} {.Bot} NfBot neq neq' j = contradiction refl neq'
cast-lemma-5 {n} {.Dyn} NfDyn neq neq' j = contradiction refl neq
cast-lemma-5 {n} {.UnitT} NfUnit neq neq' j = UnitT , (GUnit , (AConsRefl empty))
cast-lemma-5 {n} {(Label s)} NfLabel neq neq' j = Label s , GLabel , (AConsRefl empty)
cast-lemma-5 {n} {Pi A B} (NfPi {nfA = nfA}) neq neq' (PiF j j₁) = (Pi Dyn Dyn) , (GPi , (AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))))
cast-lemma-5 {n} {(Sigma A B)} (NfSigma{nfA = nfA}) neq neq' (SigmaF j j₁) = (Sigma Dyn Dyn) , (GSigma , (AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))))

-- Produce ground type for normal form but non-ground type
cast-lemma-5-1 : {n : ℕ} {A : Ty {n}} → nf-not-g A → ¬ (A ≡ Dyn) → ¬ (A ≡ Bot) → [] ⊢ A → ∃[ G ](TyG G × ([] ∣ [] ⊢ G ~ A) × ¬ (G ≡ A))
cast-lemma-5-1 {n} {.Bot} bot neq neq' j = contradiction refl neq'
cast-lemma-5-1 {n} {.Dyn} dyn neq neq' j = contradiction refl neq
cast-lemma-5-1 {n} {.(Pi _ _)} (pi x (inj₁ y)) neq neq' (PiF j j₁) = (Pi Dyn Dyn) , (GPi , ((AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₁ (Pi-equiv (sym x₁))) y))
cast-lemma-5-1 {n} {.(Pi _ _)} (pi x (inj₂ y)) neq neq' (PiF j j₁) = (Pi Dyn Dyn) , (GPi , ((AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₂ (Pi-equiv (sym x₁))) y)) 
cast-lemma-5-1 {n} {.(Sigma _ _)} (sigma x (inj₁ y)) neq neq' (SigmaF j j₁)
  = (Sigma Dyn Dyn) , (GSigma , ((AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₁ (Sigma-equiv (sym x₁))) y))
cast-lemma-5-1 {n} {.(Sigma _ _)} (sigma x (inj₂ y)) neq neq' (SigmaF j j₁)
  = (Sigma Dyn Dyn) , (GSigma , ((AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₂ (Sigma-equiv (sym x₁))) y))

-- (V : G => *) ▷ A means A either Dyn or Single _ Dyn
-- cast-result : {n : ℕ} {A' A B : Ty {n}} → Is-just (cast A' A B)
cast-lemma-6 : {n : ℕ} {e : Exp {n}} {A B C : Ty {n}} → Val e → [] ⊢ Cast e B C ▷ A → (A ≡ C) ⊎ (∃[ e ](∃[ W ](A ≡ Single{e = e} W C)))
cast-lemma-6 {n} {e} {A} {B} {C} V (CastA{A' = A'} j x x₁ x₂)
  with cast-result{n}{A'}{B}{C} x₁
... | inj₁ x₃ = inj₁ (≡-trans (sym x₂) x₃)
... | inj₂ (fst , fst₁ , snd) = inj₂ (fst , (fst₁ , (≡-trans (sym x₂) snd)))

------------------------------------------------------------------------
-- Canonical forms

cf-label◁ : {n : ℕ} {s : Subset n} {e : Exp {n}} → [] ⊢ e ◁ Label s → Val e → ∃[ l ]((e ≡ LabI l) × l ∈ s)
cf-label◁ {n} {s} {.(LabI l)} (SubTypeA (LabAI {l = l} x) (ASubSingle (ASubLabel x₃) x₁ x₂)) VLab = (l , (refl , ([l]⊆L⇒l∈L x₃)))

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
cf-label◁ {n} {s} {.(Cast _ _ Dyn)} (SubTypeA (CastA j x x₁ y) (ASubCaseXLDyn{eq = eq} x₃)) (VCast v x₂) = contradiction eq env-empty-++
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
progress {n} {CaseE (UCast {e = e} x₁ x₂) f} {T} (LabAEl j x j₁) | (other-v{neq = neq}) = contradiction j (cast-lemma-3 neq x₁ x₂)

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
progress {n} {(LetE M N)} {T} (Let x j j₁)
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
...  | result (RValue W) | result (NfBot) | _ = step Cast-Bot-L
...  | result (RValue W) | result (nf) | step r = step (Cast-Reduce-R{v = W} nf r)
...  | result (RValue W) | result (nf) | result (NfBot) = step (Cast-Bot-R nf)
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
  with cast-lemma-1 {n} {B} nfB ¬tyg
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
  with cast-lemma-5-1 {n} {B} (pi z z') (λ ()) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
-------- B = Sigma A B
---------- (V : G => *) : * => Sigma A B --> ((V : G => *) : * => G') : G' => Sigma A B
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | sigma z z'
  with cast-lemma-5-1 {n} {B} (sigma z z') (λ ()) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
-------- B = Bot
---------- (V : G => *) : * => Bot --> Bot
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | bot = step (Cast-Bot-R nfA)

------------------------------------------------------------------------------------------------
-- (V : G => *) : A => B
---- A ≠ Dyn
------ (V : G => *) ▷ A'
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq
  with cast-lemma-6 {n} {e₁} {A'} {G₁} W j
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
  with cast-lemma-6 {n} {e₁} {A'} {Pi A° B°} {Pi A°° B°°} W j
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
     with cast-lemma-1 {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with cast-lemma-5-1 {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ((λ ())) ok
-------------- (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => * --> ((V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => G) : G => *
...        | fst , snd , thd , fth = step (Cast-Factor-L{v = VCastFun{nfA = nfA°}{nfA' = nfA°°} W}{g = snd}{nfA = NfPi{nfA = nfA°°}} thd ok fth (λ ()))
-- (V : Pi A° B° => Pi A°° B°°) : A => B
---- (V : Pi A° B° => Pi A°° B°°) ▷ A'
------ Pi A°° B°° = A'
-------- Pi A°° B°° = A' = A
---------- B ≠ Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq
  with TyG? (Pi A°° B°°)  
------------ TyG (Pi A°° B°°)  
...  | yes tyg
     with TyG? B
-------------- TyG B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | yes tyg | yes tyg'
---------------- Pi A°° B°° ~ B
  with x
------------------ B = Pi A°° B°°
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A°° B°°
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
------------------ B = Pi A* B*
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A* B*
...  | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
-------------- ¬ TyG B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | yes tyg | no ¬tyg'
---------------- Pi A°° B°° ~ B
  with x
------------------ B = *
-------------------- contradiction B ≠ *
...  | AConsDynR x₄ = contradiction refl ¬eq
------------------ B = Pi A°° B°°
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A°° B°°
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
------------------ B = Pi A* B*
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A* B*
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | yes tyg | no ¬tyg' | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
-- (V : Pi A° B° => Pi A°° B°°) : A => B
---- (V : Pi A° B° => Pi A°° B°°) ▷ A'
------ Pi A°° B°° = A'
-------- Pi A°° B°° = A' = A
---------- B ≠ Dyn
------------ ¬ TyG (Pi A°° B°°) 
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg
  with TyG? B
-------------- TyG B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg | yes tyg'
---------------- Pi A°° B°° ~ B
  with x
------------------ B = Pi A°° B°°
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A°° B°°
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
------------------ B = Pi A* B*
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A* B*
...  | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
-------------- ¬ TyG B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result nfB | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg | no ¬tyg'
---------------- Pi A°° B°° ~ B
  with x
------------------ B = *
-------------------- contradiction B ≠ *
... | AConsDynR x₄ = contradiction refl ¬eq
------------------ B = Pi A°° B°°
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A°° B°°
... | AConsRefl x₄ = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
------------------ B = Pi A* B*
-------------------- Value: (V : Pi A° B° => Pi A°° B°°) : Pi A°° B°° => Pi A* B*
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg | no ¬tyg' | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
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
     with cast-lemma-1 {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with cast-lemma-5-1 {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ((λ ())) ok
...        | fst° , snd° , thd° , fth° = step (Cast-Factor-L{v = VCastFun{nfA = nfA°}{nfA' = nfA°°} W}{g = snd°}{nfA = NfPi{nfA = nfA°°}} thd° ok fth° (λ ()))
-- analogous to  Pi A°° B°°} = A'
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq
  with TyG? (Pi A°° B°°)
...  | yes tyg
     with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | yes tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
...  | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result nfB | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | yes tyg | no ¬tyg'
  with x
...  | AConsDynR x₄ = contradiction refl ¬eq
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | yes tyg | no ¬tyg' | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg
  with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
...  | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result nfB | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg | no ¬tyg'
  with x
... | AConsDynR x₄ = contradiction refl ¬eq
... | AConsRefl x₄ = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA°°} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)) | result (nfA) | result (NfPi{nfA = nfA''}) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg | no ¬tyg' | AConsPi cons cons' = result (RValue (VCastFun{nfA = nfA°°}{nfA' = nfA''} (VCastFun{nfA = nfA°}{nfA' = nfA°°} W)))                                                                                                          
------------------------------------------------------------------------------------------------
-- V : A => B, V ≠ W : C => D
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq}
  with nB ≡ᵀ? Dyn
---- B = Dyn  
...  | yes eq rewrite eq
------ TyG A
     with TyG? nA
-------- Value: V : G => *     
...     | yes tyg = result (RValue (VCast W tyg))
------ ¬ TyG A (and in nf)
...     | no ¬tyg
        with cast-lemma-1 {n} {nA} nfA ¬tyg
---------- A = Dyn
------------ V : * => * --> *
...        | dyn = step (Cast-Dyn{v = W})
---------- A = Pi A B
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | yes eq | no ¬tyg | pi x₂ x₃
  with cast-lemma-5-1 {n} {nA} (pi x₂ x₃) (λ ()) (λ ()) ok
------------ V : Pi A B => * --> (V : Pi A B => G) : G => *
...  | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))
---------- A = Sigma A B
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | yes eq | no ¬tyg | sigma x₂ x₃
  with cast-lemma-5-1 {n} {nA} (sigma x₂ x₃) (λ ()) (λ ()) ok
------------ V : Sigma A B => * --> (V : Sigma A B => G) : G => *  
...  | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))
---------- A = Bot
------------ V : Bot => * --> Blame
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | yes eq | no ¬tyg | bot = step (Cast-Bot-L)
-- V : A => B, V ≠ W : C => D
---- B ≠ Dyn  
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq
------ A = Dyn
  with nA ≡ᵀ? Dyn
...  | yes eq' rewrite eq'
     with TyG? nB
-------- TyG B
---------- contradiction, (V : * => G), V ≠ Cast untypable in empty env.
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | yes tyg
  = contradiction (CastA{ok = ok}{ok' = ok'} j x x₁ y) (cast-lemma-3 {n} {e} {T} {nB} neq W tyg)
-------- ¬ TyG B (and in nf)
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg
  with cast-lemma-1 {n} {nB} nfB ¬tyg
---------- B = Dyn
------------ contradiction, B ≠ Dyn
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | dyn = contradiction refl ¬eq
---------- B = Pi A* B*
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | pi x₂ x₃
  with cast-lemma-5-1 {n} {nB} (pi x₂ x₃) (λ ()) (λ ()) ok'
------------ (V : * => Pi A* B*) --> (V : * => G) : G => Pi A* B*  
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = W}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
---------- B = Sigma A* B*
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | sigma x₂ x₃
  with cast-lemma-5-1 {n} {nB} (sigma x₂ x₃) (λ ()) (λ ()) ok'
------------ (V : * => Sigma A* B*) --> (V : * => G) : G => Sigma A* B*    
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = W}{g = snd}{nfB = nfB} thd ok' fth (λ ()))
---------- B = Bot
------------ (V : * => Bot) --> Blame
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | bot = step (Cast-Bot-R nfA)
-- V : A => B, V ≠ W : C => D, A ≠ *, B ≠ *
---- (V : Bot => Bot) --> Blame
progress {n} {Cast e Bot .Bot} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Bot-R nfA)
---- Contradictions to A ≠ * and B ≠ *
progress {n} {Cast e .Dyn nB} {T} (CastA {ok = ok} {ok'} j (AConsDynL x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq'
progress {n} {Cast e nA .Dyn} {T} (CastA {ok = ok} {ok'} j (AConsDynR x) x₁ y) | result (RValue W) | result (nfA) | result (nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq
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
  with cast-lemma-4 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y)
progress {n} {Cast e (Sigma nA nA₁) .(Sigma nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue (VProd V W)) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' | (fst , snd , thd , fth)
-------- ⟨⟨ V' , W' ⟩⟩ : Sigma A B => Sigma A B --> let x = (V' : A => A) in ⟨⟨ x , W' : (B[V'/x] => B) ⟩⟩
  = step (Cast-Pair{w = W})
---- (V : Sigma A B => Sigma A' B')
------ V = ⟨⟨ V' , W' ⟩⟩
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue W) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq'
  with cast-lemma-4 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y)
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue (VProd V W)) | result (NfSigma{nfA = nfA}) | result (NfSigma{nfA = nfA'}) | other-v{e = e}{neq} | no ¬eq | no ¬eq' |  (fst , snd , thd , fth)
-------- ⟨⟨ V' , W' ⟩⟩ : Sigma A B => Sigma A B --> let x = (V' : A => A') in ⟨⟨ x , W' : (B[V'/x] => B') ⟩⟩  
  = step (Cast-Pair{w = W})

