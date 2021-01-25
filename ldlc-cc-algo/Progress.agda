------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

module Progress where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.Fin hiding (cast)
open import Data.Fin.Properties
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
-- Lemmas

---- Required since the function definition skips a lot of cases and Agda can't figure out what's going on
cast-result : {n : ℕ} {A' A B : Ty {n}} → Is-just (cast A' A B) → (Data.Maybe.fromMaybe UnitT (cast A' A B) ≡ B) ⊎ (∃[ e ](∃[ V ](Data.Maybe.fromMaybe UnitT (cast A' A B) ≡ Single{e = e} V B)))

cast-result {n} {Single{e = e} x A'} {Single{e = e'} x₁ A} {B} ju
  with A' ≡ᵀ? A | e ≡ᵉ? e'
...  | yes eq | yes eq' = inj₁ refl
cast-result {n} {Single{e = e} x A'} {Bot} {B} ju
  with A' ≡ᵀ? Bot | [] ∶ Cast e Bot B ⇓
...  | yes eq | fst , RValue x₁ = inj₂ (fst , ((val*⇒val x₁) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {UnitT} {B} ju
  with A' ≡ᵀ? UnitT | [] ∶ Cast e UnitT B ⇓
...  | yes eq | fst , RValue x₁ = inj₂ (fst , ((val*⇒val x₁) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {Dyn} {B} ju
  with A' ≡ᵀ? Dyn | [] ∶ Cast e Dyn B ⇓
...  | yes eq | fst , RValue x₁ = inj₂ (fst , ((val*⇒val x₁) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {Label x₁} {B} ju
  with A' ≡ᵀ? (Label x₁) | [] ∶ Cast e (Label x₁) B ⇓
...  | yes eq | fst , RValue v = inj₂ (fst , ((val*⇒val v) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {Pi A A₁} {B} ju
  with A' ≡ᵀ? (Pi A A₁) | [] ∶ Cast e (Pi A A₁) B ⇓
...  | yes eq | fst , RValue x₁ = inj₂ (fst , ((val*⇒val x₁) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {Sigma A A₁} {B} ju
  with A' ≡ᵀ? (Sigma A A₁) | [] ∶ Cast e (Sigma A A₁) B ⇓
...  | yes eq | fst , RValue x₁ = inj₂ (fst , ((val*⇒val x₁) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Single{e = e} x A'} {CaseT x₁ f} {B} ju
  with A' ≡ᵀ? (CaseT x₁ f) | [] ∶ Cast e (CaseT x₁ f) B ⇓
...  | yes eq | fst , RValue v = inj₂ (fst , ((val*⇒val v) , refl))
...  | yes eq | .Blame , RBlame = inj₁ refl
cast-result {n} {Bot} {A} {B} ju
  with A ≡ᵀ? Bot
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {UnitT} {A} {B} ju
  with A ≡ᵀ? UnitT
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {Dyn} {A} {B} ju
  with A ≡ᵀ? Dyn
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {Label x} {A} {B} ju
  with A ≡ᵀ? (Label x)
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {Pi A' A''} {A} {B} ju
  with A ≡ᵀ? (Pi A' A'')
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {Sigma A' A''} {A} {B} ju
  with A ≡ᵀ? (Sigma A' A'')
...  | yes eq rewrite eq = inj₁ refl
cast-result {n} {CaseT x f} {A} {B} ju
  with A ≡ᵀ? (CaseT x f)
...  | yes eq rewrite eq = inj₁ refl

Pi-equiv : {n : ℕ} {A A' B B' : Ty {n}} → Pi A B ≡ Pi A' B' → A ≡ A' × B ≡ B'
Pi-equiv {n} {A} {.A} {B} {.B} refl = refl , refl

Sigma-equiv : {n : ℕ} {A A' B B' : Ty {n}} → Sigma A B ≡ Sigma A' B' → A ≡ A' × B ≡ B'
Sigma-equiv {n} {A} {.A} {B} {.B} refl = refl , refl

Single-equiv : {n : ℕ} {e e' : Exp {n}} {V : Val e} {V' : Val e'} {A A' : Ty {n}} → Single V A ≡ Single V' A' → e ≡ e' × A ≡ A'
Single-equiv {n} {e} {.e} {V} {.V} {A} {.A} refl = refl , refl

cast-dyn-s : {n : ℕ} {A' A : Ty {n}} {s : Subset n} → Is-just (cast A' A Dyn) → ¬(Data.Maybe.fromMaybe UnitT (cast A' A Dyn) ≡ Label s)
cast-dyn-s {n} {A'} {A} {s} isj
  with cast-result {n} {A'} {A} {Dyn} isj
...  | inj₁ x = λ y → contradiction (≡-trans (sym x) y) λ () 
...  | inj₂ (fst , snd , thd) = λ y → contradiction (≡-trans (sym thd) y) λ ()

isnothing⇒¬isjust : {A : Set} {a : Maybe A} → Is-nothing a → ¬ (Is-just a)
isnothing⇒¬isjust {A} {.nothing} nothing = λ ()

¬isjust⇒isnothing : {A : Set} {a : Maybe A} → ¬ (Is-just a) → Is-nothing a
¬isjust⇒isnothing {A} {nothing} ju = nothing
¬isjust⇒isnothing {A} {just x} ju = contradiction (just Data.Unit.tt) ju

cast-nothing : {n : ℕ} {A B C : Ty {n}} → notSingle A → A ≢ B → Is-nothing (cast A B C)
cast-nothing {n} {A} {B} {C} (notsingle nope) neq = ¬isjust⇒isnothing ϱ
  where ϱ : ¬ (Is-just (cast A B C))
        ϱ x
          with cast-trivial-just-inv x
        ...  | inj₁ eq = contradiction eq neq
        ...  | inj₂ (fst , snd , thd) = contradiction thd (nope fst B snd)

cast-nothing-single : {n : ℕ} {A B C : Ty {n}} {e : Exp {n}} {V : Val e} → A ≢ B → (Single V A) ≢ B → Is-nothing (cast (Single V A) B C)
cast-nothing-single {n} {A} {B} {C} {e} {V} neq neq' =  ¬isjust⇒isnothing ϱ
  where ϱ : ¬ Is-just (cast (Single V A) B C)
        ϱ x
          with cast-trivial-just-inv{A = Single V A}{B = B}{C = C} x
        ...  | inj₁ eq = contradiction eq neq'
        ...  | inj₂ (fst , snd , thd) = contradiction (proj₂ (Single-equiv thd)) neq


-- If two types are in ground form and consistent, then they are equal
tyg-equal : {n : ℕ} {T T' : Ty {n}} → TyG T → TyG T' → [] ∣ [] ⊢ T ~ T' → T ≡ T'
tyg-equal {n} {.UnitT} {.UnitT} GUnit GUnit cons = refl
tyg-equal {n} {.(Label _)} {.(Label _)} GLabel GLabel (AConsRefl x) = refl
-- if S{l : L} is ground type, then L ~ S{l : L} and this and consequently val-noreduce don't hold
-- tyg-equal {n} {.(Label _)} {.(Single VLab (Label _))} GLabel GSingle cons = {!!}
tyg-equal {n} {.(Pi Dyn Dyn)} {.(Pi Dyn Dyn)} GPi GPi cons = refl
tyg-equal {n} {.(Sigma Dyn Dyn)} {.(Sigma Dyn Dyn)} GSigma GSigma cons = refl

-- Ground types don't reduce
tyg-noreduce : {n : ℕ} {T : Ty {n}} → TyG T → (∀ T' → ¬ (T ↠ T'))
tyg-noreduce {n} {.(Pi Dyn Dyn)} GPi .(Pi _ Dyn) (ξ-Pi ())
tyg-noreduce {n} {.(Sigma Dyn Dyn)} GSigma .(Sigma _ Dyn) (ξ-Sigma ())

-- Types in normal form don't reduce
tynf-noreduce : {n : ℕ} {T : Ty {n}} → TyNf T → (∀ T' → ¬ (T ↠ T'))
tynf-noreduce {n} {.(Pi _ _)} (NfPi{nfA = nfA}) .(Pi _ _) (ξ-Pi{A' = A'} r) = contradiction r (tynf-noreduce nfA A')
tynf-noreduce {n} {.(Sigma _ _)} (NfSigma {nfA = nfA}) .(Sigma _ _) (ξ-Sigma{A' = A'} r) = contradiction r (tynf-noreduce nfA A')

-- Values don't reduce
val-noreduce : {n : ℕ} {e : Exp {n}} → Val e → (∀ e' → ¬ (e ⇨ e'))
val-noreduce {n} {.UnitE} VUnit e' = λ ()
val-noreduce {n} {.(Var _)} VVar e' = λ ()
val-noreduce {n} {.(LabI _)} VLab e' = λ ()
val-noreduce {n} {.(Abs _)} VFun e' = λ ()
val-noreduce {n} {.(ProdV W _)} (VProd W W₁) .(ProdV W _) (ξ-ProdV{e₂' = e₂'} r) = contradiction r (val-noreduce W₁ e₂')
val-noreduce {n} {.(Cast _ _ Dyn)} (VCast W x) .(Cast _ _ Dyn) (ξ-Cast{e₂ = e₂} r) = contradiction r (val-noreduce W e₂)
val-noreduce {n} {.(Cast _ _ Dyn)} (VCast W x) .(Cast _ _ Dyn) (Cast-Reduce-L{A' = A'} x₁) = contradiction x₁ (tyg-noreduce x A')
val-noreduce {n} {.(Cast _ _ Dyn)} (VCast W x) .(Cast (Cast _ _ _) _ Dyn) (Cast-Factor-L{g = g} x₁ x₂ x₃ x₄) = contradiction (tyg-equal g x x₁) x₃
val-noreduce {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun v) .(Cast _ (Pi _ _) (Pi _ _)) (ξ-Cast{e₂ = e₂} r) = contradiction r (val-noreduce v e₂)
val-noreduce {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun{nfA = nfA} v) .(Cast _ _ (Pi _ _)) (Cast-Reduce-L{A' = A'} x) = contradiction x (tynf-noreduce (NfPi{nfA = nfA}) A')
val-noreduce {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun{nfA' = nfA'} v) .(Cast _ (Pi _ _) _) (Cast-Reduce-R{B' = B'} y x) = contradiction x (tynf-noreduce (NfPi{nfA = nfA'}) B')

-- ValU closed under reduction
valu-closed : {n : ℕ} {e e' : Exp {n}} → ValU e → e ⇨ e' → ValU e'
valu-closed {n} {e} {e'} (UVal v) r = contradiction r (val-noreduce v e')  
valu-closed {n} {.(Cast (Cast e' (Label _) Dyn) Dyn (Label _))} {e'} (UCast (VCast x x₂) x₁) (Cast-Collapse-Label-Label{v = v} x₃) = UVal v
valu-closed {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} (UCast (VCast x x₂) x₁) (Cast-Collapse {v = v}) = UVal v
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} (UCast x x₁) (Cast-Collide x₂) = UBlame
valu-closed {n} {.(Cast UnitE Dyn _)} {.(Cast UnitE Dyn _)} (UCast VUnit x₁) (Cast-Reduce-R{B' = B'} y x) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast UnitE Dyn _)} {.(Cast (Cast UnitE Dyn _) _ _)} (UCast VUnit x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) = contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Var _) Dyn _)} (UCast VVar x₁) (Cast-Reduce-R{B' = B'} y x) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Cast (Var _) Dyn _) _ _)} (UCast VVar x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (LabI _) Dyn _)} {.(Cast (LabI _) Dyn _)} (UCast VLab x₁) (Cast-Reduce-R{B' = B'} y x) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (LabI _) Dyn _)} {.(Cast (Cast (LabI _) Dyn _) _ _)} (UCast VLab x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (Abs _) Dyn _)} {.(Cast (Abs _) Dyn _)} (UCast VFun x₁) (Cast-Reduce-R{B' = B'} y x) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Abs _) Dyn _)} {.(Cast (Cast (Abs _) Dyn _) _ _)} (UCast VFun x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (ProdV x _) Dyn _)} (UCast (VProd x x₂) x₁) (Cast-Reduce-R{B' = B'} y x') = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (Cast (ProdV x _) Dyn _) _ _)} (UCast (VProd x x₂) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (Cast-Reduce-R{B' = B'} y x') = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast (Cast _ _ Dyn) Dyn _) _ _)} (UCast (VCast x x₂) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun x) x₁) (Cast-Reduce-R{B' = B'} y x') = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _) _ _)} (UCast (VCastFun x) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃ 
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (Cast-Reduce-L{A' = A'} x₃)) = contradiction x₃ (tyg-noreduce x₂ A')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast (Cast _ _ _) _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (Cast-Factor-L{g = g} x₃ x₄ x₅ x₆)) = contradiction (tyg-equal g x₂ x₃) x₅
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (ProdV x _) Dyn _)} (UCast (VProd x x₂) x₁) (ξ-Cast (ξ-ProdV{e₂' = e₂'} r)) = contradiction r (val-noreduce x₂ e₂')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (ξ-Cast{e₂ = e₂} r)) = contradiction r (val-noreduce x e₂)
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun x) x₁) (ξ-Cast (ξ-Cast{e₂ = e₂} r)) = contradiction r (val-noreduce x e₂)
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun{nfA = nfA} x) x₁) (ξ-Cast (Cast-Reduce-L (ξ-Pi{A' = A'} x₂))) = contradiction x₂ (tynf-noreduce nfA A')
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun{nfA' = nfA'} x) x₁) (ξ-Cast (Cast-Reduce-R y (ξ-Pi{A' = A'} x₂))) = contradiction x₂ (tynf-noreduce nfA' A')  

¬Single-nf : {n : ℕ} {A : Ty {n}} → TyNf A → (∀ e V B → A ≢ Single{n = n}{e = e} V B)
¬Single-nf {n} {.Dyn} NfDyn = λ e V B → λ ()
¬Single-nf {n} {.UnitT} NfUnit = λ e V B → λ ()
¬Single-nf {n} {.(Label _)} NfLabel = λ e V B → λ ()
¬Single-nf {n} {.(Pi _ _)} NfPi = λ e V B → λ ()
¬Single-nf {n} {.(Sigma _ _)} NfSigma = λ e V B → λ ()

¬dyn-label-sub : {n : ℕ} {s : Subset n} {A : Ty {n}} → [] ⊢ A ≤ᵀ Label s → A ≢ Dyn
¬dyn-label-sub {n} {s} {.(Label _)} (ASubLabel x) = λ ()
¬dyn-label-sub {n} {s} {.(Single _ _)} (ASubSingle leq x x₁) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT _ _)} (ASubCaseLL x x₁ leq) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT (UVal VVar) _)} (ASubCaseXL leq x) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT (UCast VVar GLabel) _)} (ASubCaseXLDyn x) = λ ()

-- Lemmas required for Cast case
-- Type that is in normal form but not ground type
data nf-not-g {n : ℕ} : Ty {n} → Set where
  dyn : nf-not-g Dyn
  pi : {A B : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) ⊎ ¬ (B ≡ Dyn) → nf-not-g (Pi A B)
  sigma : {A B : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) ⊎ ¬ (B ≡ Dyn) → nf-not-g (Sigma A B)

-- types that are nf but not ground
cast-lemma-1 : {n : ℕ} {T : Ty {n}} → TyNf T → ¬ (TyG T) → nf-not-g T
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
cast-lemma-5 : {n : ℕ} {A : Ty {n}} → TyNf A → ¬ (A ≡ Dyn) → [] ⊢ A → ∃[ G ](TyG G × ([] ∣ [] ⊢ G ~ A))
cast-lemma-5 {n} {.Dyn} NfDyn neq j = contradiction refl neq
cast-lemma-5 {n} {.UnitT} NfUnit neq j = UnitT , (GUnit , (AConsRefl empty))
cast-lemma-5 {n} {(Label s)} NfLabel neq j = Label s , GLabel , (AConsRefl empty)
cast-lemma-5 {n} {Pi A B} (NfPi {nfA = nfA}) neq (PiF j j₁) = (Pi Dyn Dyn) , (GPi , (AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))))
cast-lemma-5 {n} {(Sigma A B)} (NfSigma{nfA = nfA}) neq (SigmaF j j₁) = (Sigma Dyn Dyn) , (GSigma , (AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))))

-- Produce ground type for normal form but non-ground type
cast-lemma-5-1 : {n : ℕ} {A : Ty {n}} → nf-not-g A → ¬ (A ≡ Dyn) → [] ⊢ A → ∃[ G ](TyG G × ([] ∣ [] ⊢ G ~ A) × ¬ (G ≡ A))
cast-lemma-5-1 {n} {.Dyn} dyn neq j = contradiction refl neq
cast-lemma-5-1 {n} {.(Pi _ _)} (pi x (inj₁ y)) neq (PiF j j₁) = (Pi Dyn Dyn) , (GPi , ((AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₁ (Pi-equiv (sym x₁))) y))
cast-lemma-5-1 {n} {.(Pi _ _)} (pi x (inj₂ y)) neq (PiF j j₁) = (Pi Dyn Dyn) , (GPi , ((AConsPi (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₂ (Pi-equiv (sym x₁))) y)) 
cast-lemma-5-1 {n} {.(Sigma _ _)} (sigma x (inj₁ y)) neq (SigmaF j j₁)
  = (Sigma Dyn Dyn) , (GSigma , ((AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₁ (Sigma-equiv (sym x₁))) y))
cast-lemma-5-1 {n} {.(Sigma _ _)} (sigma x (inj₂ y)) neq (SigmaF j j₁)
  = (Sigma Dyn Dyn) , (GSigma , ((AConsSigma (AConsDynL empty) (AConsDynL (entry empty (AConsDynL empty) (DynF empty) j))) , λ x₁ → contradiction (proj₂ (Sigma-equiv (sym x₁))) y))

-- (V : G => *) ▷ A means A either Dyn or Single _ Dyn
-- cast-result : {n : ℕ} {A' A B : Ty {n}} → Is-just (cast A' A B)
cast-lemma-6 : {n : ℕ} {e : Exp {n}} {A B C : Ty {n}} → Val e → [] ⊢ Cast e B C ▷ A → (A ≡ C) ⊎ (∃[ e ](∃[ W ](A ≡ Single{e = e} W C)))
cast-lemma-6 {n} {e} {A} {B} {C} V (CastA{A' = A'} j x x₁ x₂)
  with cast-result{n}{A'}{B}{C} x₁
... | inj₁ x₃ = inj₁ (≡-trans (sym x₂) x₃)
... | inj₂ (fst , fst₁ , snd) = inj₂ (fst , (fst₁ , (≡-trans (sym x₂) snd)))

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

data Result {n : ℕ} : Exp {n} → Set where
  RValue : {e : Exp {n}} → Val {n} e → Result {n} e
  RBlame :  Result {n} Blame

{-
-- Main theorem
data Progress-Type {n : ℕ} (A : Ty {n}) {j : [] ⊢ A} : Set where
  step : {A' : Ty {n}} → A ↠ A' → Progress-Type A
  result : ResultT A → Progress-Type A

data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ▷ T} : Set where
  step : {e' : Exp{n}} → e ⇨ e' → Progress e
  result : Result e → Progress e

progress-types : {n : ℕ} {A : Ty {n}} → (j : [] ⊢ A) → Progress-Type A {j}
progress : {n : ℕ} {e : Exp {n}} {T : Ty} → (j : [] ⊢ e ▷ T) → Progress e {T} {j}

progress-types {n} {.Dyn} (DynF x) = result (RNf NfDyn)
progress-types {n} {.UnitT} (UnitF x) = result (RNf NfUnit)
progress-types {n} {.Bot} (BotF x) = result RBot
progress-types {n} {.(Label _)} (LabF x) = result (RNf NfLabel)
progress-types {n} {.(Pi _ _)} (PiF j j₁)
  with progress-types {n} j
...  | step x = step (ξ-Pi x)
...  | result (RNf x) = result (RNf (NfPi{nfA = x}))
...  | result RBot = step Pi-Bot-L
progress-types {n} {.(Sigma _ _)} (SigmaF j j₁)
  with progress-types {n} j
...  | step x = step (ξ-Sigma x)
...  | result (RNf x) = result (RNf (NfSigma{nfA = x}))
...  | result RBot = step Sigma-Bot-L  
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
...  | yes eq rewrite eq = step (ξ-Case Cast-Collapse)
...  | no ¬eq = step (ξ-Case (Cast-Collide ¬eq))
progress {n} {CaseE (UCast {_} (VCastFun v) x₂) f} {T} (LabAEl (CastA{A = Dyn}{B = G}{A' = A'} (CastA{A = Pi nA B}{B = Pi nA' B'}{A' = A''} j x₅ x₆ x₇) x₁ x₃ x₄) x j₁) | cast-v
  with cast-result{A' = A''}{A = (Pi nA B)}{B = (Pi nA' B')} x₆
...  | inj₁ eq = contradiction x₃ (isnothing⇒¬isjust (cast-nothing{A = A'}{B = Dyn}{C = G} (notsingle λ e₁ B₁ W x₈ → contradiction (≡-trans (sym (≡-trans (sym x₇) eq)) x₈) (λ ()))
                                                                                                      λ x₈ → contradiction (≡-trans (sym (≡-trans (sym x₇) eq)) x₈) (λ ())))
...  | inj₂ (fst , snd , thd)
     with (sym (≡-trans (sym thd) x₇))
...     | eq' rewrite eq' = contradiction x₃ (isnothing⇒¬isjust (cast-nothing-single{A = Pi nA' B'}{B = Dyn}{C = G} (λ ()) (λ ())))
progress {n} {CaseE (UCast {e = e} x₁ x₂) f} {T} (LabAEl j x j₁) | (other-v{neq = neq}) = contradiction j (cast-lemma-3 neq x₁ x₂)

progress {n} {App N M} {.([ 0 ↦ M ]ᵀ _)} (PiAE j x (SubTypeA x₁ x₃) x₂)
  with progress {n} {N} j
...  | step r = step (ξ-App r)
...  | result RBlame = step App-Blame
...  | result (RValue v)
     with cf-pi-⇓ {n} {N} j x v
...     | inj₁ (fst , snd) rewrite snd = step (β-App M)
...     | inj₂ (fst , snd , thd , fth) rewrite fth = step Cast-Func
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
...  | result RBlame = step LetE-Blame
...  | result (RValue V) = step (β-LetE V)
progress {n} {(ProdV V N)} {.(Sigma _ _)} (PairAI j j₁)
  with progress {n} {N} j₁
...  | step r = step (ξ-ProdV r)
...  | result RBlame = step ProdV-Blame
...  | result (RValue W) = result (RValue (VProd V W))
progress {n} {.(Abs _)} {.(Pi _ _)} (PiAI j) = result (RValue VFun)
-- progress {n} {.Bot} {T} (BotA x) = result (RValue VBot)
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

progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok'} j x x₁ y)
  with  progress{e = e} j | progress-types ok | progress-types ok'
...  | step r | _ | _ = step (ξ-Cast r)
...  | result RBlame | _ | _ = step Cast-Blame
...  | result (RValue W) | step r | _ = step (Cast-Reduce-L{v = W} r)
...  | result (RValue W) | result (RNf nf) | step r = step (Cast-Reduce-R{v = W} nf r)
...  | result (RValue W) | result RBot | _ = step Cast-Bot-L
...  | result (RValue W) | result (RNf nf) | result RBot = step (Cast-Bot-R nf)
progress {n} {(Cast e A B)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB)
  with castView e
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn}
  with A ≡ᵀ? Dyn 
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq
  rewrite eq
  with TyG? B
...  | yes tyg
     with G₁ ≡ᵀ? B
...     | yes eq' rewrite eq' = step (Cast-Collapse{v = W}{g = x₂})
...     | no ¬eq' = step (Cast-Collide{v = W} ¬eq')
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg
  with cast-lemma-1 {n} {B} nfB ¬tyg
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | dyn = step (Cast-Dyn{v =(VCast W x₂)})
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | pi z z'
  with cast-lemma-5-1 {n} {B} (pi z z') (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))    
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | yes eq | no ¬tyg | sigma z z'
  with cast-lemma-5-1 {n} {B} (sigma z z') (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = (VCast W x₂)}{g = snd}{nfB = nfB} thd ok' fth (λ ()))


progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq
  with cast-lemma-6 {n} {e₁} {A'} {G₁} W j
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} (CastA{A' = A''} j' x' x₁' y') x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq | inj₁ eq' rewrite eq'
  with cast-trivial-just-inv{A = Dyn}{B = A}{C = B} x₁
...  | inj₁ eq'' = contradiction (sym eq'') ¬eq
...  | inj₂ (fst , snd , ())
progress {n} {Cast (Cast .e₁ .G₁ .Dyn) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCast W x₂)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = G₁} {.Dyn} | no ¬eq | inj₂ (fst , snd , thd) rewrite thd
  with cast-trivial-just-inv{A = Single snd Dyn}{B = A}{C = B} x₁  
...  | inj₁ eq'' = contradiction (sym eq'') (¬Single-nf nfA fst snd Dyn)
...  | inj₂ (fst' , snd' , thd') = contradiction (sym (proj₂ (Single-equiv thd'))) ¬eq

progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)}
  with cast-lemma-6 {n} {e₁} {A'} {Pi A° B°} {Pi A°° B°°} W j
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ rewrite x₂
  with cast-trivial-just-inv{A = Pi A°° B°°}{B = A}{C = B} x₁
...  | inj₁ x₃ rewrite (sym x₃)
     with B ≡ᵀ? Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | yes eq
  rewrite eq
  with TyG? (Pi A°° B°°)
...  | yes tyg = result (RValue (VCast (VCastFun W) tyg))
...  | no ¬tyg
     with cast-lemma-1 {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with cast-lemma-5-1 {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ok
...        | fst , snd , thd , fth = step (Cast-Factor-L thd ok fth (λ ()))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq
  with TyG? (Pi A°° B°°)
...  | yes tyg
     with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | yes tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | yes tyg | no ¬tyg'
  with x
...  | AConsDynR x₄ = contradiction refl ¬eq
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg
  with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₁ x₂ | inj₁ x₃ | no ¬eq | no ¬tyg | no ¬tyg'
  with x
... | AConsDynR x₄ = contradiction refl ¬eq
... | AConsRefl x₄ = result (RValue (VCastFun (VCastFun W)))
... | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
-- Repitition of the above
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) rewrite thd
  with cast-trivial-just-inv{A = Single snd (Pi A°° B°°)}{B = A}{C = B} x₁
...  | inj₁ x₂ = contradiction (sym x₂) (¬Single-nf nfA fst snd (Pi A°° B°°)) 
...  | inj₂ (fst' , snd' , thd')
     rewrite (sym (proj₂ (Single-equiv thd')))
     with B ≡ᵀ? Dyn
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)}
                                                                                                        | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | yes eq
  rewrite eq
  with TyG? (Pi A°° B°°)
...  | yes tyg = result (RValue (VCast (VCastFun W) tyg))
...  | no ¬tyg
     with cast-lemma-1 {n} {Pi A°° B°°} nfA ¬tyg
...     | pi x₄ x₅
        with cast-lemma-5-1 {n} {Pi A°° B°°} (pi x₄ x₅) (λ ()) ok
...        | fst° , snd° , thd° , fth° = step (Cast-Factor-L thd° ok fth° (λ ()))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq
  with TyG? (Pi A°° B°°)
...  | yes tyg
     with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | yes tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | yes tyg | no ¬tyg'
  with x
...  | AConsDynR x₄ = contradiction refl ¬eq
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg
  with TyG? B
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg | yes tyg'
  with x
...  | AConsRefl empty = result (RValue (VCastFun (VCastFun W)))
...  | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))
progress {n} {Cast (Cast .e₁ (Pi A° B°) (Pi A°° B°°)) A B} {T} (CastA {A' = A'} {ok = ok} {ok'} j x x₁ y) | result (RValue (VCastFun W)) | result (RNf nfA) | result (RNf nfB) | cast-v {e = e₁} {A = .(Pi _ _)} {.(Pi _ _)} | inj₂ (fst , snd , thd) | inj₂ (fst' , snd' , thd') | no ¬eq | no ¬tyg | no ¬tyg'
  with x
... | AConsDynR x₄ = contradiction refl ¬eq
... | AConsRefl x₄ = result (RValue (VCastFun (VCastFun W)))
... | AConsPi cons cons' = result (RValue (VCastFun (VCastFun W)))                                                                                                           


progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq}
  with nB ≡ᵀ? Dyn
...  | yes eq rewrite eq
     with TyG? nA
...     | yes tyg = result (RValue (VCast W tyg))
...     | no ¬tyg
        with cast-lemma-1 {n} {nA} nfA ¬tyg        
...        | dyn = step (Cast-Dyn{v = W})
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | yes eq | no ¬tyg | pi x₂ x₃
  with cast-lemma-5-1 {n} {nA} (pi x₂ x₃) (λ ()) ok
...  | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | yes eq | no ¬tyg | sigma x₂ x₃
  with cast-lemma-5-1 {n} {nA} (sigma x₂ x₃) (λ ()) ok
...  | fst , snd , thd , fth = step (Cast-Factor-L{v = W}{g = snd}{nfA = nfA} thd ok fth (λ ()))  
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq
  with nA ≡ᵀ? Dyn
...  | yes eq' rewrite eq'
     with TyG? nB     
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | yes tyg
  = contradiction (CastA j x x₁ y) (cast-lemma-3 {n} {e} {T} {nB} neq W tyg)
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg
  with cast-lemma-1 {n} {nB} nfB ¬tyg
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | dyn = contradiction refl ¬eq
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | pi x₂ x₃
  with cast-lemma-5-1 {n} {nB} (pi x₂ x₃) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = W}{g = snd}{nfB = nfB} thd ok' fth (λ ()))  
progress {n} {(Cast e nA nB)} {T} (CastA{ok = ok}{ok'} j x x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | yes eq' | no ¬tyg | sigma x₂ x₃
  with cast-lemma-5-1 {n} {nB} (sigma x₂ x₃) (λ ()) ok'
...  | fst , snd , thd , fth = step (Cast-Factor-R{v = W}{g = snd}{nfB = nfB} thd ok' fth (λ ()))    
progress {n} {Cast e .Dyn nB} {T} (CastA {ok = ok} {ok'} j (AConsDynL x) x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq'
progress {n} {Cast e nA .Dyn} {T} (CastA {ok = ok} {ok'} j (AConsDynR x) x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq
progress {n} {Cast e UnitT .UnitT} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Unit{v = W})
progress {n} {Cast e Dyn .Dyn} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = contradiction refl ¬eq
progress {n} {Cast e (Label x₂) .(Label x₂)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (RNf nfA) | result (RNf nfB) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = step (Cast-Label{v = W} (λ x → x))
progress {n} {Cast e (Pi nA nA₁) .(Pi nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (RNf (NfPi{nfA = nfA})) | result (RNf (NfPi{nfA = nfA'})) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = result (RValue (VCastFun{nfA = nfA}{nfA' = nfA'} W))
progress {n} {Cast e .(Pi _ _) .(Pi _ _)} {T} (CastA {ok = ok} {ok'} j (AConsPi x x₂) x₁ y) | result (RValue W) | result (RNf (NfPi{nfA = nfA})) | result (RNf (NfPi{nfA = nfA'})) | other-v{e = e}{neq} | no ¬eq | no ¬eq' = result (RValue (VCastFun{nfA = nfA}{nfA' = nfA'} W))
progress {n} {Cast e (Sigma nA nA₁) .(Sigma nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue W) | result (RNf (NfSigma{nfA = nfA})) | result (RNf (NfSigma{nfA = nfA'})) | other-v{e = e}{neq} |  no ¬eq | no ¬eq'
  with cast-lemma-4 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y)
progress {n} {Cast e (Sigma nA nA₁) .(Sigma nA nA₁)} {T} (CastA {ok = ok} {ok'} j (AConsRefl x) x₁ y) | result (RValue (VProd V W)) | result (RNf (NfSigma{nfA = nfA})) | result (RNf (NfSigma{nfA = nfA'})) | other-v{e = e}{neq} | no ¬eq | no ¬eq' | (fst , snd , thd , fth)
  = step (Cast-Pair{w = W})
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue W) | result (RNf (NfSigma{nfA = nfA})) | result (RNf (NfSigma{nfA = nfA'})) | other-v{e = e}{neq} | no ¬eq | no ¬eq'
  with cast-lemma-4 {n} {e} {nfA = nfA} {nfA' = nfA'} neq W (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y)
progress {n} {Cast e .(Sigma _ _) .(Sigma _ _)} {T} (CastA {ok = ok} {ok'} j (AConsSigma x x₂) x₁ y) | result (RValue (VProd V W)) | result (RNf (NfSigma{nfA = nfA})) | result (RNf (NfSigma{nfA = nfA'})) | other-v{e = e}{neq} | no ¬eq | no ¬eq' |  (fst , snd , thd , fth)
  = step (Cast-Pair{w = W})

-}
