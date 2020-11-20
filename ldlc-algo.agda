module ldlc-algo where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)

module defs where
  data Exp {n : ℕ} : Set where
    Var : ℕ → Exp {n}
    UnitE : Exp {n}
    Abs : Exp {n} → Exp {n}
    App : Exp {n} → Exp {n} → Exp {n}
    LabI : Fin n → Exp {n}
    CaseE : {s : Subset n} → Exp {n} → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    ProdV : Exp {n} → Exp {n} → Exp {n} -- first expression must be value!
    Let : Exp {n} → Exp {n} → Exp {n}

  data Val {n : ℕ} : Exp {n} → Set where
    VUnit : {n : ℕ} → Val UnitE
    VVar : {n : ℕ} → Val (Var n)
    VLab : {x : Fin n} → Val (LabI x)
    VFun : {N : Exp} → Val (Abs N)
    VProd : {N M' : Exp} → Val N → Val M' → Val (ProdV N  M')

  data Ty {n : ℕ} : Set where
    UnitT : Ty
    Single : Exp {n} → Ty {n} → Ty
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    CaseT : {s : Subset n} → Exp {n} → (f : ∀ l → l ∈ s → Ty {n}) → Ty 

  -- Useful shorthands
  data notSingle {n : ℕ} : Ty {n} → Set where
    notsingle : {A : Ty {n}} → (∀ W B → ¬ (A ≡ Single W B)) → notSingle A
    
  ---- Algorithmic Typing
  -- Type environment
  data TEnv {n : ℕ} : Set
  -- Type environment access
  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set
  -- Type formation
  data _⊢_ {n : ℕ} : TEnv {n}→ Ty {n} → Set
  -- Type synthesis
  data _⊢_⇒_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
  -- Type check
  data _⊢_⇐_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
  -- Check subtype (⇐ instead of ⇒?)
  data _⇒_≤_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
  -- Unfolding (e.g. CaseT ... ⇓ T)
  data _⊢_⇓_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set

  -- Type environment concatenation & required proofs
  _++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
  ⊢-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} → Γ ⊢ A → (Γ ++ Γ') ⊢ A
  ⊢⇒-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} {M : Exp {n}} → Γ ⊢ M ⇒ A → (Γ ++ Γ') ⊢ M ⇒ A
  ⊢⇐-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} {M : Exp {n}} → Γ ⊢ M ⇐ A → (Γ ++ Γ') ⊢ M ⇐ A
  ⇒≤-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A B : Ty {n}} → Γ ⇒ A ≤ B → (Γ ++ Γ') ⇒ A ≤ B
  ⇓-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A ⇓ B → (Γ ++ Γ') ⊢ A ⇓ B

  -- Type environment length
  length : {n : ℕ} → TEnv {n} → ℕ
  
  -- Implementations
  data TEnv {n} where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty) (Γ : TEnv {n}) {ok : Γ ⊢ T} → TEnv

  data _∶_∈_ {n} where
    here : {T : Ty} {Γ : TEnv} {ok : Γ ⊢ T} → 0 ∶ T ∈ ⟨ T , Γ ⟩ {ok}
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} {ok : Γ ⊢ T₂} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩ {ok}

  [] ++ Γ' = Γ'
  ⟨ T , Γ ⟩ {ok} ++ Γ' = ⟨ T , Γ ++ Γ' ⟩ {ok = ⊢-++ ok}

  data _⊢_ {n} where
    UnitF : {Γ : TEnv {n}} → Γ ⊢ UnitT
    LabF : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L
    PiF : {Γ : TEnv {n}} {A B : Ty {n}} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Pi A B
    SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Sigma A B
    SingleF : {Γ : TEnv {n}} {A : Ty {n}} {V : Exp {n}} {val : Val V} → Γ ⊢ V ⇐ A → notSingle A → Γ ⊢ Single V A
    CaseF : {Γ : TEnv {n}} {L : Subset n} {V : Exp {n}} {val : Val V} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ V ⇐ Label L → Γ ⊢ CaseT V f
  
  data _⊢_⇒_ {n} where
    VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → x ∶ A ∈ Γ → Γ ⊢ Var x ⇒ A
    UnitAI : {Γ : TEnv {n}} → Γ ⊢ UnitE ⇒ UnitT
    LabAI : {Γ : TEnv {n}} {l : Fin n} → Γ ⊢ LabI l ⇒ Single (LabI l) (Label ⁅ l ⁆)
    LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {V : Exp {n}} {val : Val V} {ins : l ∈ L} {f : ∀ l → l ∈ L → Exp {n}}
             → Γ ⊢ V ⇒ Single (LabI l) (Label L')
             → L' ⊆ L
             → Γ ⊢ (f l ins) ⇒ B
             → Γ ⊢ CaseE V f ⇒ B
    LabAEx : {Γ Γ' : TEnv {n}} {D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}}
             → Γ ⇒ D ≤ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (LabI l) (Label L)) , Γ ⟩ {ok = SingleF {!!} {!!}}) ⊢ (f l i) ⇒ (f-t l i))   -- ⇐ required
             → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseE (Var (length Γ')) f ⇒ CaseT (Var (length Γ')) f-t

  data _⊢_⇐_ {n} where
    
