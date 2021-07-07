------------------------------------------------------------------------
-- Typing, small and big step semantics
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module Typing-Semantics where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Fin hiding (cast)
open import Data.Fin.Properties
open import Data.Vec hiding (_++_ ; length)
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ ; ⊤ to ⊤ˢ ; ⊥ to ⊥ˢ)
open import Data.Fin.Subset.Properties
open import Data.List hiding (_++_ ; length)
open import Data.List.Relation.Unary.All
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
open import Data.Empty
open import Size renaming (↑_ to ↑ˡ)

open import Aux

open import Syntax
open import Substitution

------------------------------------------------------------------------
-- Type environment

data TEnv {n : ℕ} : Set where
  [] : TEnv
  ⟨_,_⟩ : (T : Ty {n}) (Γ : TEnv {n}) → TEnv

data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set where
  here : {T : Ty} {Γ : TEnv} → 0 ∶ T ∈ ⟨ T , Γ ⟩
  there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩

-- Functions
_++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
[] ++ Γ' = Γ'
⟨ T , Γ ⟩ ++ Γ' = ⟨ T , Γ ++ Γ' ⟩

length : {n : ℕ} → TEnv {n} → ℕ
length {n} [] = zero
length {n} ⟨ T , Γ ⟩ = ℕ.suc (length Γ)

-- Properties
++-assoc : {n : ℕ} {Γ Γ' Γ'' : TEnv {n}} → Γ ++ (Γ' ++ Γ'') ≡ (Γ ++ Γ') ++ Γ''
++-assoc {n} {[]} {Γ'} {Γ''} = refl
++-assoc {n} {⟨ T , Γ ⟩} {Γ'} {Γ''} = cong (λ x → ⟨ T , x ⟩) (++-assoc{n}{Γ}{Γ'}{Γ''})

------------------------------------------------------------------------
-- Typing judgements

---- Algorithmic Typing
-- Type environment formation
data ⊢_ok {n : ℕ} : TEnv {n} → Set
-- Double type environment formation
-- data ⊢_∣_ok {n : ℕ} : TEnv {n} → TEnv {n} → Set
-- Type formation
data _⊢_ {n : ℕ} : TEnv {n}→ Ty {n} → Set
-- Type synthesis
data _⊢_▷_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
-- Type check
data _⊢_◁_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
-- Check subtype (⇐ instead of ⇒?)
data _⊢_≤ᵀ_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
-- Unfolding (e.g. CaseT ... ⇓ T)
data _⊢_⇓_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
-- precise cast function
cast : {n : ℕ} → Ty {n} → Ty {n} → Ty {n} → Ty {n}

-- Implementations

data ⊢_ok {n} where
  empty : ⊢ [] ok
  entry : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ A → ⊢ ⟨ A , Γ ⟩ ok

data _⊢_ {n} where
  DynF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Dyn
  UnitF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitT
  BotF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Bot
  LabF : {Γ : TEnv {n}} {L : Subset n} → ⊢ Γ ok → Γ ⊢ Label L
  PiF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Pi A B
  SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Sigma A B
  SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {ok : Γ ⊢ A} → ⊢ Γ ok → Γ ⊢ e ◁ A → TyB A → Γ ⊢ Single e A
  CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ◁ Label L → Γ ⊢ CaseT e f

data _⊢_◁_ {n} where
  SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
             → Γ ⊢ M ▷ A
             → Γ ⊢ A ≤ᵀ B
             → Γ ⊢ M ◁ B
  LabelChkA : {Γ : TEnv {n}} {L : Subset n} {l : Fin n}
              → l ∈ L
              → Γ ⊢ LabI l ◁ Label L
  UnitChkA : {Γ : TEnv {n}}
             → Γ ⊢ UnitE ◁ UnitT
  CastChkA : {Γ : TEnv {n}} {M : Exp {n}} {A B B' : Ty {n}}
             → Γ ⊢ M ◁ A
             → Γ ⊢ B ≤ᵀ B'
             → Γ ⊢ (Cast M A B) ◁ B'

data _⊢_≤ᵀ_ {n} where
  ASubBot : {Γ : TEnv {n}} {T : Ty {n}} {ok : Γ ⊢ T} → Γ ⊢ Bot ≤ᵀ T
  ASubDyn : {Γ : TEnv {n}} → Γ ⊢ Dyn ≤ᵀ Dyn  
  ASubUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≤ᵀ UnitT
  ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⊢ Label L ≤ᵀ Label L'
  ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ≤ᵀ B → TyB B → notSingle B → Γ ⊢ Single e A ≤ᵀ B
  ASubSingleSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e e' : Exp {n}} {V : Val e} {W : Val e'} → e ≡ e' → Γ ⊢ A ≤ᵀ B → Γ ⊢ Single e A ≤ᵀ Single e' B
  ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
           → Γ ⊢ A' ≤ᵀ A
           → ⟨ A' , Γ ⟩ ⊢ B ≤ᵀ B'
           → Γ ⊢ Pi A B ≤ᵀ Pi A' B'
  ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
              → Γ ⊢ A ≤ᵀ A'
              → ⟨ A , Γ ⟩ ⊢ B ≤ᵀ B'
              → Γ ⊢ Sigma A B ≤ᵀ Sigma A' B'
            
  ASubCaseLL : {Γ : TEnv {n}} {B D : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (LabI  l) D
               → (ins : l ∈ L)
               → Γ ⊢ (f l ins) ≤ᵀ B
               → Γ ⊢ CaseT e f ≤ᵀ B           
  ASubCaseLR : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (LabI l) D
               → (ins : l ∈ L)
               → Γ ⊢ A ≤ᵀ (f l ins)
               → Γ ⊢ A ≤ᵀ CaseT e f           
  ASubCaseXL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (LabI l) (Label ⁅ l ⁆) ≤ᵀ D)
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (LabI l) D , Γ ⟩) ⊢ (f l (sub i)) ≤ᵀ B)
               → Θ ⊢ CaseT (Var (length Γ')) f ≤ᵀ B
  ASubCaseXR : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (LabI l) (Label ⁅ l ⁆) ≤ᵀ D)             
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (LabI l) D , Γ ⟩) ⊢ A ≤ᵀ (f l (sub i)))
               → Θ ⊢ A ≤ᵀ CaseT (Var (length Γ')) f
  ASubCaseBL : {Γ : TEnv {n}} {B : Ty} {e : Exp {n}} {U : ValU e} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Bot
               → Γ ⊢ CaseT e f ≤ᵀ B
  ASubCaseCL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
                → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) f ≤ᵀ B
  ASubCaseCR : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ B ≤ᵀ (f l i))
                → Θ ⊢ B ≤ᵀ CaseT (Cast (Var (length Γ')) D (Label L)) f

data _⊢_▷_ {n} where
  BlameA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Blame ▷ Bot
  VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
  CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} {ok : Γ ⊢ A} {ok' : Γ ⊢ B}
           → Γ ⊢ M ▷ A' → B' ≡ (cast A' A B) → Γ ⊢ Cast M A B ▷ B'
  UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ▷ Single UnitE UnitT
  LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ▷ Single (LabI l) (Label ⁅ l ⁆)
  LabAEl : {Γ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {l : Fin n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
           → Γ ⊢ e ▷ Single (LabI l) D
           → (ins : l ∈ L)
           → Γ ⊢ (f l ins) ▷ B
           → Γ ⊢ CaseE e f ▷ B
  LabAEl-Bot : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
               → Γ ⊢ e ▷ Bot
               → Γ ⊢ CaseE e f ▷ Bot
  -- unification has problems with arbitrary functions, hence θ
  -- see https://lists.chalmers.se/pipermail/agda/2020/012293.html
  LabAEx : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L' → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
           → Γ ⊢ D ≤ᵀ Label L
           → (∀ l → l ∈ L' → Γ ⊢ Single (LabI l) (Label ⁅ l ⁆) ≤ᵀ D)
           → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ (Single (LabI l)) D , Γ ⟩) ⊢ (f l (sub i)) ▷ (f-t l i))
           → Θ ⊢ CaseE (Var (length Γ')) f ▷ CaseT (Var (length Γ')) f-t
  LabAExDyn : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → notSingle D
            → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (LabI l) (Label L)) (Label L) D)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
            → Θ ⊢ CaseE (Cast (Var (length Γ')) D (Label L)) f ▷ CaseT (Cast (Var (length Γ')) D (Label L)) f-t
  PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ▷ B → Γ ⊢ Abs M ▷ Pi A B
  PiAE-V : {Γ : TEnv {n}} {A B D F : Ty {n}} {M N : Exp {n}} {V : Val N} {eq : F ≡ [ 0 ↦ N ]ᵀ B}
         → Γ ⊢ M ▷ D
         → Γ ⊢ D ⇓ Pi A B
         → Γ ⊢ N ◁ A
         → 0 ∈`ᵀ B  -- for determinism
         → Γ ⊢ F
         → Γ ⊢ App M N ▷ F
  PiAE : {Γ : TEnv {n}} {A B D : Ty {n}} {M N : Exp {n}}
         → Γ ⊢ M ▷ D
         → Γ ⊢ D ⇓ Pi A B
         → Γ ⊢ N ◁ A
         → ¬ (0 ∈`ᵀ B)
         → Γ ⊢ B
         → Γ ⊢ App M N ▷ B       
  SigmaAI : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
            → Γ ⊢ M ◁ A
            → ⟨ A , Γ ⟩ ⊢ N ▷ B
            → Γ ⊢ Prod M N ▷ Sigma A B
  PairAI : {Γ : TEnv {n}} {A B : Ty {n}} {e N : Exp {n}} {V : Val e}
           -- x ∉ Γ redundant, DeBruijn
           → Γ ⊢ e ▷ A
           → Γ ⊢ N ▷ B
           → Γ ⊢ ProdV e N ▷ Sigma A B
  SigmaAE : {Γ : TEnv {n}} {A B C D : Ty {n}} {M N : Exp {n}}
          → Γ ⊢ M ▷ D
          → Γ ⊢ D ⇓ Sigma A B
          → ⟨ B , ⟨ A , Γ ⟩ ⟩ ⊢ N ▷ C
          → (¬ (0 ∈`ᵀ C)) × (¬ (1 ∈`ᵀ C))
          → Γ ⊢ LetP M N ▷ C           
  LetA : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
         → ¬(0 ∈`ᵀ B)
         → Γ ⊢ M ▷ A
         → ⟨ A , Γ ⟩ ⊢ N ▷ B
         → Γ ⊢ LetE M N ▷ B

data _⊢_⇓_ {n} where
  AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
  AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
  AUCaseL-P : {Γ : TEnv {n}} {A B D : Ty {n}} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (LabI l) D
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Pi A B
            → Γ ⊢ CaseT e f ⇓ Pi A B        
  AUCaseL-S : {Γ : TEnv {n}} {A B D : Ty {n}} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (LabI l) D
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Sigma A B
            → Γ ⊢ CaseT e f ⇓ Sigma A B            
  AUCaseX-P : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (LabI l) (Label ⁅ l ⁆) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (LabI l) D , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Pi (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (Var (length Γ')) fᴬ ⇓ Pi (CaseT (Var (length Γ')) fᴮ) (CaseT (Var (ℕ.suc (length Γ'))) fᶜ)          
  AUCaseX-S : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (LabI l) (Label ⁅ l ⁆) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (LabI l) D , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Sigma (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (Var (length Γ')) fᴬ ⇓ Sigma (CaseT (Var (length Γ')) fᴮ) (CaseT (Var (ℕ.suc (length Γ'))) fᶜ)
  AUCaseXDyn-P : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L : Subset n} {fᴬ fᴮ fᶜ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Pi (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) fᴬ ⇓ Pi (CaseT (Cast (Var (length Γ')) D (Label L)) fᴮ) (CaseT (Cast (Var (length Γ')) D (Label L)) fᶜ)            
  AUCaseXDyn-S : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L : Subset n} {fᴬ fᴮ fᶜ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Sigma (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) fᴬ ⇓ Sigma (CaseT (Cast (Var (length Γ')) D (Label L)) fᴮ) (CaseT (Cast (Var (length Γ')) D (Label L)) fᶜ)            

------------------------------------------------------------------------
-- Type normal form, type matching, properties

data TyNf {n} : Ty {n} → Set where
  NfDyn : TyNf Dyn
  NfUnit : TyNf UnitT
  NfLabel : {s : Subset n} → TyNf (Label s)
  NfPi : {A B : Ty {n}} → TyNf (Pi A B)
  NfSigma : {A B : Ty {n}} → TyNf (Sigma A B)
  NfSingle : {B : Ty {n}} {e : Exp {n}} {V : Val e} {tybB : TyB B} {notsingle : notSingle B} → TyNf (Single e B)

_match : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → TyNf A → Σ (Ty {n}) (TyG)
_match {neq = neq} NfDyn = contradiction refl neq
NfUnit match = UnitT , GG' GUnit
NfLabel {s = s} match = Label s , GG' GLabel
NfPi match = (Pi Dyn Dyn) , (GG' GPi)
NfSigma match = Sigma Dyn Dyn , GG' GSigma
NfSingle{B = B}{e}{V}{tybB}{notsingl} match = Single e B , (GSingle{V = V}{tygG = notsingle×TyB⊂TyG' notsingl tybB})

data ¬TyG×TyNf {n : ℕ} : Ty {n} → Set where
  Dyn : ¬TyG×TyNf Dyn
  Pi : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Pi A B)
  Sigma : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Sigma A B)

¬TyG×TyNf-in : {n : ℕ} {A : Ty {n}} → ¬ (TyG A) → TyNf A → ¬TyG×TyNf A
¬TyG×TyNf-in {n} {.Dyn} ntyg NfDyn = Dyn
¬TyG×TyNf-in {n} {.UnitT} ntyg NfUnit = contradiction (GG' GUnit) ntyg
¬TyG×TyNf-in {n} {.(Label _)} ntyg NfLabel = contradiction (GG' GLabel) ntyg
¬TyG×TyNf-in {n} {.(Single _ _)} ntyg (NfSingle{V = V}{tybB = tybB}{notsingle = notsingl}) = contradiction (GSingle{V = V}{tygG = notsingle×TyB⊂TyG' notsingl tybB}) ntyg
¬TyG×TyNf-in {n} {(Pi A B)} ntyg NfPi
  with A ≡ᵀ? Dyn
...  | no ¬p = Pi (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬q = Pi (inj₂ ¬q)     
...     | yes q rewrite p | q = contradiction (GG' GPi) ntyg
¬TyG×TyNf-in {n} {(Sigma A B)} ntyg NfSigma
  with A ≡ᵀ? Dyn
...  | no ¬p = Sigma (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬q = Sigma (inj₂ ¬q)     
...     | yes q rewrite p | q = contradiction (GG' GSigma) ntyg

data TyG×TyNf {n : ℕ} : Ty {n} → Set where
  Unit : TyG×TyNf UnitT
  Label : {s : Subset n} → TyG×TyNf (Label s)
  Pi : TyG×TyNf (Pi Dyn Dyn)
  Sigma : TyG×TyNf (Sigma Dyn Dyn)
  Single : {A : Ty {n}} {e : Exp {n}} → TyG' A → TyB A → TyG×TyNf (Single e A)

TyG×TyNf-in : {n : ℕ} {A : Ty {n}} → TyG A → TyNf A → TyG×TyNf A
TyG×TyNf-in {n} {.(Single _ _)} (GSingle{tygG = tygG}) (NfSingle{tybB = tybB}{notsingle = notsingl}) = Single tygG tybB
TyG×TyNf-in {n} {.UnitT} (GG' GUnit) NfUnit = Unit
TyG×TyNf-in {n} {.(Label _)} (GG' GLabel) NfLabel = Label
TyG×TyNf-in {n} {.(Pi Dyn Dyn)} (GG' GPi) NfPi = Pi
TyG×TyNf-in {n} {.(Sigma Dyn Dyn)} (GG' GSigma) NfSigma = Sigma

TyG×TyNf⇒match-equiv : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → TyG A → (tynfa : TyNf A) → (proj₁ (_match{neq = neq} tynfa)) ≡ A
TyG×TyNf⇒match-equiv {n} {A} {neq} tyga tynfa
  with TyG×TyNf-in tyga tynfa
TyG×TyNf⇒match-equiv {n} {UnitT} {neq} tyga NfUnit | Unit = refl
TyG×TyNf⇒match-equiv {n} {Label s} {neq} tyga NfLabel | Label = refl
TyG×TyNf⇒match-equiv {n} {Pi Dyn Dyn} {neq} tyga NfPi | Pi = refl
TyG×TyNf⇒match-equiv {n} {Sigma Dyn Dyn} {neq} tyga NfSigma | Sigma = refl
TyG×TyNf⇒match-equiv {n} {.(Single _ _)} {neq} tyga NfSingle | Single x x₁ = refl

------------------------------------------------------------------------
-- Algorithm for subtyping, limited to ground types

[]⊢_≤ᵀ?'_ : {n : ℕ} {G H : Ty {n}} (tygG : TyG' G) (tygH : TyG' H) → Dec ([] ⊢ G ≤ᵀ H)
[]⊢_≤ᵀ?_ : {n : ℕ} {G H : Ty {n}} (tygG : TyG G) (tygH : TyG H) → Dec ([] ⊢ G ≤ᵀ H)

[]⊢_≤ᵀ?'_ {n} {.UnitT} {.UnitT} GUnit GUnit = yes ASubUnit
[]⊢_≤ᵀ?'_ {n} {.UnitT} {.(Label _)} GUnit GLabel = no λ ()
[]⊢_≤ᵀ?'_ {n} {.UnitT} {.(Pi Dyn Dyn)} GUnit GPi = no λ ()
[]⊢_≤ᵀ?'_ {n} {.UnitT} {.(Sigma Dyn Dyn)} GUnit GSigma = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Label _)} {.UnitT} GLabel GUnit = no λ ()
[]⊢_≤ᵀ?'_ {n} {(Label s)} {(Label s')} GLabel GLabel
  with s ⊆? s'
...  | yes p = yes (ASubLabel p)
...  | no ¬p = no ϱ
     where ϱ : ([] ⊢ Label s ≤ᵀ Label s') → Data.Empty.⊥
           ϱ (ASubLabel x) = ¬p x
[]⊢_≤ᵀ?'_ {n} {.(Label _)} {.(Pi Dyn Dyn)} GLabel GPi = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Label _)} {.(Sigma Dyn Dyn)} GLabel GSigma = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Pi Dyn Dyn)} {.UnitT} GPi GUnit = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Pi Dyn Dyn)} {.(Label _)} GPi GLabel = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Pi Dyn Dyn)} {.(Pi Dyn Dyn)} GPi GPi = yes (ASubPi ASubDyn ASubDyn)
[]⊢_≤ᵀ?'_ {n} {.(Pi Dyn Dyn)} {.(Sigma Dyn Dyn)} GPi GSigma = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Sigma Dyn Dyn)} {.UnitT} GSigma GUnit = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Sigma Dyn Dyn)} {.(Label _)} GSigma GLabel = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Sigma Dyn Dyn)} {.(Pi Dyn Dyn)} GSigma GPi = no λ ()
[]⊢_≤ᵀ?'_ {n} {.(Sigma Dyn Dyn)} {.(Sigma Dyn Dyn)} GSigma GSigma = yes (ASubSigma ASubDyn ASubDyn)

[]⊢_≤ᵀ?_ {n} {(Single .e G)} {(Single .e' H)} (GSingle{e = e}{V = V}{tygG = tygG}) (GSingle{e = e'}{V = W}{tygG = tygH})
  with e ≡ᵉ? e' | []⊢_≤ᵀ?'_ tygG tygH
...  | yes p | yes q = yes (ASubSingleSingle{V = V}{W = W} p q)
...  | no ¬p | _ = no ϱ
     where ϱ : ¬ ([] ⊢ (Single e G) ≤ᵀ (Single e' H))
           ϱ (ASubSingle x x₁ x₂) = contradiction x₂ notnotsingle-single
           ϱ (ASubSingleSingle x leq) = ¬p x
...  | _ | no ¬p = no ϱ
     where ϱ : ¬ ([] ⊢ (Single e G) ≤ᵀ (Single e' H))
           ϱ (ASubSingle x x₁ x₂) = contradiction x₂ notnotsingle-single
           ϱ (ASubSingleSingle x leq) = ¬p leq
[]⊢_≤ᵀ?_ {n} {(Single e G)} {H} (GSingle{V = V}{tygG = tygG}) (GG' tygH)
  with []⊢_≤ᵀ?'_ tygG tygH | TyB? H
...  | yes p | yes q = yes (ASubSingle{V = V} p q (TyG'⇒notSingle tygH))
...  | no ¬p | _ = no ϱ
     where ϱ : ¬ ([] ⊢ Single e G ≤ᵀ H)
           ϱ (ASubSingle leq x x₁) = ¬p leq
...  | _ | no ¬q = no ϱ
     where ϱ : ¬ ([] ⊢ Single e G ≤ᵀ H)
           ϱ (ASubSingle leq x x₁) = ¬q x
[]⊢_≤ᵀ?_ {n} {.UnitT} {Single V H} (GG' GUnit) GSingle = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Label _)} {Single V H} (GG' GLabel) GSingle = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {Single V H} (GG' GPi) GSingle = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {Single V H} (GG' GSigma) GSingle = no λ ()
[]⊢_≤ᵀ?_ {n} {G} {H} (GG' x) (GG' x₁)
  with []⊢_≤ᵀ?'_ x x₁
...  | yes p = yes p
...  | no ¬p = no (λ x₂ → ¬p x₂)

------------------------------------------------------------------------
-- Small-step semantics

-- Type reduction
data _↠_ {n : ℕ} : Ty {n} → Ty {n} → Set
-- Expression reduction
data _⇨_ {n : ℕ} : Exp {n} → Exp {n} → Set

data _↠_ {n} where
  ξ-Case : {e e' : Exp {n}} {U : ValU e} {U' : ValU e'} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → e ⇨ e' → CaseT e f ↠ CaseT e' f
  β-Case : {l : Fin n} {s : Subset n} {ins : l ∈ s} {f : ∀ l → l ∈ s → Ty {n}} → CaseT (LabI l) f ↠ f l ins
  Case-Bot : {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → CaseT Blame f ↠ Bot

data _⇨_ {n} where
  ξ-App₁ : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → App e₁ e ⇨ App e₁' e
  ξ-App₂ : {e₂ e₂' e : Exp {n}} {v : Val e} → e₂ ⇨ e₂' → App e e₂ ⇨ App e e₂'
  ξ-LetE : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → LetE e₁ e ⇨ LetE e₁' e
  ξ-Prod : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → Prod e₁ e ⇨ Prod e₁' e
  ξ-ProdV : {e e₂ e₂' : Exp {n}} {v : Val e} → e₂ ⇨ e₂' → ProdV e e₂ ⇨ ProdV e e₂'
  ξ-LetP : {e₁ e₁' e₂ : Exp {n}} → e₁ ⇨ e₁' → LetP e₁ e₂ ⇨ LetP e₁' e₂
  ξ-Cast : {e₁ e₂ : Exp {n}} {A B : Ty {n}} → e₁ ⇨ e₂ → Cast e₁ A B ⇨ Cast e₂ A B
  ξ-Case : {s : Subset n} {e₁ e₂ : Exp {n}} {U : ValU e₁} {U' : ValU e₂} {f : ∀ l → l ∈ s → Exp {n}} → e₁ ⇨ e₂ → CaseE e₁ f ⇨ CaseE e₂ f
  β-App : {e e' : Exp {n}} → (v : Val e') → (App (Abs e) e') ⇨ (↑⁻¹[ ([ 0 ↦ ↑¹[ e' ] ] e) ])
  β-Prod : {e e' : Exp {n}} {v : Val e} → Prod e e' ⇨ ProdV e (↑⁻¹[ ([ 0 ↦ ↑¹[ e ] ] e') ])    
  β-LetE : {e e' : Exp {n}} → (v : Val e) → LetE e e' ⇨ (↑⁻¹[ ([ 0 ↦ ↑¹[ e ] ] e') ])
  β-LetP : {e e' e'' : Exp {n}} → (v : Val e) → (v' : Val e')
                            → LetP (ProdV e e') e''
                              ⇨
                              ↑ (ℤ.negsuc 1) , 0 [ ([ 0 ↦ ↑¹[ e ] ]
                                                     ([ 0 ↦ ↑ (ℤ.pos 1) , 1 [ e' ] ] e'')) ]                                                     
  β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} {x : Fin n} → (ins : x ∈ s)
           → CaseE (LabI x) f ⇨ f x ins         
  Cast-Dyn : {e : Exp {n}} {v : Val e} → Cast e Dyn Dyn ⇨ e
  Cast-Sub : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H} → [] ⊢ G ≤ᵀ H → Cast e G H ⇨ e
  Cast-Fail : {e : Exp {n}} {v : Val e} {nA nB : Ty {n}} {tynfA : TyNf nA} {tynfB : TyNf nB} {neq : nA ≢ Dyn × nB ≢ Dyn} → ¬ ([] ⊢ proj₁ (_match{neq = proj₁ neq} tynfA) ≤ᵀ proj₁ (_match{neq = proj₂ neq} tynfB)) → Cast e nA nB ⇨ Blame
  Cast-Collapse : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H} → [] ⊢ G ≤ᵀ H → Cast (Cast e G Dyn) Dyn H ⇨ e
  Cast-Collide : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H} → ¬ ([] ⊢ G ≤ᵀ H) → Cast (Cast e G Dyn) Dyn H ⇨ Blame
  Cast-Pair : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}}
              → Cast (ProdV e e') (Sigma A B) (Sigma A' B') ⇨ Prod (Cast e A A') (Cast e' B B') 
  Cast-Func : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}} → App (Cast e (Pi A B) (Pi A' B')) e' ⇨ Cast (App e (Cast e' A' A)) ([ 0 ↦ Cast e' A' A ]ᵀ B) ([ 0 ↦ e' ]ᵀ B')
  Cast-Reduce-L : {e : Exp {n}} {v : Val e} {A A' B : Ty {n}} → A ↠ A' → Cast e A B ⇨ Cast e A' B
  Cast-Reduce-R : {e : Exp {n}} {v : Val e} {A B B' : Ty {n}} → TyNf A → B ↠ B' → Cast e A B ⇨ Cast e A B'
  Cast-Factor-L : {e : Exp {n}} {v : Val e} {nA : Ty {n}} {nfA : TyNf nA} → (neq : nA ≢ Dyn) → Cast e nA Dyn ⇨ Cast (Cast e nA (proj₁ (_match{neq = neq} nfA))) (proj₁ (_match{neq = neq} nfA)) Dyn
  Cast-Factor-R : {e : Exp {n}} {v : Val e} {nB : Ty {n}} {nfB : TyNf nB} → (neq : nB ≢ Dyn) → Cast e Dyn nB ⇨ Cast (Cast e Dyn (proj₁ (_match{neq = neq} nfB))) (proj₁ (_match{neq = neq} nfB)) nB  
  App₁-Blame : {e : Exp {n}} → App Blame e ⇨ Blame
  App₂-Blame : {e : Exp {n}} {v : Val e} → App e Blame ⇨ Blame
  LetE-Blame : {e : Exp {n}} → LetE Blame e ⇨ Blame
  Prod-Blame : {e : Exp {n}} → Prod Blame e ⇨ Blame
  ProdV-Blame : {e : Exp {n}} {v : Val e} → ProdV e Blame ⇨ Blame
  LetP-Blame : {e  : Exp {n}} → LetP Blame e ⇨ Blame
  Cast-Blame : {A B : Ty {n}} → Cast Blame A B ⇨ Blame
  Case-Blame : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} → CaseE Blame f ⇨ Blame

infix  2 _⇛_
infix  1 begin_
infixr 2 _⇨⟨_⟩_
infix  3 _∎

data _⇛_ {n : ℕ} : Exp {n} → Exp {n} → Set where
  _∎ : (e : Exp {n}) → e ⇛ e
  _⇨⟨_⟩_ : {e' e'' : Exp {n}} → (e : Exp {n}) → e ⇨ e' → e' ⇛ e'' → e ⇛ e''

begin_ : {n : ℕ} {e e' : Exp {n}} → e ⇛ e' → e ⇛ e'
begin e⇛e' = e⇛e'

------------------------------------------------------------------------
-- Evaluation

data Result {n : ℕ} : (e : Exp {n}) → Set where
  RValue : {e : Exp {n}} → Val e → Result e
  RBlame : Result Blame

data ResultType {n : ℕ} : (A : Ty {n}) → Set where
  RNf : {A : Ty {n}} → TyNf A → ResultType A
  RBot : ResultType Bot

data eval-step-expr {n : ℕ} (e : Exp {n}) : Set where
  step : {e' : Exp {n}} → e ⇨ e' → eval-step-expr e
  result : Result e → eval-step-expr e
  stuck : eval-step-expr e

data eval-step-type {n : ℕ} (A : Ty {n}) : Set where
  step : {A' : Ty {n}} → A ↠ A' → eval-step-type A
  result : ResultType A → eval-step-type A
  stuck : eval-step-type A

evaluate-step-type : {n : ℕ} (A : Ty {n}) → eval-step-type A
evaluate-step-expr : {n : ℕ} (e : Exp {n}) → eval-step-expr e

evaluate-step-type UnitT = result (RNf NfUnit)
evaluate-step-type (Single x A)
  with Val? x | TyB? A | issingle? A
...  | yes v | yes tyb | no ¬sgl = result (RNf (NfSingle{V = v}{tybB = tyb}{notsingle = notsingle λ e → ¬∃⇒∀¬ ((¬∃⇒∀¬ ¬sgl) e)}))
...  | no ¬v | yes tyb | no ¬sgl = stuck
...  | yes v | no ¬tyb | no ¬sgl = stuck
...  | no ¬v | no ¬tyb | no ¬sgl = stuck
...  | yes v | yes tyb | yes sgl = stuck
...  | no ¬v | yes tyb | yes sgl = stuck
...  | yes v | no ¬tyb | yes sgl = stuck
...  | no ¬v | no ¬tyb | yes sgl = stuck

evaluate-step-type (Label x) = result (RNf NfLabel)
evaluate-step-type (Pi A A₁) = result (RNf NfPi)
evaluate-step-type (Sigma A A₁) = result (RNf NfSigma)
evaluate-step-type Dyn = result (RNf NfDyn)

evaluate-step-type Bot = result RBot

evaluate-step-type (CaseT{s = s} x f)
  with evaluate-step-expr x
...  | stuck = stuck
...  | step {e' = e'} st --  = step (ξ-Case st)
     with ValU? x | ValU? e'
...     | yes p | yes q = step (ξ-Case{U = p}{U' = q} st)
...     | no ¬p | yes q = stuck
...     | yes p | no ¬q = stuck
...     | no ¬p | no ¬q = stuck
evaluate-step-type (CaseT{s = s} x f) | result RBlame = step (Case-Bot)
evaluate-step-type (CaseT{s = s} x f) | result (RValue v)
     with v
...     | VUnit = stuck
...     | VFun = stuck
...     | VProd a b = stuck
...     | VCast a b = stuck
...     | VCastFun a = stuck
...     | VLab{x = l}
        with l ∈? s
...        | yes ins = step (β-Case{ins = ins})
...        | no ¬ins = stuck

evaluate-step-expr UnitE = result (RValue VUnit)
evaluate-step-expr (Abs e) = result (RValue VFun)
evaluate-step-expr (LabI x) = result (RValue (VLab{x = x}))

evaluate-step-expr Blame = result RBlame

evaluate-step-expr (Var x) = stuck

evaluate-step-expr (CaseE e f)
  with evaluate-step-expr e
...  | stuck = stuck
...  | step{e' = e'} st
     with ValU? e | ValU? e'
...     | yes p | yes q = step (ξ-Case{U = p}{U' = q} st)
...     | no ¬p | yes q = stuck
...     | yes p | no ¬q = stuck
...     | no ¬p | no ¬q = stuck     
evaluate-step-expr (CaseE e f) | result RBlame = step Case-Blame
evaluate-step-expr (CaseE .UnitE f) | result (RValue VUnit) = stuck
evaluate-step-expr (CaseE .(Abs _) f) | result (RValue VFun) = stuck
evaluate-step-expr (CaseE .(ProdV _ _) f) | result (RValue (VProd v v₁)) = stuck
evaluate-step-expr (CaseE .(Cast _ _ Dyn) f) | result (RValue (VCast v x)) = stuck
evaluate-step-expr (CaseE .(Cast _ (Pi _ _) (Pi _ _)) f) | result (RValue (VCastFun v)) = stuck
evaluate-step-expr (CaseE{s = s} (LabI l) f) | result (RValue VLab)
  with l ∈? s
...  | yes ins = step (β-LabE ins)
...  | no ¬ins = stuck

evaluate-step-expr (Prod e e₁)
  with evaluate-step-expr e
...  | stuck = stuck
...  | step st = step (ξ-Prod st)
...  | result RBlame = step Prod-Blame
...  | result (RValue v) = step (β-Prod{v = v})

evaluate-step-expr (ProdV e e₁)
  with Val? e
...  | no ¬v = stuck
...  | yes v
     with evaluate-step-expr e₁
...     | stuck = stuck
...     | step st = step (ξ-ProdV{v = v} st)
...     | result RBlame = step (ProdV-Blame{v = v})
...     | result (RValue w) = result (RValue (VProd v w))

evaluate-step-expr (LetE e e₁)
  with evaluate-step-expr e
...  | stuck = stuck
...  | step st = step (ξ-LetE st)
...  | result RBlame = step (LetE-Blame)
...  | result (RValue v) = step (β-LetE v)

evaluate-step-expr (LetP e e₁)
  with evaluate-step-expr e
...  | stuck = stuck
...  | step st = step (ξ-LetP st)
...  | result RBlame = step (LetP-Blame)
...  | result (RValue VUnit) = stuck
...  | result (RValue VLab) = stuck
...  | result (RValue VFun) = stuck
...  | result (RValue (VCast v x)) = stuck
...  | result (RValue (VCastFun v)) = stuck
...  | result (RValue (VProd v v₁)) = step (β-LetP v v₁)

evaluate-step-expr (App e e₁)
  with evaluate-step-expr e
...  | stuck = stuck
...  | step st = step (ξ-App₁ st)
...  | result RBlame = step (App₁-Blame)
...  | result (RValue v)
     with evaluate-step-expr e₁
...     | stuck = stuck
...     | step st = step (ξ-App₂{v = v} st)
...     | result RBlame = step (App₂-Blame{v = v})
evaluate-step-expr (App .UnitE e₁) | result (RValue VUnit) | result (RValue w) = stuck
evaluate-step-expr (App .(LabI _) e₁) | result (RValue VLab) | result (RValue w) = stuck
evaluate-step-expr (App .(ProdV _ _) e₁) | result (RValue (VProd v v₁)) | result (RValue w) = stuck
evaluate-step-expr (App .(Cast _ _ Dyn) e₁) | result (RValue (VCast v x)) | result (RValue w) = stuck
evaluate-step-expr (App .(Abs _) e₁) | result (RValue VFun) | result (RValue w) = step (β-App w)
evaluate-step-expr (App .(Cast _ (Pi _ _) (Pi _ _)) e₁) | result (RValue (VCastFun v)) | result (RValue w) = step (Cast-Func{v = v}{w = w})

evaluate-step-expr (Cast e A B)
  with evaluate-step-expr e
...  | step st = step (ξ-Cast st)
...  | stuck = stuck
...  | result RBlame = step Cast-Blame
...  | result (RValue v)
     with evaluate-step-type A
...     | step st = step (Cast-Reduce-L{v = v} st)
...     | stuck = stuck
...     | result RBot = stuck   -- (?)
...     | result (RNf nfA)
        with evaluate-step-type B
...        | step st = step (Cast-Reduce-R{v = v} nfA st)
...        | stuck = stuck
...        | result RBot = stuck   -- (?)
...        | result (RNf nfB)
           with A ≡ᵀ? Dyn | B ≡ᵀ? Dyn
...           | yes eq | yes eq₁ rewrite eq | eq₁ = step (Cast-Dyn{v = v})
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | yes eq₁ rewrite eq₁
  with TyG? A
...  | yes tyga = result (RValue (VCast v tyga))
...  | no ¬tyga = step (Cast-Factor-L{v = v}{nfA = nfA} ¬eq)
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁
  with TyG? B
...  | no ¬tygb rewrite eq = step (Cast-Factor-R{v = v}{nfB = nfB} ¬eq₁)
evaluate-step-expr (Cast .UnitE Dyn B) | result (RValue VUnit) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck   -- (?) (also the following cases) matching undefined for *
evaluate-step-expr (Cast .(LabI _) Dyn B) | result (RValue VLab) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(Abs _) Dyn B) | result (RValue VFun) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(ProdV _ _) Dyn B) | result (RValue (VProd v v₁)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) Dyn B) | result (RValue (VCastFun v)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast (Cast e G Dyn) Dyn B) | result (RValue (VCast v tygg)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb
  with []⊢ tygg ≤ᵀ? tygb
...  | yes leq = step (Cast-Collapse{v = v}{tygG = tygg}{tygH = tygb} leq)
...  | no ¬leq = step (Cast-Collide{v = v}{tygG = tygg}{tygH = tygb} ¬leq)

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁
  with TyG? A | TyG? B
 
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB
  with []⊢ tygA ≤ᵀ? tygB
...  | yes leq = step (Cast-Sub{v = v}{tygG = tygA}{tygH = tygB} leq)
...  | no ¬leq
     with λ leq → (Cast-Fail{v = v}{tynfA = nfA}{tynfB = nfB}{neq = ¬eq , ¬eq₁} leq)
...     | w rewrite (TyG×TyNf⇒match-equiv{neq = ¬eq} tygA nfA) | (TyG×TyNf⇒match-equiv{neq = ¬eq₁} tygB nfB) = step (w ¬leq)

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB
  with ¬TyG×TyNf-in ¬tygB nfB
...  | Dyn = contradiction refl ¬eq₁
-- A = Pi
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x
  with v | tygA
evaluate-step-expr (Cast e UnitT (Pi A B)) | result (RValue v) | result (RNf NfUnit) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GG' GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Label s) (Pi A B)) | result (RValue v) | result (RNf NfLabel) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GG' GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma Dyn Dyn) (Pi A B)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GG' GSigma
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Single e' G) (Pi A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB}{notsingle = notsingl})) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSingle
 = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = tybB}{notsingle = notsingl}}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} ϱ)
 where ϱ : ¬ ([] ⊢ Single e' G ≤ᵀ Pi Dyn Dyn)
       ϱ (ASubSingle constr () x₁)
evaluate-step-expr (Cast e (Pi Dyn Dyn) (Pi A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GG' GPi = result (RValue (VCastFun v))
-- A = Sigma
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x
  with v | tygA
evaluate-step-expr (Cast e UnitT (Sigma A B)) | result (RValue v) | result (RNf NfUnit) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GG' GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Label s) (Sigma A B)) | result (RValue v) | result (RNf NfLabel) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GG' GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GG' GPi
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Single e' G) (Sigma A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB}{notsingle = notsingl})) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSingle
 = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = tybB}{notsingle = notsingl}}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} ϱ)
 where ϱ : ¬ ([] ⊢ Single e' G ≤ᵀ Sigma Dyn Dyn)
       ϱ (ASubSingle constr () x₁)
evaluate-step-expr (Cast .UnitE (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VUnit | GG' GSigma = stuck
evaluate-step-expr (Cast .(LabI _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VLab | GG' GSigma = stuck
evaluate-step-expr (Cast .(Abs _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VFun | GG' GSigma = stuck
evaluate-step-expr (Cast .(Cast _ _ Dyn) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VCast w x₁ | GG' GSigma = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VCastFun w | GG' GSigma = stuck
evaluate-step-expr (Cast .(ProdV _ _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VProd w w₁ | GG' GSigma
 = step (Cast-Pair{v = w}{w = w₁})

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB
  with ¬TyG×TyNf-in ¬tygA nfA
...  | Dyn = contradiction refl ¬eq
-- A = Pi
evaluate-step-expr (Cast e (Pi A B) C) | result (RValue v) | result (RNf NfPi) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x
  with tygB
evaluate-step-expr (Cast e (Pi A B) UnitT) | result (RValue v) | result (RNf NfPi) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GG' GUnit
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfUnit}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Label s)) | result (RValue v) | result (RNf NfPi) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GG' GLabel
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfLabel}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Sigma Dyn Dyn)) | result (RValue v) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GG' GSigma
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Single e' G)) | result (RValue v) | result (RNf NfPi) | result (RNf (NfSingle{V = V}{tybB = tybB}{notsingle = notsingl})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSingle
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = tybB}{notsingle = notsingl}}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Pi Dyn Dyn)) | result (RValue v) | result (RNf NfPi) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GG' GPi
 = result (RValue (VCastFun v))
-- A = Sigma
evaluate-step-expr (Cast e (Sigma A B) C) | result (RValue v) | result (RNf NfSigma) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x
  with tygB
evaluate-step-expr (Cast e (Sigma A B) UnitT) | result (RValue v) | result (RNf NfSigma) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GUnit
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfUnit}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Label s)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GLabel
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfLabel}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Pi Dyn Dyn)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GPi
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Single e' G)) | result (RValue v) | result (RNf NfSigma) | result (RNf (NfSingle{V = V}{tybB = tybB}{notsingle = notsingl})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSingle
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = tybB}{notsingle = notsingl}}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast .UnitE (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VUnit) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = stuck
evaluate-step-expr (Cast .(LabI _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VLab) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = stuck
evaluate-step-expr (Cast .(Abs _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VFun) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = stuck
evaluate-step-expr (Cast .(Cast _ _ Dyn) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VCast v x₁)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VCastFun v)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = stuck
evaluate-step-expr (Cast .(ProdV _ _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VProd v v₁)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GG' GSigma = step (Cast-Pair{v = v}{w = v₁})

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB
  with ¬TyG×TyNf-in ¬tygA nfA | ¬TyG×TyNf-in ¬tygB nfB
...  | Dyn | Dyn = contradiction refl ¬eq
...  | Dyn | Pi x = contradiction refl ¬eq
...  | Pi x | Dyn = contradiction refl ¬eq₁
...  | Dyn | Sigma x = contradiction refl ¬eq
...  | Sigma x | Dyn = contradiction refl ¬eq₁
evaluate-step-expr (Cast e (Pi A B) (Sigma A' B')) | result (RValue v) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Pi x | Sigma x₁
  = step (Cast-Fail {v = v} {tynfA = NfPi} {tynfB = NfSigma}
            {neq = ¬eq , ¬eq₁} (λ ()))
evaluate-step-expr (Cast e (Sigma A B) (Pi A' B')) | result (RValue v) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Pi x₁
  = step (Cast-Fail {v = v} {tynfA = NfSigma} {tynfB = NfPi}
            {neq = ¬eq , ¬eq₁} (λ ()))
evaluate-step-expr (Cast e (Pi A B) (Pi A' B')) | result (RValue v) | result (RNf NfPi) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Pi x | Pi x₁ = result (RValue (VCastFun v))
evaluate-step-expr (Cast .UnitE (Sigma A B) (Sigma A' B')) | result (RValue VUnit) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = stuck
evaluate-step-expr (Cast .(LabI _) (Sigma A B) (Sigma A' B')) | result (RValue VLab) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = stuck
evaluate-step-expr (Cast .(Abs _) (Sigma A B) (Sigma A' B')) | result (RValue VFun) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = stuck
evaluate-step-expr (Cast .(Cast _ _ Dyn) (Sigma A B) (Sigma A' B')) | result (RValue (VCast v x₂)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) (Sigma A B) (Sigma A' B')) | result (RValue (VCastFun v)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = stuck
evaluate-step-expr (Cast .(ProdV _ _) (Sigma A B) (Sigma A' B')) | result (RValue (VProd v v₁)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | no ¬tygB | Sigma x | Sigma x₁ = step (Cast-Pair{v = v}{w = v₁})

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data finished {n : ℕ} (e : Exp {n}) : Set where
  result : Result e → finished e
  stuck : finished e
  out-of-gas : finished e

evaluate-full : {n : ℕ} → Gas → Exp {n} → ∃[ N ]( finished{n = n} N )
evaluate-full (gas zero) e = e , out-of-gas
evaluate-full (gas (ℕ.suc amount)) e
  with evaluate-step-expr e
...  | stuck = e , stuck
...  | result x = e , (result x)
...  | step{e' = e'} x = evaluate-full (gas amount) e'

data Steps {n : ℕ} : Exp {n} → Set where
  steps : {e e' : Exp {n}} → e ⇛ e' → finished e' → Steps e

evaluate-full-steps : {n : ℕ} → Gas → (e : Exp {n}) → Steps e
evaluate-full-steps (gas zero) e = steps (e ∎) out-of-gas
evaluate-full-steps (gas (ℕ.suc amount)) e
  with evaluate-step-expr e
...  | stuck = steps (e ∎) (stuck)
...  | result x = steps (e ∎) (result x)
...  | step{e' = e'} e⇨e'
     with evaluate-full-steps (gas amount) e'
...     | steps e'⇛e'' fin = steps (e ⇨⟨ e⇨e' ⟩ e'⇛e'') fin

------------------------------------------------------------------------
-- Cast function, limited to 1000 evaluations

cast (Single e A') A B
  with evaluate-full (gas 1000) (Cast e A B)
...  | fst , result RBlame = Bot
...  | fst , result (RValue v) = Single fst B 
...  | fst , stuck = Bot
...  | fst , out-of-gas = Bot

cast UnitT A B = B
cast (Label x) A B = B
cast (Pi A' A'') A B = B
cast (Sigma A' A'') A B = B
cast (CaseT x f) A B = B
cast Bot A B = B
cast Dyn A B = B

-- Sanity check
s : Subset 2
s = inside ∷ (inside ∷ [])

f₃-branches : {n : ℕ} (l : Fin 2) → l ∈ s → Exp {n}
f₃-branches zero ins = Var 0
f₃-branches (Fin.suc zero) ins = UnitE

f₃ : Exp {2}
f₃ = Abs (Abs ((CaseE{s = s} (Var 1) f₃-branches)))

f₃-0 : (evaluate-full (gas 100) (App (App f₃ (LabI zero)) (LabI zero))) ≡ (LabI zero , result (RValue (VLab{x = zero})))
f₃-0 = refl

f₃-1 : (evaluate-full (gas 100) (App (App f₃ (LabI (Fin.suc zero))) (LabI zero))) ≡ (UnitE , result (RValue VUnit))
f₃-1 = refl

blame : (evaluate-full (gas 100) (Cast (LabI zero) UnitT (Label (inside ∷ [])))) ≡ (Blame , result RBlame)
blame = refl

_ : (evaluate-full (gas 100) (CaseE{s = (inside ∷ (inside ∷ []))} (Cast (Cast (LabI zero) (Label (inside ∷ (outside ∷ []))) Dyn) Dyn (Label (inside ∷ (inside ∷ [])))) (λ l → λ ins → UnitE))) ≡ (UnitE , (result (RValue VUnit)))
_ = refl
