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
  SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {ok : Γ ⊢ A} → ⊢ Γ ok → Γ ⊢ e ◁ A → TyB A → Γ ⊢ Single V A
  CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ◁ Label L → Γ ⊢ CaseT U f

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
  ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ≤ᵀ B → TyB B → notSingle B → Γ ⊢ Single V A ≤ᵀ B
  ASubSingleSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e e' : Exp {n}} {V : Val e} {W : Val e'} → e ≡ e' → Γ ⊢ A ≤ᵀ B → Γ ⊢ Single V A ≤ᵀ Single W B
  ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
           → Γ ⊢ A' ≤ᵀ A
           → ⟨ A' , Γ ⟩ ⊢ B ≤ᵀ B'
           → Γ ⊢ Pi A B ≤ᵀ Pi A' B'
  ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
              → Γ ⊢ A ≤ᵀ A'
              → ⟨ A , Γ ⟩ ⊢ B ≤ᵀ B'
              → Γ ⊢ Sigma A B ≤ᵀ Sigma A' B'
            
  ASubCaseLL : {Γ : TEnv {n}} {B D : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (VLab{x = l}) D
               → (ins : l ∈ L)
               → Γ ⊢ (f l ins) ≤ᵀ B
               → Γ ⊢ CaseT U f ≤ᵀ B           
  ASubCaseLR : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (VLab{x = l}) D
               → (ins : l ∈ L)
               → Γ ⊢ A ≤ᵀ (f l ins)
               → Γ ⊢ A ≤ᵀ CaseT U f           
  ASubCaseXL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) (Label ⁅ l ⁆) ≤ᵀ D)
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) D , Γ ⟩) ⊢ (f l (sub i)) ≤ᵀ B)
               → Θ ⊢ CaseT (UVar{x = length Γ'}) f ≤ᵀ B
  ASubCaseXR : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) (Label ⁅ l ⁆) ≤ᵀ D)             
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) D , Γ ⟩) ⊢ A ≤ᵀ (f l (sub i)))
               → Θ ⊢ A ≤ᵀ CaseT (UVar{x = length Γ'}) f
  ASubCaseBL : {Γ : TEnv {n}} {B : Ty} {e : Exp {n}} {U : ValU e} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Bot
               → Γ ⊢ CaseT U f ≤ᵀ B
  ASubCaseCL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
                → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) f ≤ᵀ B
  ASubCaseCR : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ B ≤ᵀ (f l i))
                → Θ ⊢ B ≤ᵀ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) f

data _⊢_▷_ {n} where
  BlameA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Blame ▷ Bot
  VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
  CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} {ok : Γ ⊢ A} {ok' : Γ ⊢ B}
           → Γ ⊢ M ▷ A' → B' ≡ (cast A' A B) → Γ ⊢ Cast M A B ▷ B'
  UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ▷ Single VUnit UnitT
  LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ▷ Single (VLab{x = l}) (Label ⁅ l ⁆)
  LabAEl : {Γ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {l : Fin n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
           → Γ ⊢ e ▷ Single (VLab{x = l}) D
           → (ins : l ∈ L)
           → Γ ⊢ (f l ins) ▷ B
           → Γ ⊢ CaseE U f ▷ B
  LabAEl-Bot : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
               → Γ ⊢ e ▷ Bot
               → Γ ⊢ CaseE U f ▷ Bot
  -- unification has problems with arbitrary functions, hence θ
  -- see https://lists.chalmers.se/pipermail/agda/2020/012293.html
  LabAEx : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L' → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
           → Γ ⊢ D ≤ᵀ Label L
           → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) (Label ⁅ l ⁆) ≤ᵀ D)
           → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ (Single (VLab{x = l})) D , Γ ⟩) ⊢ (f l (sub i)) ▷ (f-t l i))
           → Θ ⊢ CaseE (UVar{x = length Γ'}) f ▷ CaseT (UVar{x = length Γ'}) f-t
  LabAExDyn : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → notSingle D
            → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l}) (Label L)) (Label L) D)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
            → Θ ⊢ CaseE (UVarCast{x = length Γ'}{A = D}{Label L}) f ▷ CaseT (UVarCast{x = length Γ'}{A = D}{Label L}) f-t
  PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ▷ B → Γ ⊢ Abs M ▷ Pi A B
  PiAE-V : {Γ : TEnv {n}} {A B D F : Ty {n}} {M N : Exp {n}} {V : Val N} {eq : F ≡ [ 0 ↦ V ]ᵀ B}
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
           → Γ ⊢ ProdV V N ▷ Sigma A B
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
            → Γ ⊢ e ▷ Single (VLab{x = l}) D
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Pi A B
            → Γ ⊢ CaseT U f ⇓ Pi A B        
  AUCaseL-S : {Γ : TEnv {n}} {A B D : Ty {n}} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (VLab{x = l}) D
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Sigma A B
            → Γ ⊢ CaseT U f ⇓ Sigma A B            
  AUCaseX-P : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) (Label ⁅ l ⁆) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) D , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Pi (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (UVar{x = length Γ'}) fᴬ ⇓ Pi (CaseT (UVar{x = length Γ'}) fᴮ) (CaseT (UVar{x = ℕ.suc (length Γ')}) fᶜ)          
  AUCaseX-S : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) (Label ⁅ l ⁆) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) D , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Sigma (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (UVar{x = length Γ'}) fᴬ ⇓ Sigma (CaseT (UVar{x = length Γ'}) fᴮ) (CaseT (UVar{x = ℕ.suc (length Γ')}) fᶜ)
  AUCaseXDyn-P : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L : Subset n} {fᴬ fᴮ fᶜ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Pi (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴬ ⇓ Pi (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴮ) (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᶜ)            
  AUCaseXDyn-S : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L : Subset n} {fᴬ fᴮ fᶜ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Sigma (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴬ ⇓ Sigma (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴮ) (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᶜ)            

------------------------------------------------------------------------
-- Type normal form, type matching, properties

data TyNf {n} : Ty {n} → Set where
  NfDyn : TyNf Dyn
  NfUnit : TyNf UnitT
  NfLabel : {s : Subset n} → TyNf (Label s)
  NfPi : {A B : Ty {n}} → TyNf (Pi A B)
  NfSigma : {A B : Ty {n}} → TyNf (Sigma A B)
  NfSingle : {B : Ty {n}} {e : Exp {n}} {V : Val e} {tybB : TyB B} {notsingle : notSingle B} → TyNf (Single V B)

_match : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → TyNf A → Σ (Ty {n}) (TyG)
_match {neq = neq} NfDyn = contradiction refl neq
NfUnit match = UnitT , GG' GUnit
NfLabel {s = s} match = Label s , GG' GLabel
NfPi match = (Pi Dyn Dyn) , (GG' GPi)
NfSigma match = Sigma Dyn Dyn , GG' GSigma
NfSingle{B = B}{e}{V}{tybB}{notsingl} match = Single V B , (GSingle{tygG = notsingle×TyB⊂TyG' notsingl tybB})

data ¬TyG×TyNf {n : ℕ} : Ty {n} → Set where
  Dyn : ¬TyG×TyNf Dyn
  Pi : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Pi A B)
  Sigma : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Sigma A B)

¬TyG×TyNf-in : {n : ℕ} {A : Ty {n}} → ¬ (TyG A) → TyNf A → ¬TyG×TyNf A
¬TyG×TyNf-in {n} {.Dyn} ntyg NfDyn = Dyn
¬TyG×TyNf-in {n} {.UnitT} ntyg NfUnit = contradiction (GG' GUnit) ntyg
¬TyG×TyNf-in {n} {.(Label _)} ntyg NfLabel = contradiction (GG' GLabel) ntyg
¬TyG×TyNf-in {n} {.(Single _ _)} ntyg (NfSingle{tybB = tybB}{notsingle = notsingl}) = contradiction (GSingle{tygG = notsingle×TyB⊂TyG' notsingl tybB}) ntyg
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

------------------------------------------------------------------------
-- Algorith for subtyping, limited to ground types

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

[]⊢_≤ᵀ?_ {n} {(Single V G)} {(Single W H)} (GSingle{e = e}{tygG = tygG}) (GSingle{e = e'}{tygG = tygH})
  with e ≡ᵉ? e' | []⊢_≤ᵀ?'_ tygG tygH
...  | yes p | yes q = yes (ASubSingleSingle p q)
...  | no ¬p | _ = no ϱ
     where ϱ : ¬ ([] ⊢ (Single V G) ≤ᵀ (Single W H))
           ϱ (ASubSingle x x₁ x₂) = contradiction x₂ notnotsingle-single
           ϱ (ASubSingleSingle x leq) = ¬p x
...  | _ | no ¬p = no ϱ
     where ϱ : ¬ ([] ⊢ (Single V G) ≤ᵀ (Single W H))
           ϱ (ASubSingle x x₁ x₂) = contradiction x₂ notnotsingle-single
           ϱ (ASubSingleSingle x leq) = ¬p leq
[]⊢_≤ᵀ?_ {n} {(Single V G)} {H} (GSingle{tygG = tygG}) (GG' tygH)
  with []⊢_≤ᵀ?'_ tygG tygH | TyB? H
...  | yes p | yes q = yes (ASubSingle p q (TyG'⇒notSingle tygH))
...  | no ¬p | _ = no ϱ
     where ϱ : ¬ ([] ⊢ Single V G ≤ᵀ H)
           ϱ (ASubSingle leq x x₁) = ¬p leq
...  | _ | no ¬q = no ϱ
     where ϱ : ¬ ([] ⊢ Single V G ≤ᵀ H)
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
-- Big-step semantics

data Result {n : ℕ} : Set where
  RValue : {e : Exp {n}} → Val {n} e → Result {n}
  RBlame : Result {n}
  RStuck : Result {n}

data ResultType {n : ℕ} : Set where
  RNf : {A : Ty {n}} → TyNf {n} A → ResultType {n}
  RBot : ResultType {n}
  RStuck : ResultType {n}

Env : {ℕ} → Set
Env {n} = List (Exp {n})

_∶_⇓ : {n : ℕ} {Γ : Env {n}} → All Val Γ → Exp {n} → Result {n}
_∶_⇓ᵀ : {n : ℕ} {Γ : Env {n}} → All Val Γ → (A : Ty {n}) → ResultType {n}

access : {n : ℕ} {Γ : Env {n}} → (m : ℕ) → All Val Γ → Result {n}
access {n} {[]} m [] = RStuck
access {n} {x ∷ Γ} zero (px ∷ px₁) = RValue px
access {n} {x ∷ Γ} (ℕ.suc m) (px ∷ px₁) = access m px₁

-- Evaluate expression
Γ ∶ Var x ⇓ = access x Γ
Γ ∶ UnitE ⇓ = RValue VUnit
Γ ∶ Abs e ⇓ = RValue (VFun{N = e})
Γ ∶ LabI x ⇓ = RValue (VLab{x = x})
Γ ∶ Blame ⇓ = RBlame

{-
_∶_⇓{n = n} Γ (App e e₁)
  with Γ ∶ e ⇓ | Γ ∶ e₁ ⇓
... | RBlame | _ = RBlame
... | _ | RBlame = RBlame
... | RStuck | _ = RStuck
... | _ | RStuck = RStuck
... | RValue{e = vₑ} v | RValue{e = wₑ} w
    with v
...    | VUnit = RStuck
...    | VLab = RStuck
...    | VProd x x₁ = RStuck
...    | VCast x x₁ = RStuck
...    | VCastFun{e = xₑ}{A = A}{A' = A'}{B = B}{B' = B'} x  =  Γ ∶ LetE (Cast wₑ A' A) (Cast (App xₑ (Var 0)) B ([ 0 ↦ w ]ᵀ B')) ⇓ -- Γ ∶ LetE (Cast wₑ A' A) (Cast (App vₑ (Var 0)) B ([ 0 ↦ w ]ᵀ B')) ⇓
_∶_⇓{Γ = Γ} v-Γ (App e e₁) | RValue{e = Abs N} v | RValue w | VFun = {!rec w N!} -- (w ∷ v-Γ) ∶ N ⇓
-}
_∶_⇓{n = n} Γ (App (Abs e) e₁)
  with Γ ∶ e₁ ⇓
...  | RStuck = RStuck  
...  | RBlame = RBlame
...  | RValue v = (v ∷ Γ) ∶ e ⇓  
_∶_⇓{n = n} Γ (App (Cast e A B) e₁)
  with Γ ∶ e₁ ⇓ | Γ ∶ A ⇓ᵀ | Γ ∶ B ⇓ᵀ
...  | RStuck | _ | _ = RStuck  
...  | RBlame | _ | _ = RBlame
...  | _ | RStuck | _ = RStuck
...  | _ | _ | RStuck = RStuck
...  | _ | RBot | _ = RBlame
...  | _ | _ | RBot = RBlame
...  | RValue{e = wₑ} w | RNf (NfPi{A = A₁}{B = B₁}) | RNf (NfPi{A = A₁'}{B = B₁'}) = Γ ∶ LetE (Cast wₑ A₁' A₁) (Cast (App e (Var 0)) B₁ ([ 0 ↦ w ]ᵀ B₁')) ⇓ 
...  | RValue v | _ | _ = RStuck



Γ ∶ CaseE{s = s}{e = e} x f ⇓
  with Γ ∶ e ⇓
...  | RStuck = RStuck  
...  | RBlame = RBlame
...  | RValue v
     with v
...     | VUnit = RStuck
...     | VFun = RStuck
...     | VProd w w₁ = RStuck
...     | VCast y x₁ = RStuck
...     | VCastFun z = RStuck
...     | VLab {x = l}
        with l ∈? s
...        | yes ins = Γ ∶ (f l ins) ⇓
...        | no ¬ins = RStuck

_∶_⇓{n = n}{Γ = Γ} v-Γ (Prod e e₁)
  with v-Γ ∶ e ⇓ | λ vₑ → (λ v → _∶_⇓{n = n}{Γ = vₑ ∷ Γ} (v ∷ v-Γ) e₁)
...  | RStuck | rec = RStuck
...  | RBlame | rec = RBlame
...  | RValue{e = vₑ} v | rec
     with rec vₑ v
...     | RBlame = RBlame
...     | RStuck = RStuck
...     | RValue w = RValue (VProd v w)

Γ ∶ ProdV x e ⇓
  with Γ ∶ e ⇓
...  | RStuck = RStuck
...  | RBlame = RBlame
...  | RValue v = RValue (VProd x v)

_∶_⇓{n = n}{Γ = Γ} v-Γ (LetP e e₁)
  with v-Γ ∶ e ⇓ | λ wₑ' wₑ → (λ w' w → _∶_⇓{n = n}{Γ = wₑ' ∷ (wₑ ∷ Γ)} (w' ∷ (w ∷ v-Γ)) e₁)
...  | RStuck | rec = RStuck
...  | RBlame | rec = RBlame
...  | RValue v | rec
     with v
...     | VUnit = RStuck
...     | VLab = RStuck
...     | VFun = RStuck
...     | VCast w x = RStuck
...     | VCastFun w = RStuck
...     | VProd{e = wₑ}{e' = wₑ'} w w' = rec wₑ' wₑ w' w

_∶_⇓{Γ = Γ} v-Γ (LetE e e₁)
  with v-Γ ∶ e ⇓
...  | RStuck = RStuck
...  | RBlame = RBlame
...  | RValue{e = vₑ} v = _∶_⇓ {Γ = vₑ ∷ Γ} (v ∷ v-Γ) (e₁)

Γ ∶ Cast e A B ⇓
  with Γ ∶ e ⇓ | Γ ∶ A ⇓ᵀ | Γ ∶ B ⇓ᵀ
...  | RBlame | _ | _ = RBlame  
...  | _ | RBot | _ = RBlame
...  | _ | _ | RBot = RBlame
...  | RStuck | _ | _ = RStuck
...  | _ | RStuck | _ = RStuck
...  | _ | _ | RStuck = RStuck
...  | RValue v | RNf nfA | RNf nfB = {!!} -- cast-eval v nfA nfB

{-
-- Evaluate (V : nA ⇒ nB)
cast-eval : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → Val e → TyNf A → TyNf B → Result {n}
cast-eval {n} {e} {A} {B} V nfA nfB
  with TyG? A | TyG? B
...  | yes tygA | yes tygB
     with []⊢ tygA ≤ᵀ? tygB
...     | yes leq = RValue V  -- Cast-Sub
...     | no ¬leq = RBlame    -- Cast-Fail

cast-eval {n} {e} {A} {B} V nfA nfB | yes tygA | no ¬tygB
  with B ≡ᵀ? Dyn
...  | yes p = RValue (VCast V tygA)  -- Already Value
...  | no ¬p
     with ¬TyG×TyNf-in ¬tygB nfB
...     | Dyn = contradiction refl ¬p
cast-eval {n} {e} {A} {Pi B₁ B₂} V nfA nfB | yes tygA | no ¬tygB | no ¬p | Pi x
   with tygA
...   | GSingle = RBlame  -- Cast-Fail, Pi not Base Type
...   | GG' GUnit = RBlame  -- Cast-Fail, ¬ (Unit ≤ Pi)
...   | GG' GLabel = RBlame  -- Cast-Fail, ¬ (Label ≤ Pi)
...   | GG' GPi = RValue (VCastFun{A = Dyn}{A' = B₁}{B = Dyn}{B' = B₂} V) -- Tagged function value
...   | GG' GSigma = RBlame  -- Cast-Fail, ¬ (Sigma ≤ Pi)
cast-eval {n} {e} {A} {Sigma B₁ B₂} V nfA nfB | yes tygA | no ¬tygB | no ¬p | Sigma x
  with tygA
...  | GSingle = RBlame  -- Cast-Fail, Sigma not Base Type
...  | GG' GUnit = RBlame  -- Cast-Fail, ¬ (Unit ≤ Pi)
...  | GG' GLabel = RBlame  -- Cast-Fail, ¬ (Label ≤ Pi)
...  | GG' GPi = RBlame  -- Cast-Fail, ¬ (Pi ≤ Sigma)
...  | GG' GSigma
     with V
...     | VUnit = RStuck  -- No reduction for () : Sigma ⇒ Sigma
...     | VLab = RStuck  -- No reduction for () : Sigma ⇒ Sigma
...     | VFun = RStuck  -- No reduction for () : Sigma ⇒ Sigma
...     | VCast y z = RStuck  -- No reduction for (V : G ⇒ *) : Sigma ⇒ Sigma
...     | VCastFun y = RStuck  -- No reduction for (V : Pi ⇒ Pi) : Sigma ⇒ Sigma
...     | VProd{e = yₑ}{e' = zₑ} y z = _∶_⇓ [] (Prod (Cast yₑ Dyn B₁) (Cast zₑ Dyn B₂))

cast-eval {n} {e} {A} {B} V nfA nfB | no ¬tygA | yes tygB
  with A ≡ᵀ? Dyn
...  | yes p
     with V
...     | VUnit = RBlame
...     | VLab = RBlame
...     | VFun = RBlame
...     | VProd x x₁ = RBlame
...     | VCastFun x = RBlame
...     | VCast x tygG
        with []⊢ tygG ≤ᵀ? tygB
...        | yes leq = RValue x  -- Cast-Collapse
...        | no ¬leq = RBlame    -- Cast-Collide
cast-eval {n} {e} {A} {B} V nfA nfB | no ¬tygA | yes tygB | no ¬p
  with _match {neq = ¬p} nfA
...  | C , tygC
     with []⊢ tygC ≤ᵀ? tygB
...        | yes leq = RValue V  -- Cast-Sub (?)
...        | no ¬leq = RBlame    -- Cast-Fail
cast-eval {n} {e} {A} {B} V nfA nfB | no ¬tygA | no ¬tygB
  with B ≡ᵀ? Dyn
...  | yes p
     with A ≡ᵀ? Dyn
...     | yes q = RValue V   -- Cast-Dyn-Dyn
...     | no ¬q
        with ¬TyG×TyNf-in ¬tygA nfA
...        | Dyn = contradiction refl ¬q
cast-eval {n} {e} {Pi A₁ A₂} {B} V nfA nfB | no ¬tygA | no ¬tygB | yes p | no ¬q | Pi x = RValue (VCast (VCastFun{A = A₁}{A' = Dyn}{B = A₂}{B' = Dyn} V) (GG' GPi))   -- Cast-Factor-Left
cast-eval {n} {e} {Sigma A₁ A₂} {B} V nfA nfB | no ¬tygA | no ¬tygB | yes p | no ¬q | Sigma x
  with V
...  | VUnit = RStuck -- Cast-Factor-Left, then nothing applicable
...  | VLab = RStuck -- Cast-Factor-Left, then nothing applicable
...  | VFun = RStuck -- Cast-Factor-Left, then nothing applicable
...  | VCast W x₁ = RStuck -- Cast-Factor-Left, then nothing applicable
...  | VCastFun W = RStuck -- Cast-Factor-Left, then nothing applicable
...  | VProd W W₁ = {!!}
cast-eval {n} {e} {A} {B} V nfA nfB | no ¬tygA | no ¬tygB | no ¬p
  with A ≡ᵀ? Dyn
...  | yes q = {!!}
...  | no ¬q = {!!}
-}


{-
Γ ∶ (UVar{x = x}) ⇓ = access x Γ
Γ ∶ UValUnit ⇓ = RValue VUnit
Γ ∶ UValLab {x = x} ⇓ = RValue (VLab{x = x})
Γ ∶ UValFun {N = N} ⇓ = RValue (VFun{N = N})
Γ ∶ UValProd v x ⇓ = RValue (VProd v x)
Γ ∶ UVarCast {x = x} {A = A} {B = B} ⇓
  with access x Γ
...  | RBlame = RBlame
...  | RStuck = RStuck
...  | RValue v
     with Γ ∶ A ⇓ᵀ | Γ ∶ B ⇓ᵀ
...     | RBot | _ = RBlame
...     | _ | RBot = RBlame
...     | RStuck | _ = RStuck
...     | _ | RStuck = RStuck
...     | RNf nfA | RNf nfB = cast-eval v nfA nfB     
Γ ∶ UValCast {A = A} {B = B} v ⇓
  with Γ ∶ A ⇓ᵀ | Γ ∶ B ⇓ᵀ
...  | RBot | _ = RBlame
...  | _ | RBot = RBlame
...  | RStuck | _ = RStuck
...  | _ | RStuck = RStuck
...  | RNf nfA | RNf nfB = cast-eval v nfA nfB
Γ ∶ UBlame ⇓ = RBlame
-}

-- Type reduction
Γ ∶ UnitT ⇓ᵀ = RNf NfUnit
Γ ∶ Single {e = e} x A ⇓ᵀ
  with TyB? A
...  | no ¬p = RStuck
...  | yes BSingleLab = RStuck
...  | yes BSingleUnit = RStuck
...  | yes BUnit = RNf (NfSingle{B = A}{e = e}{V = x}{tybB = BUnit}{notsingle = notsingle λ e B W → λ ()})
...  | yes BLabel = RNf (NfSingle{B = A}{e = e}{V = x}{tybB = BLabel}{notsingle = notsingle λ e B W → λ ()})
Γ ∶ Label x ⇓ᵀ = RNf (NfLabel{s = x})
Γ ∶ Pi A A₁ ⇓ᵀ = RNf (NfPi{A = A}{B = A₁})
Γ ∶ Sigma A A₁ ⇓ᵀ = RNf (NfSigma{A = A}{B = A₁})
Γ ∶ Bot ⇓ᵀ = RBot
Γ ∶ Dyn ⇓ᵀ = RNf NfDyn

Γ ∶ CaseT{s = s}{e = e} x f ⇓ᵀ = {!!}
{-
  with Γ ∶ e ⇓ | λ l ins → Γ ∶ (f l ins) ⇓ᵀ
...  | RBlame | rec = RBot
...  | RStuck | rec = RStuck
...  | RValue VUnit | rec = RStuck
...  | RValue VFun | rec = RStuck
...  | RValue (VProd x₁ x₂) | rec = RStuck
...  | RValue (VCast x₁ x₂) | rec = RStuck
...  | RValue (VCastFun x₁) | rec = RStuck
...  | RValue (VLab{x = y}) | rec
     with y ∈? s
...     | yes ins = rec y ins
...     | no ¬ins = RStuck
-}

-- Cast function
cast (Single{e = e} x A') A B
  with [] ∶ e ⇓
...  | RValue x₁ = Single x₁ B
...  | RBlame = Bot
...  | RStuck = B  -- (?)

cast UnitT A B = B
cast (Label x) A B = B
cast (Pi A' A'') A B = B
cast (Sigma A' A'') A B = B
cast (CaseT x f) A B = B
cast Bot A B = B
cast Dyn A B = B

------------------------------------------------------------------------
-- Code graveyard
{-
[]⊢_▷?_ : {n : ℕ} {e : Exp {n}} {B : Ty {n}} → Val e → TyB B → Dec ([] ⊢ e ▷ B)
[]⊢_◁?_ : {n : ℕ} {e : Exp {n}} {B : Ty {n}} → Val e → TyB B → Dec ([] ⊢ e ◁ B)

[]⊢_▷?_ {n} {.UnitE} {.UnitT} VUnit BUnit = no λ ()
[]⊢_▷?_ {n} {.UnitE} {.(Label _)} VUnit BLabel = no λ ()
[]⊢_▷?_ {n} {.UnitE} {.(Single VLab (Label _))} VUnit BSingleLab = no λ ()
[]⊢_▷?_ {n} {.UnitE} {.(Single VUnit UnitT)} VUnit BSingleUnit = yes (UnitAI empty)
[]⊢_▷?_ {n} {.(LabI _)} {.UnitT} VLab BUnit = no λ ()
[]⊢_▷?_ {n} {.(LabI _)} {.(Label _)} VLab BLabel = no λ ()
[]⊢_▷?_ {n} {.(LabI _)} {.(Single VLab (Label _))} VLab BSingleLab = yes {!LabAI!}
[]⊢_▷?_ {n} {.(LabI _)} {.(Single VUnit UnitT)} VLab BSingleUnit = no λ ()
[]⊢_▷?_ {n} {.(Abs _)} {.UnitT} VFun BUnit = no λ ()
[]⊢_▷?_ {n} {.(Abs _)} {.(Label _)} VFun BLabel = no λ ()
[]⊢_▷?_ {n} {.(Abs _)} {.(Single VLab (Label _))} VFun BSingleLab = no λ ()
[]⊢_▷?_ {n} {.(Abs _)} {.(Single VUnit UnitT)} VFun BSingleUnit = no λ ()
[]⊢_▷?_ {n} {.(ProdV V _)} {.UnitT} (VProd V V₁) BUnit = no λ ()
[]⊢_▷?_ {n} {.(ProdV V _)} {.(Label _)} (VProd V V₁) BLabel = no λ ()
[]⊢_▷?_ {n} {.(ProdV V _)} {.(Single VLab (Label _))} (VProd V V₁) BSingleLab = no λ ()
[]⊢_▷?_ {n} {.(ProdV V _)} {.(Single VUnit UnitT)} (VProd V V₁) BSingleUnit = no λ ()

[]⊢_▷?_ {n} {.(Cast _ _ Dyn)} {.UnitT} (VCast V x) BUnit = {!!}
[]⊢_▷?_ {n} {.(Cast _ _ Dyn)} {.(Label _)} (VCast V x) BLabel = {!no λ ()!}
[]⊢_▷?_ {n} {.(Cast _ _ Dyn)} {.(Single VLab (Label _))} (VCast V x) BSingleLab = {!!}
[]⊢_▷?_ {n} {.(Cast _ _ Dyn)} {.(Single VUnit UnitT)} (VCast V x) BSingleUnit = {!!}
[]⊢_▷?_ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.UnitT} (VCastFun V) BUnit = {!!}
[]⊢_▷?_ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(Label _)} (VCastFun V) BLabel = {!!}
[]⊢_▷?_ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(Single VLab (Label _))} (VCastFun V) BSingleLab = {!!}
[]⊢_▷?_ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {.(Single VUnit UnitT)} (VCastFun V) BSingleUnit = {!!}

[]⊢_◁?_ {n} {.UnitE} {.UnitT} VUnit BUnit = yes UnitChkA
[]⊢_◁?_ {n} {.UnitE} {.(Label _)} VUnit BLabel = no {!!}
[]⊢_◁?_ {n} {.UnitE} {.(Single VLab (Label _))} VUnit BSingleLab = {!!}
[]⊢_◁?_ {n} {.UnitE} {.(Single VUnit UnitT)} VUnit BSingleUnit = {!!}
[]⊢_◁?_ {n} {.(LabI _)} {.UnitT} VLab BUnit = {!!}
[]⊢_◁?_ {n} {.(LabI _)} {.(Label _)} VLab BLabel = {!!}
[]⊢_◁?_ {n} {.(LabI _)} {.(Single VLab (Label _))} VLab BSingleLab = {!!}
[]⊢_◁?_ {n} {.(LabI _)} {.(Single VUnit UnitT)} VLab BSingleUnit = {!!}
[]⊢_◁?_ {n} {.(Abs _)} {B} VFun tybB = {!!}
[]⊢_◁?_ {n} {.(ProdV V _)} {B} (VProd V V₁) tybB = {!!}
[]⊢_◁?_ {n} {.(Cast _ _ Dyn)} {B} (VCast V x) tybB = {!!}
[]⊢_◁?_ {n} {.(Cast _ (Pi _ _) (Pi _ _))} {B} (VCastFun V) tybB = {!!}
-}
