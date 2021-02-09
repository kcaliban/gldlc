------------------------------------------------------------------------
-- Typing, small and big step semantics
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module Typing-Semantics where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Fin hiding (cast)
open import Data.Fin.Properties
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
data ⊢_∣_ok {n : ℕ} : TEnv {n} → TEnv {n} → Set
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
-- Conversion
data _⊢_≡ᵀ_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
-- Consistency
data _∣_⊢_~_ {n : ℕ} : TEnv {n} → TEnv {n} → Ty {n} → Ty {n} → Set
-- precise cast function
cast : {n : ℕ} → Ty {n} → Ty {n} → Ty {n} → Maybe (Ty {n})

-- Implementations
data ⊢_ok {n} where
  empty : ⊢ [] ok
  entry : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ A → ⊢ ⟨ A , Γ ⟩ ok

data ⊢_∣_ok {n} where
  empty : ⊢ [] ∣ [] ok
  entry : {Γ Γ' : TEnv {n}} {A A' : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ A' → Γ ⊢ A → Γ' ⊢ A' → ⊢ ⟨ A , Γ ⟩ ∣ ⟨ A' , Γ' ⟩ ok

data _⊢_ {n} where
  DynF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Dyn
  UnitF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitT
  BotF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Bot
  LabF : {Γ : TEnv {n}} {L : Subset n} → ⊢ Γ ok → Γ ⊢ Label L
  PiF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Pi A B
  SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Sigma A B
  SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {ok : Γ ⊢ A} → ⊢ Γ ok → Γ ⊢ e ◁ A → notSingle A → Γ ⊢ Single V A
  CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ◁ Label L → Γ ⊢ CaseT U f

data _⊢_◁_ {n} where
  SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
             → Γ ⊢ M ▷ A
             → Γ ⊢ A ≤ᵀ B
             → Γ ⊢ M ◁ B

data _⊢_≤ᵀ_ {n} where
  ASubBot : {Γ : TEnv {n}} {T : Ty {n}} {ok : Γ ⊢ T} → Γ ⊢ Bot ≤ᵀ T
  ASubUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≤ᵀ UnitT
  ASubDyn : {Γ : TEnv {n}} → Γ ⊢ Dyn ≤ᵀ Dyn
  ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⊢ Label L ≤ᵀ Label L'
  ASubSingleSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ≤ᵀ B → Γ ⊢ Single V A ≤ᵀ Single V B
  ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ≤ᵀ B → notSingle B → notCase B → Γ ⊢ Single V A ≤ᵀ B
  ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
           → Γ ⊢ A' ≤ᵀ A
           → ⟨ A' , Γ ⟩ ⊢ B ≤ᵀ B'
           → Γ ⊢ Pi A B ≤ᵀ Pi A' B'
  ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
              → Γ ⊢ A ≤ᵀ A'
              → ⟨ A , Γ ⟩ ⊢ B ≤ᵀ B'
              → Γ ⊢ Sigma A B ≤ᵀ Sigma A' B'
  ASubCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
               → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
               → L' ⊆ L
               → Γ ⊢ (f l ins) ≤ᵀ B
               → Γ ⊢ CaseT U f ≤ᵀ B
  ASubCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
               → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
               → L' ⊆ L
               → Γ ⊢ A ≤ᵀ (f l ins)
               → Γ ⊢ A ≤ᵀ CaseT U f
  ASubCaseXL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
             → Γ ⊢ D ≤ᵀ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
             → Θ ⊢ CaseT (UVal (VVar{i = length Γ'})) f ≤ᵀ B
  ASubCaseXR : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
             → Γ ⊢ D ≤ᵀ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ A ≤ᵀ (f l i))
             → Θ ⊢ A ≤ᵀ CaseT (UVal (VVar{i = length Γ'})) f
  ASubCaseXLDyn : {Γ Γ' Θ : TEnv {n}} {B : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) Dyn , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
                → Θ ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f ≤ᵀ B
  ASubCaseXRDyn : {Γ Γ' Θ : TEnv {n}} {A : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨  Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) Dyn , Γ ⟩) ⊢ A ≤ᵀ (f l i))
                → Θ ⊢ A ≤ᵀ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f 


data _⊢_▷_ {n} where
  BlameA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Blame ▷ Bot
  VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
  CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} {ok : Γ ⊢ A} {ok' : Γ ⊢ B}
           → Γ ⊢ M ▷ A' → Γ ∣ Γ ⊢ A ~ B → Is-just (cast A' A B) → (Data.Maybe.fromMaybe UnitT (cast A' A B)) ≡ B' → Γ ⊢ Cast M A B ▷ B' -- UnitT is arbitrary and is discarded
  UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ▷ UnitT
  LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ▷ Single (VLab{x = l}) (Label ⁅ l ⁆)
  LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {e : Exp {n}} {U : ValU e} {ins : l ∈ L} {f : ∀ l → l ∈ L → Exp {n}}
           → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
           → L' ⊆ L
           → Γ ⊢ (f l ins) ▷ B
           → Γ ⊢ CaseE U f ▷ B
  -- unification has problems with arbitrary functions, hence θ
  -- see https://lists.chalmers.se/pipermail/agda/2020/012293.html
  LabAEx : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
           → Γ ⊢ D ≤ᵀ Label L
           → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (VLab{x = l}) (Label ⁅ l ⁆)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
           → Θ ⊢ CaseE (UVal (VVar{i = length Γ'})) f ▷ CaseT (UVal (VVar{i = length Γ'})) f-t
  LabAExDyn : {Γ Γ' Θ : TEnv {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨  Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
              → Θ ⊢ CaseE (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f ▷ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f-t             
  PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ▷ B → Γ ⊢ Abs M ▷ Pi A B
  PiAE : {Γ : TEnv {n}} {A B D : Ty {n}} {M e : Exp {n}} {V : Val e}
         → Γ ⊢ M ▷ D
         → Γ ⊢ D ⇓ Pi A B
         → Γ ⊢ e ◁ A
         → Γ ⊢ ([ 0 ↦ V ]ᵀ B)
         → Γ ⊢ App M V ▷ ([ 0 ↦ V ]ᵀ B)
  SigmaAI : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
            → Γ ⊢ M ◁ A
            → ⟨ A , Γ ⟩ ⊢ N ▷ B
            → Γ ⊢ Prod M N ▷ Sigma A B
  PairAI : {Γ : TEnv {n}} {A B : Ty {n}} {e N : Exp {n}} {V : Val e}
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
  AURefl-U : {Γ : TEnv {n}} → Γ ⊢ UnitT ⇓ UnitT
  AURefl-L : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ⇓ Label L
  AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
  AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
  AURefl-D : {Γ : TEnv {n}} → Γ ⊢ Dyn ⇓ Dyn
  AURefl-B : {Γ : TEnv {n}} → Γ ⊢ Bot ⇓ Bot
  AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
  AUCaseL : {Γ : TEnv {n}} {D : Ty {n}} {l : Fin n} {L L' : Subset n} {ins : l ∈ L} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
            → L' ⊆ L
            → Γ ⊢ (f l ins) ⇓ D
            → Γ ⊢ CaseT U f ⇓ D

  AUCaseX-P : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
            → Θ ⊢ CaseT (UVal (VVar{i = length Γ'})) fᴮ ⇓ Pi (CaseT (UVal (VVar{i = length Γ'})) fᴬ) (CaseT (UVal (VVar{i = ℕ.suc (length Γ')})) fᴰ)

  AUCaseX-S : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
            → Θ ⊢ CaseT (UVal (VVar{i = length Γ'})) fᴮ ⇓ Sigma (CaseT (UVal (VVar{i = length Γ'})) fᴬ) (CaseT (UVal (VVar{i = ℕ.suc (length Γ')})) fᴰ)

  AUCaseXDyn-P : {Γ Γ' Θ : TEnv {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
                 → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
                 → Θ ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴮ ⇓ Pi (CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴬ) (CaseT (UCast{G = Label L} (VVar{i = ℕ.suc (length Γ')}) GLabel) fᴰ)

  AUCaseXDyn-S : {Γ Γ' Θ : TEnv {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
                 → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
                 → Θ ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴮ ⇓ Sigma (CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴬ) (CaseT (UCast{G = Label L} (VVar{i = ℕ.suc (length Γ')}) GLabel) fᴰ)

data _⊢_≡ᵀ_ {n} where
  AConvUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≡ᵀ UnitT
  AConvBot : {Γ : TEnv {n}} → Γ ⊢ Bot ≡ᵀ Bot
  AConvLabel : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ≡ᵀ Label L
  AConvDyn : {Γ : TEnv {n}} → Γ ⊢ Dyn ≡ᵀ Dyn
  AConvSingle : {Γ : TEnv {n}} {A : Ty} {e : Exp {n}} {V : Val e} {j : Γ ⊢ Single V A} → Γ ⊢ Single V A ≡ᵀ Single V A
  AConvPi : {Γ : TEnv {n}} {A A' B B' : Ty} → Γ ⊢ A ≡ᵀ A' → ⟨ A' , Γ ⟩ ⊢ B ≡ᵀ B' → Γ ⊢ Pi A B ≡ᵀ Pi A' B'
  AConvSigma : {Γ : TEnv {n}} {A A' B B' : Ty} → Γ ⊢ A ≡ᵀ A' → ⟨ A , Γ ⟩ ⊢ B ≡ᵀ B' → Γ ⊢ Sigma A B ≡ᵀ Sigma A' B'
  AConvCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {U : ValU e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
                → L' ⊆ L
                → Γ ⊢ (f l ins) ≡ᵀ B
                → Γ ⊢ CaseT U f ≡ᵀ B
  AConvCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {U : ValU e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
                → L' ⊆ L
                → Γ ⊢ A ≡ᵀ (f l ins)
                → Γ ⊢ A ≡ᵀ CaseT U f               
  AConvCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
             → Γ ⊢ D ≤ᵀ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ (f l i) ≡ᵀ B)
             → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) f ≡ᵀ B
  AConvCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
             → Γ ⊢ D ≤ᵀ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ⊢ A ≡ᵀ (f l i))
             → (Γ' ++ ⟨ D , Γ ⟩) ⊢ A ≡ᵀ CaseT (UVal (VVar{i = length Γ'})) f
  AConvCaseXLDyn : {Γ Γ' : TEnv {n}} {B : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                   → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ⊢ (f l i) ≡ᵀ B)
                   → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ CaseT (UCast{G = (Label L)} (VVar{i = length Γ'}) GLabel) f ≡ᵀ B
  AConvCaseXRDyn : {Γ Γ' : TEnv {n}} {A : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                   → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ⊢ A ≡ᵀ (f l i))
                  → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ A ≡ᵀ CaseT (UCast{G = (Label L)} (VVar{i = length Γ'}) GLabel) f

data _∣_⊢_~_ {n} where
  AConsDynL : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ Dyn ~ A
  AConsDynR : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ Dyn
  AConsRefl : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ A
  AConsSingleL : {Γ Γ' : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ∣ Γ' ⊢ A ~ B → Γ ⊢ e ◁ A → Γ ∣ Γ' ⊢ Single V A ~ B
  AConsSingleR : {Γ Γ' : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ∣ Γ' ⊢ A ~ B → Γ' ⊢ e ◁ A → Γ ∣ Γ' ⊢ A ~ Single V B
  AConsPi : {Γ Γ' : TEnv {n}} {A A' B B' : Ty {n}}
            → Γ ∣ Γ' ⊢ A ~ A'
            → ⟨ A , Γ ⟩ ∣ ⟨ A' , Γ' ⟩ ⊢ B ~ B'
            → Γ ∣ Γ' ⊢ Pi A B ~ Pi A' B'
  AConsSigma : {Γ Γ' : TEnv {n}} {A A' B B' : Ty {n}}
               → Γ ∣ Γ' ⊢ A ~ A'
               → ⟨ A , Γ ⟩ ∣ ⟨ A' , Γ' ⟩ ⊢ B ~ B'
               → Γ ∣ Γ' ⊢ Sigma A B ~ Sigma A' B'
  AConsCaseLL : {Γ Γ' : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {U : ValU e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
                → L' ⊆ L
                → Γ ∣ Γ' ⊢ (f l ins) ~ B
                → Γ ∣ Γ' ⊢ CaseT U f ~ B
  AConsCaseLR : {Γ Γ' : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {U : ValU e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                → Γ' ⊢ e ▷ Single (VLab{x = l}) (Label L')
                → L' ⊆ L
                → Γ ∣ Γ' ⊢ A ~ (f l ins)
                → Γ ∣ Γ' ⊢ A ~ CaseT U f              
  AConsCaseXL : {Γ Γ' Δ Δ' Θ Θ' : TEnv {n}} {B D D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Δ ++ ⟨ D , Γ ⟩)} {eq' : Θ' ≡ (Δ' ++ ⟨ D' , Γ' ⟩)}
             → Γ ⊢ D ≤ᵀ Label L
             → (∀ l → (i : l ∈ L)
                    → {D° : Ty {n}} {p : Is-just (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D')} {env-ty : (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D')) ≡ D°}
                    → (Δ ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ ⟩) ∣ (Δ' ++ ⟨ D° , Γ' ⟩) ⊢ (f l i) ~ B)
             → Θ ∣ Θ' ⊢ CaseT (UVal (VVar{i = length Γ'})) f ~ B
  AConsCaseXR : {Γ Γ' Δ Δ' Θ Θ' : TEnv {n}} {A D D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Δ ++ ⟨ D , Γ ⟩)} {eq' : Θ' ≡ (Δ' ++ ⟨ D' , Γ' ⟩)}
             → Γ ⊢ D' ≤ᵀ Label L
             → (∀ l → (i : l ∈ L)
                    → {D° : Ty {n}} {p : Is-just (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)} {env-ty : (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) ≡ D°}
                    → (Δ ++ ⟨ D° , Γ ⟩) ∣ (Δ' ++ ⟨ Single (VLab{x = l}) (Label ⁅ l ⁆) , Γ' ⟩) ⊢ A ~ (f l i))
             → Θ ∣ Θ' ⊢ A ~ CaseT (UVal (VVar{i = length Γ'})) f
  AConsCaseXLDyn : {Γ Γ' Δ Δ' Θ Θ' : TEnv {n}} {B D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Δ ++ ⟨ Dyn , Γ ⟩)} {eq' : Θ' ≡ (Δ' ++ ⟨ D' , Γ' ⟩)}
                   → (∀ l → (i : l ∈ L)
                     → {D° : Ty {n}} {p : Is-just (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D')} {env-ty : (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D')) ≡ D°}
                     → (Δ ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ ⟩) ∣ (Δ' ++ ⟨ D° , Γ' ⟩) ⊢ (f l i) ~ B)
                   → Θ ∣ Θ' ⊢ CaseT (UCast{G = (Label L)} (VVar{i = length Γ'}) GLabel) f ~ B
  AConsCaseXRDyn : {Γ Γ' Δ Δ' Θ Θ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Δ ++ ⟨ D , Γ ⟩)} {eq' : Θ' ≡ (Δ' ++ ⟨ Dyn , Γ' ⟩)}
                   → (∀ l → (i : l ∈ L)
                     → {D° : Ty {n}} {p : Is-just (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)} {env-ty : (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) ≡ D°}
                     → (Δ ++ ⟨ D° , Γ ⟩) ∣ (Δ' ++ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , Γ' ⟩) ⊢ A ~ (f l i))
                   →  Θ ∣ Θ' ⊢ A ~ CaseT (UCast{G = (Label L)} (VVar{i = length Γ'}) GLabel) f

------------------------------------------------------------------------
-- Small step semantics

-- Type reduction
data _↠_ {n : ℕ} : Ty {n} → Ty {n} → Set
-- Expression reduction
data _⇨_ {n : ℕ} : Exp {n} → Exp {n} → Set

data _↠_ {n} where
  ξ-Case : {e e' : Exp {n}} {U : ValU e} {U' : ValU e'} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → e ⇨ e' → CaseT U f ↠ CaseT U' f
  ξ-Pi : {A A' B : Ty {n}} → A ↠ A' → Pi A B ↠ Pi A' B
  ξ-Sigma : {A A' B : Ty {n}} → A ↠ A' → Sigma A B ↠ Sigma A' B
  β-Single : {A : Ty {n}} {e : Exp {n}} {V : Val e}  → Single V A ↠ A
  β-Case : {l : Fin n} {s : Subset n} {ins : l ∈ s} {f : ∀ l → l ∈ s → Ty {n}} → CaseT (UVal (VLab{x = l})) f ↠ f l ins
  Case-Bot : {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → CaseT UBlame f ↠ Bot

data _⇨_ {n} where
  ξ-App : {e₁ e₁' e : Exp {n}} {v : Val e} → e₁ ⇨ e₁' → App e₁ v ⇨ App e₁' v
  ξ-LetE : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → LetE e₁ e ⇨ LetE e₁' e
  ξ-Prod : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → Prod e₁ e ⇨ Prod e₁' e
  ξ-ProdV : {e e₂ e₂' : Exp {n}} {v : Val e} → e₂ ⇨ e₂' → ProdV v e₂ ⇨ ProdV v e₂'
  ξ-LetP : {e₁ e₁' e₂ : Exp {n}} → e₁ ⇨ e₁' → LetP e₁ e₂ ⇨ LetP e₁' e₂
  ξ-Cast : {e₁ e₂ : Exp {n}} {A B : Ty {n}} → e₁ ⇨ e₂ → Cast e₁ A B ⇨ Cast e₂ A B
  ξ-Case : {s : Subset n} {e₁ e₂ : Exp {n}} {U : ValU e₁} {U' : ValU e₂} {f : ∀ l → l ∈ s → Exp {n}} → e₁ ⇨ e₂ → CaseE U f ⇨ CaseE U' f
  β-App : {e e' : Exp {n}} → (v : Val e') → (App (Abs e) v) ⇨ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e) ])
  β-Prod : {e e' : Exp {n}} {v : Val e} → Prod e e' ⇨ ProdV v (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
  β-LetE : {e e' : Exp {n}} → (v : Val e) → LetE e e' ⇨ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
  β-LetP : {e e' e'' : Exp {n}} → (v : Val e) → (v' : Val e')
                            → LetP (ProdV v e') e''
                              ⇨
                              ↑ (ℤ.negsuc 1) , 0 [ ([ 0 ↦ ↑ⱽ¹[ v ] ]
                                                     ([ 0 ↦ shift-val {n} {ℤ.pos 1} {1} v' ] e'')) ]
  β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} {x : Fin n} → (ins : x ∈ s)
           → CaseE (UVal (VLab{x = x})) f ⇨ f x ins
  Cast-Dyn : {e : Exp {n}} {v : Val e} → Cast e Dyn Dyn ⇨ e
  Cast-Unit : {e : Exp {n}} {v : Val e} → Cast e UnitT UnitT ⇨ e
  Cast-Label : {e : Exp {n}} {v : Val e} {L L' : Subset n} → L ⊆ L' → Cast e (Label L) (Label L') ⇨ e
  Cast-Func : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}} → App (Cast e (Pi A B) (Pi A' B')) w ⇨ LetE (Cast e' A' A) (Cast (App e (VVar{i = 0})) B ([ 0 ↦ w ]ᵀ B'))
  Cast-Pair : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}}
              → Cast (ProdV v e') (Sigma A B) (Sigma A' B') ⇨ LetE (Cast e A A') (ProdV (VVar{i = 0}) (Cast e' ([ 0 ↦ v ]ᵀ B) B'))
  Cast-Collapse-Label-Label : {e : Exp {n}} {v : Val e} {L L' : Subset n} → L ⊆ L' → Cast (Cast e (Label L) Dyn) Dyn (Label L') ⇨ e
  Cast-Collapse : {e : Exp {n}} {v : Val e} {G : Ty {n}} {g : TyG G} → Cast (Cast e G Dyn) Dyn G ⇨ e
  Cast-Collide : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {g : TyG G} {h : TyG H} → G ≢ H → Cast (Cast e G Dyn) Dyn H ⇨ Blame
  Cast-Reduce-L : {e : Exp {n}} {v : Val e} {A A' B : Ty {n}} → A ↠ A' → Cast e A B ⇨ Cast e A' B
  Cast-Reduce-R : {e : Exp {n}} {v : Val e} {A B B' : Ty {n}} → TyNf A → B ↠ B' → A ≢ Bot → Cast e A B ⇨ Cast e A B'
  Cast-Factor-L : {e : Exp {n}} {v : Val e} {G nA : Ty {n}} {g : TyG G} {nfA : TyNf nA} → ([] ∣ [] ⊢ G ~ nA) → [] ⊢ nA → G ≢ nA → nA ≢ Dyn → Cast e nA Dyn ⇨ Cast (Cast e nA G) G Dyn
  Cast-Factor-R : {e : Exp {n}} {v : Val e} {G nB : Ty {n}} {g : TyG G} {nfB : TyNf nB} → ([] ∣ [] ⊢ G ~ nB) → [] ⊢ nB → G ≢ nB → nB ≢ Dyn → Cast e Dyn nB ⇨ Cast (Cast e Dyn G) G nB
  App-Blame : {e : Exp {n}} {v : Val e} → App Blame v ⇨ Blame
  LetE-Blame : {e : Exp {n}} → LetE Blame e ⇨ Blame
  Prod-Blame : {e : Exp {n}} → Prod Blame e ⇨ Blame
  ProdV-Blame : {e : Exp {n}} {v : Val e} → ProdV v Blame ⇨ Blame
  LetP-Blame : {e  : Exp {n}} → LetP Blame e ⇨ Blame
  Cast-Blame : {A B : Ty {n}} → Cast Blame A B ⇨ Blame
  Cast-Bot-L : {e : Exp {n}} {B : Ty {n}} → Cast e Bot B ⇨ Blame
  Cast-Bot-R : {e : Exp {n}} {A : Ty {n}} → TyNf A → A ≢ Bot → Cast e A Bot ⇨ Blame    
  Case-Blame : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} → CaseE UBlame f ⇨ Blame

------------------------------------------------------------------------
-- Big step semantics

Env : {ℕ} → Set
Env {n} = List (Exp {n})

-- Values without variables
data Val* {n : ℕ} : Exp {n} → Set
val*⇒val : {n : ℕ} {e : Exp {n}} → Val* e → Val e

data Val* {n} where
  VUnit : Val* UnitE
  VLab : {x : Fin n} → Val* (LabI x)
  VFun : {N : Exp} → Val* (Abs N)
  VProd : {e e' : Exp} → (v : Val* e) → Val* e' → Val* (ProdV (val*⇒val v) e')
  VCast : {e : Exp} {G : Ty {n}} → Val* e → TyG G → Val* (Cast e G Dyn)
  VCastFun : {e : Exp} {nA nA' B B' : Ty {n}} {nfA : TyNf nA} {nfA' : TyNf nA'} → Val* e → Val* (Cast e (Pi nA B) (Pi nA' B'))

val*⇒val {n} {.UnitE} VUnit = VUnit
val*⇒val {n} {.(LabI _)} VLab = VLab
val*⇒val {n} {.(Abs _)} VFun = VFun
val*⇒val {n} {.(ProdV _ _)} (VProd j j₁) = VProd (val*⇒val j) (val*⇒val j₁)
val*⇒val {n} {.(Cast _ _ Dyn)} (VCast j x) = VCast (val*⇒val j) x
val*⇒val {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun{nfA = nfA}{nfA' = nfA'} j) = VCastFun{nfA = nfA}{nfA' = nfA'} (val*⇒val j)

-- Result with values without variables
data Result* {n : ℕ} : Exp {n} → Set where
  RValue : {e : Exp {n}} → Val* {n} e → Result* {n} e
  RBlame :  Result* {n} Blame

access : {n : ℕ} {Γ : Env {n}} → (m : ℕ) → All Val* Γ → Σ (Exp {n}) Result*
access {n} {.[]} m [] = Blame , RBlame
access {n} {(e ∷ Γ)} zero (px ∷ venv) = (e , RValue px)
access {n} {.(_ ∷ _)} (ℕ.suc m) (px ∷ venv) = access m venv

-- Reduces a cast V : A ⇒ B, returns Blame if A and B collide
castreduce : {n : ℕ} {e : Exp {n}} → Val* e → Ty {n} → Ty {n} → Σ (Exp {n}) Result*
-- Cast-Collapse-Label-Label
castreduce {n} {e} (VCast{e = e'}{Label s} v g) Dyn (Label s')
  with s ⊆? s'
...  | yes p =  (e' , RValue v)
...  | no ¬p = Blame , RBlame
-- Collapse/Collide
castreduce {n} {e} (VCast{e = e'}{G} v g) Dyn B
  with G ≡ᵀ? B
...  | yes p =  (e' , RValue v)
...  | no ¬p = Blame , RBlame
-- Illegal
castreduce {n} {e} (VCast{e = e'}{G} v g) A B = Blame , RBlame
-- Collapse/Collide
castreduce {n} {e} (VCastFun{e = e'}{nA}{nA'}{B}{B'} v) A B*
  with A ≡ᵀ? Pi nA' B'
...  | no ¬p = Blame , RBlame
...  | yes p
     with B* ≡ᵀ? Pi nA B
...     | yes p' =  (e' , RValue v)
...     | no ¬p' = Blame , RBlame
-- Base Cases
castreduce {n} {e} V UnitT UnitT =  (e , RValue V)
castreduce {n} {e} V Dyn Dyn =  (e , RValue V)
castreduce {n} {e} V (Label s) (Label s')
  with (s ⊆? s')
...  | yes p =  (e , RValue V)
...  | no ¬p = Blame , RBlame
-- Value
castreduce {n} {e} V G Dyn
  with TyG? G
...  | yes p =  ((Cast e G Dyn) , RValue (VCast V p))
...  | no ¬p = Blame , RBlame
-- Illegal
castreduce {n} {e} V A B = Blame , RBlame

-- Big step semantics for expressions and types, returns Blame/Bot if term/type stuck and not a/in value/nf
_∶_⇓ : {n : ℕ} {Γ : Env {n}} (venv : All Val* Γ) (e : Exp {n}) → Σ (Exp {n}) Result*
_∶_⇓ᵀ : {n : ℕ} {Γ : Env {n}} (venv : All Val* Γ) (T : Ty {n}) → Σ (Ty {n}) TyNf

_∶_⇓ {n} {Γ} venv (App{e = e'} (Cast (Abs e) A B) x)
  with venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ | venv ∶ e' ⇓
...  | (Pi Â B̂) , NfPi | (Pi Â' B̂') , NfPi | e* , RValue v* = venv ∶ LetE (Cast e' Â' Â) (Cast (App (Abs e) (VVar{i = 0})) B̂ ([ 0 ↦ val*⇒val v* ]ᵀ B̂')) ⇓
...  | _ | _ | _ = Blame , RBlame
_∶_⇓ {n} {Γ} venv (App{e = e'} e x)
  with venv ∶ e ⇓ | venv ∶ e' ⇓
...  | ((Abs e*) , RValue VFun) | (e'' , RValue v') = (v' ∷ venv) ∶ e* ⇓
...  | _ | _ = Blame , RBlame
_∶_⇓ {n} {Γ} venv (Cast (ProdV{e = e} v e') A B)
  with venv ∶ e ⇓ | venv ∶ e' ⇓ | venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ
...  | (e* , RValue v*) | e** , RValue v** | (Sigma Â B̂) , NfSigma | (Sigma Â' B̂') , NfSigma = venv ∶ LetE (Cast e* Â Â') (ProdV (VVar{i = zero}) (Cast e** ([ 0 ↦ val*⇒val v* ]ᵀ B̂) B̂')) ⇓
...  | _ | _ | _ | _ = Blame , RBlame
_∶_⇓ {n} {Γ} venv (Cast e A B)
  with venv ∶ e ⇓ | venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ
...  | _ | Bot , NfBot | _ = Blame , RBlame 
...  | _ | _ | Bot , NfBot = Blame , RBlame 
...  | (e* , RValue val) | Â , NfA | B̂ , NfB = castreduce val Â B̂
...  | Blame , RBlame | _ | _ = Blame , RBlame  
_∶_⇓ {n} {Γ} venv (LetE e e₁)  
  with venv ∶ e ⇓
...  | (e' , RValue v) = _∶_⇓{Γ = e' ∷ Γ} (v ∷ venv) e₁
...  | Blame , RBlame = Blame , RBlame
_∶_⇓ {n} {Γ} venv (Var x) = access x venv
_∶_⇓ {n} {Γ} venv UnitE = UnitE , RValue VUnit
_∶_⇓ {n} {Γ} venv Blame = Blame , RBlame
_∶_⇓ {n} {Γ} venv (Abs e) = (Abs e) , (RValue VFun)
_∶_⇓ {n} {Γ} venv (LabI x) =  LabI x , RValue VLab
_∶_⇓ {n} {Γ} venv (CaseE{s = s}{e = e} x f)
  with venv ∶ e ⇓
...  | Blame , RBlame = Blame , RBlame
...  | ((LabI l) , RValue (VLab{x = l}))
     with l ∈? s
...     | yes ins = venv ∶ (f l ins) ⇓ 
...     | no ¬ins = Blame , RBlame
_∶_⇓ {n} {Γ} venv (CaseE{e = e} x f) | e' = Blame , RBlame  
_∶_⇓ {n} {Γ} venv (Prod e e₁)
    with venv ∶ e ⇓
...  | Blame , RBlame = Blame , RBlame
...  | (e' , RValue v)
     with ((v ∷ venv) ∶ e₁ ⇓)
...     | (e₁' , RValue v') = (ProdV (val*⇒val v) e₁') , RValue (VProd v v')
...     | Blame , RBlame = Blame , RBlame
_∶_⇓ {n} {Γ} venv (ProdV{e = e} x e')
    with venv ∶ e ⇓ | venv ∶ e' ⇓
...  | (e* , RValue v*) | (e** , RValue v**) = ((ProdV (val*⇒val v*) e**) , RValue (VProd v* v**))
...  | _ | _ = Blame , RBlame
_∶_⇓ {n} {Γ} venv (LetP e e₁)
  with venv ∶ e ⇓
...  | (ProdV{e = e*} v₁ e₂ , RValue (VProd v₁* v₂*)) = (v₂* ∷ (v₁* ∷ venv)) ∶ e₁ ⇓
...  | (e* , v*) = Blame , RBlame

venv ∶ Bot ⇓ᵀ = Bot , NfBot
venv ∶ UnitT ⇓ᵀ = UnitT , (NfUnit)
venv ∶ Dyn ⇓ᵀ = Dyn , (NfDyn)
venv ∶ Label x ⇓ᵀ = (Label x) , (NfLabel)
venv ∶ Single x T ⇓ᵀ = venv ∶ T ⇓ᵀ
venv ∶ Pi T T₁ ⇓ᵀ
  with venv ∶ T ⇓ᵀ
...  | T' , NfT' = (Pi T' T₁) , ((NfPi{nfA = NfT'}))
venv ∶ Sigma T T₁ ⇓ᵀ
  with venv ∶ T ⇓ᵀ
...  | T' , NfT' = (Sigma T' T₁) , ((NfSigma{nfA = NfT'}))  
venv ∶ CaseT{s = s}{e = e} x f ⇓ᵀ
  with venv ∶ e ⇓
... | (LabI l) , (RValue (VLab{x = .l}))
  with l ∈? s
...  | yes ins = venv ∶ (f l ins) ⇓ᵀ
...  | no ¬ins = Bot , NfBot
venv ∶ CaseT{s = s}{e = e} x f ⇓ᵀ | e' , RValue v' = Bot , NfBot
venv ∶ CaseT{s = s}{e = e} x f ⇓ᵀ | .Blame , RBlame = Bot , NfBot

------------------------------------------------------------------------
-- Cast function, properties

cast (Single{e = e} x A) (Single{e = e'} x₁ B) C
  with A ≡ᵀ? B | e ≡ᵉ? e'
...  | yes p | yes p' = just C
...  | yes p | no ¬p' = nothing
...  | no ¬p | _ = nothing

cast (Single{e = e} x A) Bot C
  with A ≡ᵀ? Bot | [] ∶ (Cast e Bot C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) UnitT C
  with A ≡ᵀ? UnitT | [] ∶ (Cast e UnitT C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) Dyn C
  with A ≡ᵀ? Dyn | [] ∶ (Cast e Dyn C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) (Label x₁) C
  with A ≡ᵀ? Label x₁ | [] ∶ (Cast e (Label x₁) C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) (Pi B B₁) C
  with A ≡ᵀ? (Pi B B₁) | [] ∶ (Cast e (Pi B B₁) C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) (Sigma B B₁) C
  with A ≡ᵀ? (Sigma B B₁) | [] ∶ (Cast e (Sigma B B₁) C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing
cast (Single{e = e} x A) (CaseT x₁ f) C
  with A ≡ᵀ? (CaseT x₁ f) | [] ∶ (Cast e (CaseT x₁ f) C) ⇓
...  | yes p | e₁ , RValue W = just (Single (val*⇒val W) C)
...  | yes p | Blame , RBlame = just C
...  | no ¬p | _ = nothing

cast Bot B C
  with B ≡ᵀ? Bot
...  | yes p = just C
...  | no ¬p = nothing
cast UnitT B C
  with B ≡ᵀ? UnitT 
...  | yes p = just C
...  | no ¬p = nothing
cast Dyn B C
  with B ≡ᵀ? Dyn
...  | yes p = just C
...  | no ¬p = nothing
cast (Label x) B C
  with B ≡ᵀ? (Label x)
...  | yes p = just C
...  | no ¬p = nothing
cast (Pi A A₁) B C
  with B ≡ᵀ? (Pi A A₁)
...  | yes p = just C
...  | no ¬p = nothing
cast (Sigma A A₁) B C
  with B ≡ᵀ? (Sigma A A₁)
...  | yes p = just C
...  | no ¬p = nothing
cast (CaseT x f) B C
  with B ≡ᵀ? (CaseT x f)
...  | yes p = just C
...  | no ¬p = nothing

-- properties

cast-trivial-just : {n : ℕ} {A B C : Ty {n}} → A ≡ B → Is-just (cast A B C)
cast-trivial-just {n} {Bot} {.Bot} {C} refl = just Data.Unit.tt
cast-trivial-just {n} {UnitT} {.UnitT} {C} refl = just Data.Unit.tt
cast-trivial-just {n} {Dyn} {.Dyn} {C} refl = just Data.Unit.tt
cast-trivial-just {n} {Single{e = e} x A} {.(Single x A)} {C} refl
  with A ≡ᵀ? A | e ≡ᵉ? e
...  | yes eq | yes eq' rewrite eq | eq' = just Data.Unit.tt
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial-just {n} {Label x} {.(Label x)} {C} refl
  with x ≡ˢ? x
...  | yes eq rewrite eq = just Data.Unit.tt
...  | no ¬eq = contradiction refl ¬eq
cast-trivial-just {n} {Pi A A₁} {.(Pi A A₁)} {C} refl
  with A ≡ᵀ? A | A₁ ≡ᵀ? A₁
...  | yes eq | yes eq' rewrite eq | eq' = just Data.Unit.tt
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial-just {n} {Sigma A A₁} {.(Sigma A A₁)} {C} refl
  with A ≡ᵀ? A | A₁ ≡ᵀ? A₁
...  | yes eq | yes eq' rewrite eq | eq' = just Data.Unit.tt
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial-just {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl
  with e ≡ᵉ? e | s ≡ˢ? s
...  | yes eq | yes eq'
     rewrite eq | eq' | (ValU-uniqueness x x)
     with (_≡ᶠ?_{dec = λ a a' → _≡ᵀ?_ a a' } f f)
...     | yes eq'' rewrite eq'' = just Data.Unit.tt
cast-trivial-just {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | yes eq | yes eq' | no ¬eq'' = contradiction refl ¬eq''
cast-trivial-just {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | yes eq | no ¬eq' = contradiction refl ¬eq'
cast-trivial-just {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | no ¬eq | _ = contradiction refl ¬eq

cast-trivial : {n : ℕ} → {A B C : Ty {n}} → A ≡ B → (Data.Maybe.fromMaybe UnitT (cast A B C)) ≡ C
cast-trivial {n} {Bot} {.Bot} {C} refl = refl
cast-trivial {n} {UnitT} {.UnitT} {C} refl = refl
cast-trivial {n} {Dyn} {.Dyn} {C} refl = refl
cast-trivial {n} {Single{e = e} x A} {.(Single x A)} {C} refl
  with A ≡ᵀ? A | e ≡ᵉ? e
...  | yes eq | yes eq' rewrite eq | eq' = refl
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial {n} {Label x} {.(Label x)} {C} refl
  with x ≡ˢ? x
...  | yes eq rewrite eq = refl
...  | no ¬eq = contradiction refl ¬eq
cast-trivial {n} {Pi A A₁} {.(Pi A A₁)} {C} refl
  with A ≡ᵀ? A | A₁ ≡ᵀ? A₁
...  | yes eq | yes eq' rewrite eq | eq' = refl
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial {n} {Sigma A A₁} {.(Sigma A A₁)} {C} refl
  with A ≡ᵀ? A | A₁ ≡ᵀ? A₁
...  | yes eq | yes eq' rewrite eq | eq' = refl
...  | yes eq | no ¬eq' = contradiction refl ¬eq'
...  | no ¬eq | _ = contradiction refl ¬eq
cast-trivial {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl
  with e ≡ᵉ? e | s ≡ˢ? s
...  | yes eq | yes eq'
     rewrite eq | eq' | (ValU-uniqueness x x)
     with (_≡ᶠ?_{dec = λ a a' → _≡ᵀ?_ a a' } f f)
...     | yes eq'' rewrite eq'' = refl
cast-trivial {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | yes eq | yes eq' | no ¬eq'' = contradiction refl ¬eq''
cast-trivial {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | yes eq | no ¬eq' = contradiction refl ¬eq'
cast-trivial {n} {CaseT{s = s}{e = e} x f} {.(CaseT x f)} {C} refl | no ¬eq | _ = contradiction refl ¬eq

cast-trivial-just-inv : {n : ℕ} {A B C : Ty {n}} → Is-just (cast A B C) → A ≡ B ⊎ (∃[ e ](∃[ V ](A ≡ Single{e = e} V B)))
cast-trivial-just-inv {n} {Single{e = e} x A} {Single{e = e'} x₁ B} {C} ju
  with A ≡ᵀ? B | e ≡ᵉ? e'
...  | yes eq | yes eq' rewrite eq | eq' | Val-uniqueness x x₁ = inj₁ refl
cast-trivial-just-inv {n} {Single{e = e} x A} {Bot} {C} ju
  with A ≡ᵀ? Bot
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {UnitT} {C} ju
  with A ≡ᵀ? UnitT
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {Dyn} {C} ju
  with A ≡ᵀ? Dyn
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {Label x₁} {C} ju
  with A ≡ᵀ? (Label x₁)
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {Pi B B₁} {C} ju
  with A ≡ᵀ? (Pi B B₁)
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {Sigma B B₁} {C} ju
  with A ≡ᵀ? (Sigma B B₁)
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Single{e = e} x A} {CaseT x₁ f} {C} ju
  with A ≡ᵀ? (CaseT x₁ f)
... | yes p rewrite p = inj₂ (e , x , refl)
cast-trivial-just-inv {n} {Bot} {B} {C} ju
  with B ≡ᵀ? Bot
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {UnitT} {B} {C} ju
  with B ≡ᵀ? UnitT
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {Dyn} {B} {C} ju
  with B ≡ᵀ? Dyn
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {Label x} {B} {C} ju
  with B ≡ᵀ? (Label x)
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {Pi A A₁} {B} {C} ju
  with B ≡ᵀ? (Pi A A₁)
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {Sigma A A₁} {B} {C} ju
  with B ≡ᵀ? (Sigma A A₁)
...  | yes p = inj₁ (sym p)
cast-trivial-just-inv {n} {CaseT x f} {B} {C} ju
  with B ≡ᵀ? (CaseT x f)
...  | yes p = inj₁ (sym p)

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

cast-dyn-s : {n : ℕ} {A' A : Ty {n}} {s : Subset n} → Is-just (cast A' A Dyn) → ¬(Data.Maybe.fromMaybe UnitT (cast A' A Dyn) ≡ Label s)
cast-dyn-s {n} {A'} {A} {s} isj
  with cast-result {n} {A'} {A} {Dyn} isj
...  | inj₁ x = λ y → contradiction (≡-trans (sym x) y) λ () 
...  | inj₂ (fst , snd , thd) = λ y → contradiction (≡-trans (sym thd) y) λ ()

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

------------------------------------------------------------------------
-- Various properties

-- If two types are in ground form and consistent, then they are equal
tyg-equal : {n : ℕ} {T T' : Ty {n}} → TyG T → TyG T' → [] ∣ [] ⊢ T ~ T' → T ≡ T'
tyg-equal {n} {.UnitT} {.UnitT} GUnit GUnit cons = refl
tyg-equal {n} {.(Label _)} {.(Label _)} GLabel GLabel (AConsRefl x) = refl
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
val-noreduce {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun{nfA' = nfA'} v) .(Cast _ (Pi _ _) _) (Cast-Reduce-R{B' = B'} y x z) = contradiction x (tynf-noreduce (NfPi{nfA = nfA'}) B')

-- ValU closed under reduction
valu-closed : {n : ℕ} {e e' : Exp {n}} → ValU e → e ⇨ e' → ValU e'
valu-closed {n} {e} {e'} (UVal v) r = contradiction r (val-noreduce v e')  
valu-closed {n} {.(Cast (Cast e' (Label _) Dyn) Dyn (Label _))} {e'} (UCast (VCast x x₂) x₁) (Cast-Collapse-Label-Label{v = v} x₃) = UVal v
valu-closed {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} (UCast (VCast x x₂) x₁) (Cast-Collapse {v = v}) = UVal v
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} (UCast x x₁) (Cast-Collide x₂) = UBlame
valu-closed {n} {.(Cast UnitE Dyn _)} {.(Cast UnitE Dyn _)} (UCast VUnit x₁) (Cast-Reduce-R{B' = B'} y x z) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast UnitE Dyn _)} {.(Cast (Cast UnitE Dyn _) _ _)} (UCast VUnit x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) = contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Var _) Dyn _)} (UCast VVar x₁) (Cast-Reduce-R{B' = B'} y x z) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Cast (Var _) Dyn _) _ _)} (UCast VVar x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (LabI _) Dyn _)} {.(Cast (LabI _) Dyn _)} (UCast VLab x₁) (Cast-Reduce-R{B' = B'} y x z) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (LabI _) Dyn _)} {.(Cast (Cast (LabI _) Dyn _) _ _)} (UCast VLab x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (Abs _) Dyn _)} {.(Cast (Abs _) Dyn _)} (UCast VFun x₁) (Cast-Reduce-R{B' = B'} y x z) = contradiction x (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Abs _) Dyn _)} {.(Cast (Cast (Abs _) Dyn _) _ _)} (UCast VFun x₁) (Cast-Factor-R{g = g} x x₂ x₃ x₄) =  contradiction (tyg-equal g x₁ x) x₃
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (ProdV x _) Dyn _)} (UCast (VProd x x₂) x₁) (Cast-Reduce-R{B' = B'} y x' z) = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (Cast (ProdV x _) Dyn _) _ _)} (UCast (VProd x x₂) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (Cast-Reduce-R{B' = B'} y x' z) = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast (Cast _ _ Dyn) Dyn _) _ _)} (UCast (VCast x x₂) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun x) x₁) (Cast-Reduce-R{B' = B'} y x' z) = contradiction x' (tyg-noreduce x₁ B')
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _) _ _)} (UCast (VCastFun x) x₁) (Cast-Factor-R{g = g} x' x₂' x₃ x₄) =  contradiction (tyg-equal g x₁ x') x₃ 
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (Cast-Reduce-L{A' = A'} x₃)) = contradiction x₃ (tyg-noreduce x₂ A')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast (Cast _ _ _) _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (Cast-Factor-L{g = g} x₃ x₄ x₅ x₆)) = contradiction (tyg-equal g x₂ x₃) x₅
valu-closed {n} {.(Cast (ProdV x _) Dyn _)} {.(Cast (ProdV x _) Dyn _)} (UCast (VProd x x₂) x₁) (ξ-Cast (ξ-ProdV{e₂' = e₂'} r)) = contradiction r (val-noreduce x₂ e₂')
valu-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} (UCast (VCast x x₂) x₁) (ξ-Cast (ξ-Cast{e₂ = e₂} r)) = contradiction r (val-noreduce x e₂)
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun x) x₁) (ξ-Cast (ξ-Cast{e₂ = e₂} r)) = contradiction r (val-noreduce x e₂)
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun{nfA = nfA} x) x₁) (ξ-Cast (Cast-Reduce-L (ξ-Pi{A' = A'} x₂))) = contradiction x₂ (tynf-noreduce nfA A')
valu-closed {n} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} {.(Cast (Cast _ (Pi _ _) (Pi _ _)) Dyn _)} (UCast (VCastFun{nfA' = nfA'} x) x₁) (ξ-Cast (Cast-Reduce-R y (ξ-Pi{A' = A'} x₂) z)) = contradiction x₂ (tynf-noreduce nfA' A')

-- Dyn can't be subtype of Label
¬dyn-label-sub : {n : ℕ} {s : Subset n} {A : Ty {n}} → [] ⊢ A ≤ᵀ Label s → A ≢ Dyn
¬dyn-label-sub {n} {s} {.(Label _)} (ASubLabel x) = λ ()
¬dyn-label-sub {n} {s} {.(Single _ _)} (ASubSingle leq x x₁) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT _ _)} (ASubCaseLL x x₁ leq) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT (UVal VVar) _)} (ASubCaseXL leq x) = λ ()
¬dyn-label-sub {n} {s} {.(CaseT (UCast VVar GLabel) _)} (ASubCaseXLDyn x) = λ ()
