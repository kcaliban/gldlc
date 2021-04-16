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
-- Conversion
-- data _⊢_≡ᵀ_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
-- precise cast function
cast : {n : ℕ} → Ty {n} → Ty {n} → Ty {n} → Ty {n}

-- Implementations
data ⊢_ok {n} where
  empty : ⊢ [] ok
  entry : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ A → ⊢ ⟨ A , Γ ⟩ ok

{-
data ⊢_∣_ok {n} where
  empty : ⊢ [] ∣ [] ok
  entry : {Γ Γ' : TEnv {n}} {A A' : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ A' → Γ ⊢ A → Γ' ⊢ A' → ⊢ ⟨ A , Γ ⟩ ∣ ⟨ A' , Γ' ⟩ ok
-}

data _⊢_ {n} where
  DynF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Dyn
  UnitF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitT
  BotF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ Bot
  LabF : {Γ : TEnv {n}} {L : Subset n} → ⊢ Γ ok → Γ ⊢ Label L
  PiF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Pi A B
  SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Sigma A B
  SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {ok : Γ ⊢ A} → ⊢ Γ ok → Γ ⊢ e ◁ A → TyB A → Γ ⊢ Single V
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
  ASubUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≤ᵀ UnitT
  ASubDyn : {Γ : TEnv {n}} → Γ ⊢ Dyn ≤ᵀ Dyn
  ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⊢ Label L ≤ᵀ Label L'
  ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ e ◁ B → TyB B → notSingle B → Γ ⊢ Single V ≤ᵀ B
  ASubSingleSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e e' : Exp {n}} {V : Val e} {W : Val e'} → e ≡ e' → Γ ⊢ Single V ≤ᵀ Single W
  ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
           → Γ ⊢ A' ≤ᵀ A
           → ⟨ A' , Γ ⟩ ⊢ B ≤ᵀ B'
           → Γ ⊢ Pi A B ≤ᵀ Pi A' B'
  ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
              → Γ ⊢ A ≤ᵀ A'
              → ⟨ A , Γ ⟩ ⊢ B ≤ᵀ B'
              → Γ ⊢ Sigma A B ≤ᵀ Sigma A' B'
            
  ASubCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (VLab{x = l})
               → (ins : l ∈ L)
               → Γ ⊢ (f l ins) ≤ᵀ B
               → Γ ⊢ CaseT U f ≤ᵀ B
  ASubCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {U : ValU e} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ e ▷ Single (VLab{x = l})
               → (ins : l ∈ L)
               → Γ ⊢ A ≤ᵀ (f l ins)
               → Γ ⊢ A ≤ᵀ CaseT U f
  ASubCaseXL : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) , Γ ⟩) ⊢ (f l (sub i)) ≤ᵀ B)
               → Θ ⊢ CaseT (UVar{x = length Γ'}) f ≤ᵀ B
  ASubCaseXR : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → notSingle D
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)             
               → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) , Γ ⟩) ⊢ A ≤ᵀ (f l (sub i)))
               → Θ ⊢ A ≤ᵀ CaseT (UVar{x = length Γ'}) f
  ASubCaseXLDyn : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → Γ ⊢ D ≤ᵀ Label L
                → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
                → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ (cast (Single (VLab{x = l})) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (f l (sub i)) ≤ᵀ B)
                → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) f ≤ᵀ B
  ASubCaseXRDyn : {Γ Γ' Θ : TEnv {n}} {A D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → Γ ⊢ D ≤ᵀ Label L
                → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
                → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨  (cast (Single (VLab{x = l})) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ A ≤ᵀ (f l (sub i)))
                → Θ ⊢ A ≤ᵀ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) f

data _⊢_▷_ {n} where
  BlameA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Blame ▷ Bot
  VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
  CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} {ok : Γ ⊢ A} {ok' : Γ ⊢ B}
           → Γ ⊢ M ▷ A' → B' ≡ (cast A' A B) → Γ ⊢ Cast M A B ▷ B'
  UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ▷ Single VUnit
  LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ▷ Single (VLab{x = l})
  LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L : Subset n} {l : Fin n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
           → Γ ⊢ e ▷ Single (VLab{x = l})
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
           → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
           → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ (Single (VLab{x = l})) , Γ ⟩) ⊢ (f l (sub i)) ▷ (f-t l i))
           → Θ ⊢ CaseE (UVar{x = length Γ'}) f ▷ CaseT (UVar{x = length Γ'}) f-t
  LabAExDyn : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → notSingle D
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l})) (Label L) D)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
            → Θ ⊢ CaseE (UVarCast{x = length Γ'}{A = D}{Label L}) f ▷ CaseT (UVarCast{x = length Γ'}{A = D}{Label L}) f-t
  PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ▷ B → Γ ⊢ Abs M ▷ Pi A B
  PiAE-V : {Γ : TEnv {n}} {A B D F : Ty {n}} {M N : Exp {n}} {V : Val N} {eq : F ≡ [ 0 ↦ V ]ᵀ B}
         → Γ ⊢ M ▷ D
         → Γ ⊢ D ⇓ Pi A B
         → Γ ⊢ N ◁ A
         → 0 ∈`ᵀ B
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
--  AURefl-U : {Γ : TEnv {n}} → Γ ⊢ UnitT ⇓ UnitT
--  AURefl-L : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ⇓ Label L
--  AURefl-D : {Γ : TEnv {n}} → Γ ⊢ Dyn ⇓ Dyn
--  AURefl-B : {Γ : TEnv {n}} → Γ ⊢ Bot ⇓ Bot
--  AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
  AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
  AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
  AUCaseL-P : {Γ : TEnv {n}} {A B : Ty {n}} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (VLab{x = l})
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Pi A B
            → Γ ⊢ CaseT U f ⇓ Pi A B
  AUCaseL-S : {Γ : TEnv {n}} {A B : Ty {n}} {l : Fin n} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
            → Γ ⊢ e ▷ Single (VLab{x = l})
            → (ins : l ∈ L)
            → Γ ⊢ (f l ins) ⇓ Sigma A B
            → Γ ⊢ CaseT U f ⇓ Sigma A B
  AUCaseX-P : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Pi (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (UVar{x = length Γ'}) fᴬ ⇓ Pi (CaseT (UVar{x = length Γ'}) fᴮ) (CaseT (UVar{x = ℕ.suc (length Γ')}) fᶜ)
  AUCaseX-S : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
            → Γ ⊢ D ≤ᵀ Label L
            → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)
            → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ Single (VLab{x = l}) , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Sigma (fᴮ l i) (fᶜ l i))
            → Θ ⊢ CaseT (UVar{x = length Γ'}) fᴬ ⇓ Sigma (CaseT (UVar{x = length Γ'}) fᴮ) (CaseT (UVar{x = ℕ.suc (length Γ')}) fᶜ)            
  AUCaseXDyn-P : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                 → Γ ⊢ D ≤ᵀ Label L
                 → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)  
                 → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l})) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Pi (fᴮ l i) (fᶜ l i))
                 → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴬ ⇓ Pi (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L'}) fᴮ) (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L'}) fᶜ)
  AUCaseXDyn-S : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L L' : Subset n} {sub : L' ⊆ L} {fᴬ : (∀ l → l ∈ L → Ty {n})} {fᴮ fᶜ : (∀ l → l ∈ L' → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                 → Γ ⊢ D ≤ᵀ Label L
                 → (∀ l → l ∈ L' → Γ ⊢ Single (VLab{x = l}) ≤ᵀ D)  
                 → (∀ l → (i : l ∈ L') → (Γ' ++ ⟨ ( (cast (Single (VLab{x = l})) (Label ⁅ l ⁆) D)) , Γ ⟩) ⊢ (fᴬ l (sub i)) ⇓ Sigma (fᴮ l i) (fᶜ l i))
                 → Θ ⊢ CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L}) fᴬ ⇓ Sigma (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L'}) fᴮ) (CaseT (UVarCast{x = length Γ'}{A = D}{B = Label L'}) fᶜ)

{-
------------------------------------------------------------------------
-- Implementation of above rules

access-env : {n : ℕ} → (m : ℕ) → (Γ : TEnv {n}) → Maybe (∃[ T ]( m ∶ T ∈ Γ ))
access-env {n} m [] = nothing
access-env {n} zero ⟨ T , Γ ⟩ = just (T , here)
access-env {n} (ℕ.suc m) ⟨ T , Γ ⟩
  with access-env m Γ
...  | nothing = nothing
...  | just (fst , snd) = just (fst , (there snd))

-- Γ , x : A , Δ
env-replace : {n : ℕ} → (m : ℕ) → TEnv {n} → Ty {n} → TEnv {n}
env-replace {n} m [] A = []
env-replace {n} zero ⟨ T , Γ ⟩ A = ⟨ A , Γ ⟩
env-replace {n} (ℕ.suc m) ⟨ T , Γ ⟩ A = ⟨ T , env-replace m Γ A ⟩

-- split environment, after m
-- proj₁ env-split 1 ⟨ UnitT , ⟨ Bot , [] ⟩ ⟩ = ⟨ Unit , [] ⟩ 
env-split : {n : ℕ} → (m : ℕ) → TEnv {n} → TEnv {n} × TEnv {n}
env-split {n} m [] = [] , []
env-split {n} zero ⟨ T , Γ ⟩ = [] , ⟨ T , Γ ⟩
env-split {n} (ℕ.suc m) ⟨ T , Γ ⟩
  with env-split m Γ
...  | Γ' , Γ'' = ⟨ T , Γ' ⟩ , Γ''

-- example
env1 : TEnv {42}
env1 = ⟨ UnitT , ⟨ Bot , [] ⟩ ⟩

env2 : TEnv {42}
env2 = proj₁ (env-split 1 (env-replace 0 env1 (Single VUnit)))

_ : env2 ≡ ⟨ Single VUnit , [] ⟩
_ = refl

_⊢_⇓ : {n : ℕ} → TEnv {n} → Ty {n} → Ty {n}

_⊢_◁ : {n : ℕ} → TEnv {n} → Exp {n} → Ty {n}

_,_⊢_≤ᵀ?_ : {n : ℕ} → (Γ : TEnv {n}) → ⊢ Γ ok → (A B : Ty {n}) → Maybe (Γ ⊢ A ≤ᵀ B)

-- Left to right update of a map, update depending on the index
updateMap : ∀ {a} {n} {A : Set a} → (Fin n → A → A) → Vec A n → Vec A n
updateMap f [] = []
updateMap {a} {ℕ.suc n} f (x ∷ xs) = f zero x ∷ updateMap (λ x₁ x₂ → f (Fin.suc x₁) x₂) xs

-- example
ve : Vec ℕ 3
ve = 4 ∷ 3 ∷ 2 ∷ []

ve' : Vec ℕ 3
ve' = updateMap (λ x y → y +ᴺ (toℕ x)) ve

_ : ve' ≡ 4 ∷ 4 ∷ 4 ∷ []
_ = refl

-- L' = {l ∈ L ∣ Γ ⊢ S{l} ≤ D}
helper : {n : ℕ} → (Γ : TEnv {n}) → ⊢ Γ ok → Ty {n} → Fin n → Side → Side
helper {n} Γ Γ-ok D m outside = outside
helper {n} Γ Γ-ok D m inside
  with Γ , Γ-ok ⊢ Single (VLab{x = m}) ≤ᵀ? D
...  | nothing = outside
...  | just fst = inside

get-single-label-subset : {n : ℕ} → (Γ : TEnv {n}) → ⊢ Γ ok → (D : Ty {n}) → (L : Subset n) → Subset n   
get-single-label-subset {n} Γ Γ-ok D L = updateMap (helper Γ Γ-ok D) L

-- Apply function to elements that are in a subset
-- Result is the same subset with "inside" elements updated
updateMapSubset : ∀ {a} {n} {B : Set a} → ((l : Fin n) → B) → Vec Side n → Vec (Side ⊎ B) n
updateMapSubset {a} {.0} {B} f [] = []
updateMapSubset {a} {ℕ.suc n} {B} f (outside ∷ xs) = (inj₁ outside) ∷ (updateMapSubset (λ x → f (Fin.suc x)) xs)
updateMapSubset {a} {ℕ.suc n} {B} f (inside ∷ xs) = (inj₂ (f zero)) ∷ (updateMapSubset (λ x → f (Fin.suc x)) xs)

notNothing : ∀ {n} {L : Subset n} → {A : Set} → (f : (l : Fin n) → l ∈ L → Maybe A) → (l : Fin n) → (i : l ∈ L) → Dec (Is-just (f l i))
notNothing {n} {L} {A} f l i
  with f l i
...  | nothing = no λ ()
...  | just x = yes (just Data.Unit.tt)

{-
dec-manipulate : {n : ℕ} {A : Set} → (dec : (a a' : A) → Dec (a ≡ a')) → ((a a' : A ⊎ ⊤) → Dec (a ≡ a'))
dec-manipulate {n} {A} dec (inj₁ x) (inj₁ x₁)
  with dec x x₁
...  | yes p = yes (cong inj₁ p)
...  | no ¬p = no λ x₂ → contradiction (sum-eq x₂) ¬p
dec-manipulate {n} {A} dec (inj₁ x) (inj₂ y) = no λ ()
dec-manipulate {n} {A} dec (inj₂ y) (inj₁ x) = no λ ()
dec-manipulate {n} {A} dec (inj₂ tt) (inj₂ tt) = yes (cong inj₂ refl)

f-manipulate : {n : ℕ} {A : Set} {s : Subset n} → ((l : Fin n) → l ∈ s → A) → (Fin n → (A ⊎ ⊤))
f-manipulate {n} {A} {s} f l
  with l ∈? s
...  | yes p = inj₁ (f l p)
...  | no ¬p = inj₂ tt

f-equal : {n : ℕ} {A : Set} {dec : (a a' : A) → Dec (a ≡ a')} → (f f' : (l : Fin n) → A) → Dec (f ≡ f')
f-equal {n} {A} {dec} f f'
  with all?{n} λ x → dec (f x) (f' x)
...  | yes p = yes (ext p)
...  | no ¬p = no λ x → contradiction (cong-app x) ¬p
-}


-- If one result is nothing, all is nothing.
subsetMaybe : ∀ {n} {L : Subset n} {A : Set} → ((l : Fin n) → (i : l ∈ L) → Maybe A) → Maybe ((l : Fin n) → (i : l ∈ L) → A)
subsetMaybe {n} {L} {A} f = {!!}

{-
data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
-}

data _[_]∶_ {A B : Set} : ∀ {n} → Vec (A ⊎ B) n → Fin n → Set → Set where
  here-inj₁ : ∀ {n} {x} {xs : Vec (A ⊎ B) n} → ((inj₁ x) ∷ xs) [ zero ]∶ A
  here-inj₂ : ∀ {n} {x} {xs : Vec (A ⊎ B) n} → ((inj₂ x) ∷ xs) [ zero ]∶ B
  there-inj₁ : ∀ {n} {i} {y} {xs : Vec (A ⊎ B) n}
            (xs[i]∶x : xs [ i ]∶ A) → (y ∷ xs) [ Fin.suc i ]∶ A
  there-inj₂ : ∀ {n} {i} {y} {xs : Vec (A ⊎ B) n}
            (xs[i]∶x : xs [ i ]∶ B) → (y ∷ xs) [ Fin.suc i ]∶ B

-- Function on subset to vector, vector to function on subset
funcToVec : {n : ℕ} {A : Set} {L : Subset n} → ((l : Fin n) → l ∈ L → A) → Vec (Side ⊎ A) n
funcToVec {n} {A} {L} f = {!!}

-- vecToFunc : {n : ℕ} {A : Set} → (vec : Vec (Side ⊎ A) n) → ((l : Fin n) → 
-- apply function to every element in Subset, return function mapping each element to result

_,_⊢_▷ : {n : ℕ} → (Γ : TEnv {n}) → ⊢ Γ ok → (M : Exp {n}) → Maybe (∃[ T ](Γ ⊢ M ▷ T))
_,_⊢_▷ {n} Γ Γ-ok (Var x)
  with access-env x Γ
...  | nothing = nothing
...  | just (fst , snd) = just (fst , (VarA Γ-ok snd))
_,_⊢_▷ {n} Γ Γ-ok UnitE = just (Single VUnit , UnitAI Γ-ok)
_,_⊢_▷ {n} Γ Γ-ok (LabI x) = just ((Single VLab) , (LabAI Γ-ok))
_,_⊢_▷ {n} Γ Γ-ok Blame = just (Bot , (BlameA Γ-ok))

_,_⊢_▷ {n} Γ Γ-ok (ProdV{e = N} x M) = {!!}

_,_⊢_▷ {n} Γ Γ-ok (Abs M) = {!!}
_,_⊢_▷ {n} Γ Γ-ok (Prod M M₁) = {!!}

_,_⊢_▷ {n} Γ Γ-ok (App M M₁) = {!!}

_,_⊢_▷ {n} Γ Γ-ok (LetP M M₁) = {!!}
_,_⊢_▷ {n} Γ Γ-ok (LetE M M₁) = {!!}

_,_⊢_▷ {n} Γ Γ-ok (Cast M A B)
  with Γ , Γ-ok ⊢ M ▷    -- | Γ ⊢ A ok | Γ ⊢ B ok
...  | nothing = nothing
...  | just (fst , snd) = just ((cast fst A B) , (CastA snd))

_,_⊢_▷ {n} Γ Γ-ok (CaseE{s = L}{e = e} x f)
  with Γ , Γ-ok ⊢ e ▷
...  | nothing = nothing
...  | just (fst , snd)
     with fst
...     | Bot = just (Bot , (LabAEl-Bot snd))
...     | Single (VLab{x = l})
        with l ∈? L
...        | no ¬ins = nothing
...        | yes ins
           with Γ , Γ-ok ⊢ (f l ins) ▷
...           | nothing = nothing
...           | just (fst' , snd') = just (fst' , (LabAEl snd ins snd'))
_,_⊢_▷ {n} Γ Γ-ok (CaseE{s = L}{e = e} x f) | just (fst , snd) | D
  with x
_,_⊢_▷ {n} Γ Γ-ok (CaseE{s = L}{e = e} x f) | just (fst , snd) | D | UVar
  with Γ , Γ-ok ⊢ D ≤ᵀ? Label L
...  | nothing = nothing
...  | just fst'
     with get-single-label-subset Γ Γ-ok D L
...     | L'
        with (subsetMaybe {n} {L} {} (λ l i → (env-replace (toℕ l) Γ (Single (VLab{x = l}))) , ?  ⊢ (f l i) ▷))
...        | blub = ?        
_,_⊢_▷ {n} Γ Γ-ok (CaseE{s = L}{e = e} x f) | just (fst , snd) | D | UVarCast = {!!}
_,_⊢_▷ {n} Γ Γ-ok (CaseE{s = L}{e = e} x f) | just (fst , snd) | D | _ = nothing  

-- subsetMaybe : ∀ {n} {L : Subset n} {A : Set} → ((l : Fin n) → (i : l ∈ L) → Maybe A) → Maybe ((l : Fin n) → (i : l ∈ L) → A)

-- extract deepest cast expression
extr-cast : {n : ℕ} → Exp {n} → Exp {n}
extr-cast {n} (Var x) = Var x
extr-cast {n} UnitE = UnitE
extr-cast {n} Blame = Blame
extr-cast {n} (Abs e) = Abs e
extr-cast {n} (App e e₁) = App e e₁
extr-cast {n} (LabI x) = LabI x
extr-cast {n} (CaseE x f) = CaseE x f
extr-cast {n} (Prod e e₁) = Prod e e₁
extr-cast {n} (ProdV x e) = ProdV x e
extr-cast {n} (LetP e e₁) = LetP e e₁
extr-cast {n} (LetE e e₁) = LetE e e₁
extr-cast {n} (Cast e x x₁) = extr-cast e

-}
------------------------------------------------------------------------
-- Cast function, requires big step semantics, which will be defined later


-- Required for big step semantics
Env : {ℕ} → Set
Env {n} = List (Exp {n})

-- Evaluation results
data Result {n : ℕ} : Exp {n} → Set where
  RValue : {e : Exp {n}} → Val {n} e → Result {n} e
  RBlame :  Result {n} Blame
  RStuck : {e : Exp {n}} → Result {n} e
  
_∶_⇓ : {n : ℕ} {Γ : Env {n}} (venv : All Val Γ) (e : Exp {n}) → Σ (Exp {n}) Result

-- Cast function
cast (Single{e = e} x) B C
  with [] ∶ (Cast e B C) ⇓
...  | fst , RValue x₁ = Single x₁
...  | .Blame , RBlame = Bot
...  | fst , RStuck = C

cast Bot B C = C
cast UnitT B C = C
cast Dyn B C = C
cast (Label x) B C = C
cast (Pi A A₁) B C = C
cast (Sigma A A₁) B C = C
cast (CaseT x f) B C = C

------------------------------------------------------------------------
-- Lemma for casting and judgement

-- result of cast A A' C is either singleton, just C or Bot
cast-result : {n : ℕ} {A' A B : Ty {n}} → ((cast A' A B) ≡ B) ⊎ (∃[ e ](∃[ V ]((cast A' A B) ≡ Single{e = e} V))) ⊎ ((cast A' A B) ≡ Bot)
cast-result {n} {Single{e = e} x} {A} {B}
  with [] ∶ Cast e A B ⇓
...  | fst , RValue x₁ = inj₂ (inj₁ (fst , (x₁ , refl)))
...  | fst , RStuck = inj₁ refl
...  | Blame , RBlame = inj₂ (inj₂ refl)

cast-result {n} {Bot} {A} {B} = inj₁ refl
cast-result {n} {UnitT} {A} {B} = inj₁ refl
cast-result {n} {Dyn} {A} {B} = inj₁ refl
cast-result {n} {Label x} {A} {B} = inj₁ refl
cast-result {n} {Pi A' A''} {A} {B} = inj₁ refl
cast-result {n} {Sigma A' A''} {A} {B} = inj₁ refl
cast-result {n} {CaseT x f} {A} {B} = inj₁ refl

{-
-- only 2 possible types for expressions (V : T ⇒ *)
cast-dyn : {n : ℕ} {e : Exp {n}} {T A : Ty {n}} → [] ⊢ Cast e T Dyn ▷ A → Val e → (∃[ e ](∃[ W ]( A ≡ Single{e = e} W ))) ⊎ A ≡ Dyn
cast-dyn {n} {e} {T} {A} (CastA{A' = A'} j x) V = {!!}
--  with cast-result{A' = A'}{A = T}{B = Dyn} x
-- ...  | inj₁ x₂ = ?
-- ...  | inj₂ (fst , snd , thd) = ?

--
no-single-lemma : {n : ℕ} {e e' : Exp {n}} {V : Val e} {W : Val e'} → [] ⊢ e ▷ Single W → (∃[ l ]( e ≡ LabI l )) ⊎ ( e ≡ UnitE ) ⊎ (∃[ e'' ](∃[ A ](∃[ B ]( e ≡ Cast e'' A B ))))
no-single-lemma {n} {(Cast e'' A B)} {e'} {V} {W} (CastA j x) = inj₂ (inj₂ (e'' , (A , (B , refl)))) 
no-single-lemma {n} {.UnitE} {.UnitE} {V} {.VUnit} (UnitAI x) = inj₂ (inj₁ refl)
no-single-lemma {n} {(LabI l)} {.(LabI _)} {V} {.VLab} (LabAI x) = inj₁ (l , refl)

no-single : {n : ℕ} {e e' : Exp {n}} {V : Val e} {W : Val e'} → ¬ ((∃[ l ]( e ≡ LabI l )) ⊎ ( e ≡ UnitE ) ⊎ (∃[ e'' ](∃[ A ](∃[ B ]( e ≡ Cast e'' A B ))))) → ¬ ([] ⊢ e ▷ Single W)
no-single = contraposition no-single-lemma

cast-dyn-no-single-lemma : {n : ℕ} {e e' : Exp {n}} {V : Val e} {W : Val e'} {T : Ty {n}} → [] ⊢ Cast e T Dyn ▷ Single W → (∃[ l ]( e ≡ LabI l )) ⊎ ( e ≡ UnitE ) ⊎ (∃[ e'' ](∃[ A ](∃[ B ]( e ≡ Cast e'' A B ))))
cast-dyn-no-single-lemma {n} {e} {e'} {V} {W} {T} j = {!!}


cast-dyn-no-single : {n : ℕ} {e e' : Exp {n}} {V : Val e} {W : Val e'} {T : Ty {n}} → ¬ ((∃[ l ]( e ≡ LabI l )) ⊎ ( e ≡ UnitE ) ⊎ (∃[ e'' ](∃[ A ](∃[ B ]( e ≡ Cast e'' A B ))))) → [] ⊢ Cast e T Dyn ▷ Dyn
cast-dyn-no-single {n} {UnitE} {e'} {V} {W} neq = {!neq (inj₂ (inj₁ refl))!}
cast-dyn-no-single {n} {LabI x} {e'} {V} {W} neq = {!!}
cast-dyn-no-single {n} {Cast e x x₁} {e'} {V} {W} neq = {!!}

cast-dyn-no-single {n} {Abs e} {e'} {V} {W} neq = CastA {!!} {!!}
cast-dyn-no-single {n} {ProdV x e} {e'} {V} {W} neq = {!!}

--
cast-dyn-synt : {n : ℕ} {e : Exp {n}} {G : Ty {n}} → (V : Val e) → (tyg : TyG G) → ([] ⊢ Cast e G Dyn ▷ Single (VCast V tyg)) ⊎ ([] ⊢ Cast e G Dyn ▷ Dyn)
cast-dyn-synt {n} {UnitE} {G} V tyg = inj₁ (CastA (UnitAI empty) {!!})
cast-dyn-synt {n} {Abs e} {G} V tyg = inj₂ (CastA {!!} {!!})
cast-dyn-synt {n} {LabI x} {G} V tyg = {!!}
cast-dyn-synt {n} {ProdV x e} {G} V tyg = {!!}
cast-dyn-synt {n} {Cast e x x₁} {G} V tyg = {!!}
-}

------------------------------------------------------------------------
-- Type normal form

data TyNf {n : ℕ} : Ty {n} → Set where
  NfDyn : TyNf Dyn
  NfUnit : TyNf UnitT
  NfLabel : {s : Subset n} → TyNf (Label s)
  NfPi : {A B : Ty {n}} → TyNf (Pi A B)
  NfSigma : {A B : Ty {n}} → TyNf (Sigma A B)
  NfSingle : {e : Exp {n}} {V : Val e} {A : Ty {n}} → [] ⊢ e ▷ A → TyB A → TyNf (Single V)

-- Predicate
TyNf?_ : {n : ℕ} → (A : Ty {n}) → Dec (TyNf A)
TyNf? Bot = no λ ()
TyNf? CaseT x f = no λ ()

TyNf? UnitT = yes NfUnit
TyNf? Dyn = yes NfDyn
TyNf? Label x = yes NfLabel
TyNf? Pi A A₁ = yes NfPi
TyNf? Sigma A A₁ = yes NfSigma

TyNf? Single VUnit = yes (NfSingle (UnitAI empty) BSingleUnit)
TyNf? Single VLab = yes (NfSingle (LabAI empty) BSingleLab)
TyNf? Single (VCast {e = UnitE} x x₁) = {!!}
TyNf? Single (VCast {e = LabI x₂} x x₁) = {!!}

TyNf? Single (VCast {e = Cast e x₂ x₃} x x₁) = {!!}

TyNf? Single (VCast {e = Abs e} x x₁) = yes (NfSingle {!!} {!!})
TyNf? Single (VCast {e = ProdV x₂ e} x x₁) = {!ye!}

TyNf? Single VFun = no {!!}
TyNf? Single (VProd x x₁) = {!!}
TyNf? Single (VCastFun x) = {!!}

------------------------------------------------------------------------
-- Cast function, big step semantics

b-◁ : {n : ℕ} {T : Ty {n}} {e : Exp {n}} → Val e → TyB T → notSingle T → Dec ([] ⊢ e ▷ T)
b-◁ {n} {.UnitT} {.UnitE} VUnit BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.UnitE} VUnit BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.UnitE} VUnit BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.UnitE} VUnit BSingleUnit b = yes (UnitAI empty)
b-◁ {n} {.UnitT} {.(LabI _)} VLab BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(LabI _)} VLab BLabel b = no λ ()
b-◁ {n} {(Single (VLab{x = x}))} {(LabI l)} VLab BSingleLab b 
  with x Data.Fin.≟ l
... | yes eq rewrite eq = yes (LabAI{l = l} empty)
... | no ¬eq = {!!}
b-◁ {n} {.(Single VUnit)} {.(LabI _)} VLab BSingleUnit b = no λ ()
b-◁ {n} {.UnitT} {.(Abs _)} VFun BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(Abs _)} VFun BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.(Abs _)} VFun BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.(Abs _)} VFun BSingleUnit b = no λ ()
b-◁ {n} {.UnitT} {.(ProdV V _)} (VProd V V₁) BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(ProdV V _)} (VProd V V₁) BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.(ProdV V _)} (VProd V V₁) BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.(ProdV V _)} (VProd V V₁) BSingleUnit b = no λ ()
b-◁ {n} {A} {Cast e G Dyn} (VCast V x) bA b = no (ϱ A bA b)
  where
  ϱ : (A' : Ty) → (bA' : TyB A') → notSingle A' → ¬ ([] ⊢ Cast e G Dyn ▷ A')
  ϱ A' bA' (notsingle ns) j = {!!}
{-    with cast-lemma-3 {n} {e} {A'} {G} {Dyn} V j
  ...  | inj₁ eq
       with bA'
  ...     | BUnit = contradiction eq (λ ())
  ...     | BLabel = contradiction eq (λ ())
  ...     | BSingleLab = contradiction eq (λ ())
  ...     | BSingleUnit = contradiction eq (λ ())
  ϱ A' bA' (notsingle ns) j | inj₂ (fst , fst₁ , snd)
       with bA'
  ...     | (BSingleLab{l = l}) = contradiction refl (ns (LabI l) VLab)
  ...     | BSingleUnit = contradiction refl (ns UnitE VUnit) -}
b-◁ {n} {A} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun V) b = {!!} -- analogous to case above

_▷ : {n : ℕ} {T : Ty {n}} → TyNf T × T ≢ Dyn → ∃[ T' ](TyG{n} T')
_▷ {n} {.Dyn} (NfDyn , ndyn) = contradiction refl ndyn
_▷ {n} {.UnitT} (NfUnit , ndyn) = UnitT , GUnit
_▷ {n} {(Label L)} (NfLabel , ndyn) = Label L , GLabel
_▷ {n} {(Pi A B)} (NfPi , ndyn) = (Pi Dyn Dyn) , GPi
_▷ {n} {(Sigma A B)} (NfSigma , ndyn) = (Sigma Dyn Dyn) , GSigma
_▷ {n} {Single V} (NfSingle j b , ndyn) = (Single V) , GSingle

g-≤? : {n : ℕ} {A B : Ty {n}} → TyG A → TyG B → Dec ([] ⊢ A ≤ᵀ B)
-- only ASubSingleSingle, only if V = W
g-≤? {n} {(Single V)} {(Single W)} GSingle GSingle = {!!}

-- ASubSingle applicable, if V has correct type => requires type check & synthesis
g-≤? {n} {(Single V)} {.UnitT} GSingle GUnit
  with b-◁ V BUnit (notsingle (λ e W → λ ()))
...  | yes p = yes (ASubSingle (SubTypeA p ASubUnit) BUnit (notsingle (λ e W → λ ())))
...  | no ¬p = {!!}
g-≤? {n} {(Single V)} {(Label L)} GSingle GLabel = {!!}

-- not base types, ASubSingle not applicable
g-≤? {n} {.(Single _)} {.(Pi Dyn Dyn)} GSingle GPi = {!!}
g-≤? {n} {.(Single _)} {.(Sigma Dyn Dyn)} GSingle GSigma = {!!}

g-≤? {n} {.UnitT} {.UnitT} GUnit GUnit = yes ASubUnit
g-≤? {n} {(Label s)} {(Label s')} GLabel GLabel
  with s ⊆? s'
...  | yes sub = yes (ASubLabel sub)
...  | no ¬sub = no ϱ
     where ϱ : ¬ ([] ⊢ Label s ≤ᵀ Label s')
           ϱ (ASubLabel sub) = contradiction (λ {x} → sub{x}) ¬sub
g-≤? {n} {.(Pi Dyn Dyn)} {.(Pi Dyn Dyn)} GPi GPi = yes (ASubPi ASubDyn ASubDyn)
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Sigma Dyn Dyn)} GSigma GSigma = yes (ASubSigma ASubDyn ASubDyn)

g-≤? {n} {.UnitT} {.(Single _)} GUnit GSingle = no (λ ())
g-≤? {n} {.UnitT} {.(Label _)} GUnit GLabel = no (λ ())
g-≤? {n} {.UnitT} {.(Pi Dyn Dyn)} GUnit GPi = no (λ ())
g-≤? {n} {.UnitT} {.(Sigma Dyn Dyn)} GUnit GSigma = no (λ ())
g-≤? {n} {.(Label _)} {.(Single _)} GLabel GSingle = no (λ ())
g-≤? {n} {.(Label _)} {.UnitT} GLabel GUnit = no (λ ())
g-≤? {n} {.(Label _)} {.(Pi Dyn Dyn)} GLabel GPi = no (λ ())
g-≤? {n} {.(Label _)} {.(Sigma Dyn Dyn)} GLabel GSigma = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Single _)} GPi GSingle = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.UnitT} GPi GUnit = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Label _)} GPi GLabel = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Sigma Dyn Dyn)} GPi GSigma = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Single _)} GSigma GSingle = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.UnitT} GSigma GUnit = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Label _)} GSigma GLabel = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Pi Dyn Dyn)} GSigma GPi = no (λ ())

------------------------------------------------------------------------
-- Cast function, big step semantics

-- Type results
data TResult {n : ℕ} : Ty {n} → Set where
  RNf : {T : Ty {n}} → TyNf T → TResult T
  RBot : TResult Bot
  RStuck : {T : Ty {n}} → TResult T
  
access : {n : ℕ} {Γ : Env {n}} → (m : ℕ) → All Val Γ → Σ (Exp {n}) Result
access {n} {.[]} m [] = Blame , RStuck
access {n} {(e ∷ Γ)} zero (px ∷ venv) = (e , RValue px)
access {n} {.(_ ∷ _)} (ℕ.suc m) (px ∷ venv) = access m venv

-- Big step semantics for expressions and types, cast reduction

_∶_⇓ᵀ : {n : ℕ} {Γ : Env {n}} (venv : All Val Γ) (T : Ty {n}) → Σ (Ty {n}) TResult
castreduce : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → Val e → TyNf A → TyNf B → Σ (Exp {n}) Result

venv ∶ Bot ⇓ᵀ = Bot , RBot
venv ∶ UnitT ⇓ᵀ = UnitT , RNf NfUnit
venv ∶ Dyn ⇓ᵀ = Dyn , RNf NfDyn
venv ∶ Label x ⇓ᵀ = Label x , RNf NfLabel
venv ∶ Pi T T₁ ⇓ᵀ = Pi T T₁ , RNf NfPi
venv ∶ Sigma T T₁ ⇓ᵀ = Sigma T T₁ , RNf NfSigma

venv ∶ CaseT{s = s}{e = e} x f ⇓ᵀ
  with venv ∶ e ⇓
...  | .Blame , RBlame = Bot , RBot
...  | fst , RStuck = CaseT x f , RStuck
...  | fst , RValue x₁
     with x₁
...     | VUnit = CaseT x f , RStuck
...     | VFun = CaseT x f , RStuck
...     | VProd value value₁ = CaseT x f , RStuck
...     | VCast value x₂ = CaseT x f , RStuck
...     | VCastFun value = CaseT x f , RStuck
...     | (VLab{x = l})
        with l ∈? s
...        | yes ins = venv ∶ (f l ins) ⇓ᵀ
...        | no ¬ins = CaseT x f , RStuck

venv ∶ Single x ⇓ᵀ
  with TyNf? (Single x)
...  | yes tynf = Single x , RNf tynf
...  | no ¬tynf = Single x , RStuck

-- check whether Single x is in NF => whether type of x is base type
-- what happens if its not in NF? Stuck?


venv ∶ Var x ⇓ = access x venv
venv ∶ UnitE ⇓ = UnitE , (RValue VUnit)
venv ∶ Blame ⇓ = Blame , RBlame
venv ∶ Abs e ⇓ = (Abs e) , (RValue VFun)
venv ∶ LabI x ⇓ = (LabI x) , (RValue VLab)

venv ∶ App e e₁ ⇓
  with venv ∶ e ⇓
...  | fst , RStuck = fst , RStuck  
...  | .Blame , RBlame = Blame , RBlame
...  | UnitE , RValue x = App UnitE e₁ , RStuck
...  | LabI x₁ , RValue x = App (LabI x₁) e₁ , RStuck
...  | ProdV x₁ fst , RValue x = App (ProdV x₁ fst) e₁ , RStuck

... | Cast e' x₁ .Dyn , RValue (VCast x x₂) = Cast e' x₁ Dyn , RStuck -- ?
... | Cast e' (Pi A B) (Pi A' B') , RValue (VCastFun x)
     with venv ∶ e₁ ⇓
...     | fst' , RValue y = venv ∶ LetE (Cast fst' A' A) (Cast (App e' (Var 0)) B ([ 0 ↦ y ]ᵀ B')) ⇓
...     | .Blame , RBlame = Blame , RBlame
...     | fst' , RStuck = App (Cast e' (Pi A B) (Pi A' B')) fst' , RStuck 
venv ∶ App e e₁ ⇓ | Abs fst , RValue (VFun)
     with venv ∶ e₁ ⇓
...     | fst' , RValue x₁ = (x₁ ∷ venv) ∶ fst ⇓ 
...     | .Blame , RBlame = Blame , RBlame
...     | fst' , RStuck = (App (Abs fst) fst') , RStuck

venv ∶ Prod e e₁ ⇓
  with venv ∶ e ⇓
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = (Prod fst e₁) , RStuck
...  | fst , RValue x
     with venv ∶ e₁ ⇓
...     | fst' , RValue x₁ = (ProdV x fst') , (RValue (VProd x x₁))
...     | .Blame , RBlame = Blame , RBlame
...     | fst' , RStuck = ProdV x fst' , RStuck 

venv ∶ ProdV x e ⇓
  with venv ∶ e ⇓
...  | fst , RValue x₁ = (ProdV x fst) , (RValue (VProd x x₁))
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = ProdV x fst , RStuck

venv ∶ LetE e e₁ ⇓
  with venv ∶ e ⇓
...  | fst , RValue x = (x ∷ venv) ∶ e₁ ⇓
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = LetE fst e₁ , RStuck

venv ∶ LetP e e₁ ⇓
  with venv ∶ e ⇓
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = LetP fst e₁ , RStuck
...  | .UnitE , RValue VUnit = LetP UnitE e₁ , RStuck
...  | (LabI l) , RValue VLab = LetP (LabI l) e₁ , RStuck 
...  | (Abs e') , RValue VFun = LetP (Abs e') e₁ , RStuck
...  | (Cast e' A Dyn) , RValue (VCast x x₁) = LetP (Cast e' A Dyn) e₁ , RStuck
...  | (Cast e' (Pi A B) (Pi A' B')) , RValue (VCastFun x) = LetP (Cast e' (Pi A B) (Pi A' B')) e₁ , RStuck
...  | (ProdV x v) , RValue (VProd x x₁) = ((x₁ ∷ (x ∷ venv))) ∶ e₁ ⇓

venv ∶ CaseE{s = s} x f ⇓
  with x
...  | UBlame = Blame , RBlame

-- access environment
...  | (UVar{x = y})
     with access y venv
...     | .Blame , RBlame = Blame , RBlame
...     | fst , RStuck = CaseE x f , RStuck
...     | fst , RValue val = venv ∶ CaseE (val⊂valu val) f ⇓ 
venv ∶ CaseE x f ⇓ | (UVarCast{x = y}{A = A}{B = B})
-- access environment, casting might be necessary
     with access y venv
...     | .Blame , RBlame = Blame , RBlame
...     | fst , RStuck = CaseE x f , RStuck
...     | fst , RValue v
        with venv ∶ (Cast fst A B) ⇓
...        | .Blame , RBlame = Blame , RBlame
...        | fst' , RStuck = CaseE (UVarCast{x = y}{A = A}{B = B}) f , RStuck
...        | fst' , RValue val = venv ∶ CaseE (val⊂valu val) f ⇓ 

venv ∶ CaseE x f ⇓ | UValUnit = CaseE UValUnit f , RStuck
venv ∶ CaseE x f ⇓ | (UValFun{N = N}) = CaseE (UValFun{N = N}) f , RStuck
venv ∶ CaseE x f ⇓ | UValProd v x₁ = CaseE (UValProd v x₁) f , RStuck
venv ∶ CaseE{s = s} x f ⇓ | (UValLab{x = l})
  with l ∈? s
...  | yes p = venv ∶ f l p ⇓ 
...  | no ¬p = CaseE (UValLab{x = l}) f , RStuck

venv ∶ CaseE x f ⇓ | (UValCast{e = e}{A = A}{B = B} x₁)
  with venv ∶ (Cast e A B) ⇓
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = CaseE (UValCast{A = A}{B = B} x₁) f , RStuck
...  | fst , RValue val = venv ∶ CaseE (val⊂valu val) f ⇓

venv ∶ Cast e A B ⇓
  with venv ∶ e ⇓
...  | .Blame , RBlame = Blame , RBlame
...  | fst , RStuck = Cast fst A B , RStuck
...  | fst , RValue x
     with venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ
...     | .Bot , RBot | nfB =  fst , RValue x -- Bot is subtype of all types, hence Cast-Sub applicable   
...     | A' , RNf nfA' | .Bot , RBot = Blame , RBlame -- No type (except bot, see above) is subtype of bot, hence Cast-Fail applicable
...     | A' , RNf nfA' | B' , RNf nfB' = castreduce x nfA' nfB'


castreduce {n} {e} {.Dyn} {B} val NfDyn nfB
  with B ≡ᵀ? Dyn
...  | yes p = e , RValue val
...  | no ¬p
     with val
...     | VUnit = Cast e Dyn B , RStuck
...     | VLab = Cast e Dyn B , RStuck
...     | VFun = Cast e Dyn B , RStuck
...     | VProd v v₁ = Cast e Dyn B , RStuck
...     | VCastFun v = Cast e Dyn B , RStuck
...     | VCast{e = e'} val' tygA
        with TyG? B
...        | no ¬tygB = Cast e Dyn B , RStuck
...        | yes tygB
           with g-≤? tygA tygB
...           | yes leq = e' , RValue val'  -- Cast-Collapse
...           | no ¬leq = Blame , RBlame -- Cast-Collide

castreduce {n} {e} {.UnitT} {B} val NfUnit nfB
  with nfB
...  | NfLabel = Blame , RBlame
...  | NfPi = Blame , RBlame
...  | NfSigma = Blame , RBlame
...  | NfSingle x x₁ = Blame , RBlame
...  | NfDyn = Cast e UnitT Dyn , RValue (VCast val GUnit)
...  | NfUnit = e , RValue val -- Cast-Sub, Unit ≤ᵀ Unit

castreduce {n} {e} {Label s} {C} val NfLabel nfC
  with nfC
...  | NfUnit = Blame , RBlame
...  | NfPi = Blame , RBlame
...  | NfSigma = Blame , RBlame
...  | NfSingle x x₁ = Blame , RBlame
...  | NfDyn = Cast e (Label s) Dyn , RValue (VCast val GLabel)
...  | (NfLabel{s = s'})
     with s ⊆? s'
...     | yes subs = e , RValue val
...     | no ¬subs = Blame , RBlame

castreduce {n} {e} {Pi A B} {C} val NfPi nfC
  with nfC
...  | NfUnit = Blame , RBlame
...  | NfLabel = Blame , RBlame
...  | NfSigma = Blame , RBlame
...  | NfSingle x x₁ = Blame , RBlame
...  | NfDyn
     with (TyG? (Pi A B))
...     | yes p = Cast e (Pi A B) Dyn , RValue (VCast val p)
...     | no ¬p = Blame , RBlame
castreduce {n} {e} {Pi A B} {Pi A' B'} val NfPi NfPi | NfPi = Cast e (Pi A B) (Pi A' B') , RValue (VCastFun val)

castreduce {n} {e} {Sigma A B} {C} val NfSigma nfC
  with nfC
...  | NfUnit = Blame , RBlame
...  | NfLabel = Blame , RBlame
...  | NfPi = Blame , RBlame
...  | NfSingle x x₁ = Blame , RBlame
...  | NfDyn
     with TyG? (Sigma A B)
...     | yes tyg = Cast e (Sigma A B) Dyn , RValue (VCast val tyg)
...     | no ¬tyg = Blame , RBlame
castreduce {n} {e} {Sigma A B} {Sigma A' B'} val NfSigma NfSigma | NfSigma
  with val
...  | VUnit = Cast e (Sigma A B) (Sigma A' B') , RStuck
...  | VLab = Cast e (Sigma A B) (Sigma A' B') , RStuck
...  | VFun = Cast e (Sigma A B) (Sigma A' B') , RStuck
...  | VCast value x = Cast e (Sigma A B) (Sigma A' B') , RStuck
...  | VCastFun value = Cast e (Sigma A B) (Sigma A' B') , RStuck
...  | VProd{e = e₁}{e' = e₁'} value value₁ = {!!} ∶ Prod (Cast e₁ A A') (Cast e₁' B B') ⇓

castreduce {n} {e} {Single{e = e₁} W} {Single{e = e₁'} W'} val (NfSingle j B) (NfSingle j' B')
  with e₁ ≡ᵉ? e₁'
... | yes eq = e , RValue val
... | no ¬eq = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.Dyn} val (NfSingle j B) NfDyn = Cast e (Single W) Dyn , RValue (VCast val GSingle)

castreduce {n} {e} {Single {e = e₁} W} {.UnitT} val (NfSingle j BUnit) NfUnit = e , RValue val
castreduce {n} {e} {Single {e = e₁} W} {.UnitT} val (NfSingle j BLabel) NfUnit = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.UnitT} val (NfSingle j BSingleLab) NfUnit = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.UnitT} val (NfSingle j BSingleUnit) NfUnit = e , RValue val -- Cast-Sub
castreduce {n} {e} {Single {e = e₁} W} {.UnitT} val (NfSingle j BDyn) NfUnit = Blame , RBlame -- Cast-Fail

castreduce {n} {e} {Single {e = e₁} W} {.(Label _)} val (NfSingle j BUnit) NfLabel = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {Label s'} val (NfSingle j (BLabel{s = s})) NfLabel
  with s ⊆? s'
...  | yes subs = e , RValue val
...  | no ¬subs = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {(Label s)} val (NfSingle j (BSingleLab{l = l})) NfLabel
  with l ∈? s
...  | yes ins = e , RValue val
...  | no ¬ins = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.(Label _)} val (NfSingle j BSingleUnit) NfLabel = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.(Label _)} val (NfSingle j BDyn) NfLabel = Blame , RBlame

castreduce {n} {e} {Single {e = e₁} W} {.(Pi _ _)} val (NfSingle j B) NfPi = Blame , RBlame
castreduce {n} {e} {Single {e = e₁} W} {.(Sigma _ _)} val (NfSingle j B) NfSigma = Blame , RBlame


{-
------------------------------------------------------------------------
-- Consistency, decidable checking for base types and decidable subtyping for ground types

cast-result : {n : ℕ} {A' A B : Ty {n}} → Is-just (cast A' A B) → (Data.Maybe.fromMaybe UnitT (cast A' A B) ≡ B) ⊎ (∃[ e ](∃[ V ](Data.Maybe.fromMaybe UnitT (cast A' A B) ≡ Single{e = e} V)))

-- (V : B => C) ▷ A means A either C or Single _ C
cast-lemma-3 : {n : ℕ} {e : Exp {n}} {A B C : Ty {n}} → Val e → [] ⊢ Cast e B C ▷ A → (A ≡ C) ⊎ (∃[ e ](∃[ W ](A ≡ Single{e = e} W)))
cast-lemma-3 {n} {e} {A} {B} {C} V (CastA{A' = A'} j x x₁)
  with cast-result{n}{A'}{B}{C} x
... | inj₁ x₃ = {!!}
... | inj₂ (fst , fst₁ , snd) = {!!}

b-◁ : {n : ℕ} {T : Ty {n}} {e : Exp {n}} → Val e → TyB T → notSingle T → Dec ([] ⊢ e ▷ T)
b-◁ {n} {.UnitT} {.UnitE} VUnit BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.UnitE} VUnit BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.UnitE} VUnit BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.UnitE} VUnit BSingleUnit b = yes (UnitAI empty)
b-◁ {n} {.UnitT} {.(LabI _)} VLab BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(LabI _)} VLab BLabel b = no λ ()
b-◁ {n} {(Single (VLab{x = x}))} {(LabI l)} VLab BSingleLab b 
  with x Data.Fin.≟ l
... | yes eq rewrite eq = yes (LabAI{l = l} empty)
... | no ¬eq = {!!}
b-◁ {n} {.(Single VUnit)} {.(LabI _)} VLab BSingleUnit b = no λ ()
b-◁ {n} {.UnitT} {.(Abs _)} VFun BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(Abs _)} VFun BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.(Abs _)} VFun BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.(Abs _)} VFun BSingleUnit b = no λ ()
b-◁ {n} {.UnitT} {.(ProdV V _)} (VProd V V₁) BUnit b = no λ ()
b-◁ {n} {.(Label _)} {.(ProdV V _)} (VProd V V₁) BLabel b = no λ ()
b-◁ {n} {.(Single VLab)} {.(ProdV V _)} (VProd V V₁) BSingleLab b = no λ ()
b-◁ {n} {.(Single VUnit)} {.(ProdV V _)} (VProd V V₁) BSingleUnit b = no λ ()
b-◁ {n} {A} {Cast e G Dyn} (VCast V x) bA b = no (ϱ A bA b)
  where
  ϱ : (A' : Ty) → (bA' : TyB A') → notSingle A' → ¬ ([] ⊢ Cast e G Dyn ▷ A')
  ϱ A' bA' (notsingle ns) j
    with cast-lemma-3 {n} {e} {A'} {G} {Dyn} V j
  ...  | inj₁ eq
       with bA'
  ...     | BUnit = contradiction eq (λ ())
  ...     | BLabel = contradiction eq (λ ())
  ...     | BSingleLab = contradiction eq (λ ())
  ...     | BSingleUnit = contradiction eq (λ ())
  ϱ A' bA' (notsingle ns) j | inj₂ (fst , fst₁ , snd)
       with bA'
  ...     | (BSingleLab{l = l}) = contradiction refl (ns (LabI l) VLab)
  ...     | BSingleUnit = contradiction refl (ns UnitE VUnit)
b-◁ {n} {A} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun V) b = {!!} -- analogous to case above

_~ : {n : ℕ} {T : Ty {n}} → TyNf T × T ≢ Dyn → ∃[ T' ](TyG{n} T')
_~ {n} {.Dyn} (NfDyn , ndyn) = contradiction refl ndyn
_~ {n} {.UnitT} (NfUnit , ndyn) = UnitT , GUnit
_~ {n} {(Label L)} (NfLabel , ndyn) = Label L , GLabel
_~ {n} {(Pi A B)} (NfPi , ndyn) = (Pi Dyn Dyn) , GPi
_~ {n} {(Sigma A B)} (NfSigma , ndyn) = (Sigma Dyn Dyn) , GSigma

g-≤? : {n : ℕ} {A B : Ty {n}} → TyG A → TyG B → Dec ([] ⊢ A ≤ᵀ B)
-- only ASubSingleSingle, only if V = W
g-≤? {n} {(Single V)} {(Single W)} GSingle GSingle = {!!}

-- ASubSingle applicable, if V has correct type => requires type check & synthesis
g-≤? {n} {(Single V)} {.UnitT} GSingle GUnit
  with b-◁ V BUnit (notsingle (λ e W → λ ()))
...  | yes p = yes (ASubSingle (SubTypeA p ASubUnit) BUnit (notsingle (λ e W → λ ())))
...  | no ¬p = {!!}
g-≤? {n} {(Single V)} {(Label L)} GSingle GLabel = {!!}

-- not base types, ASubSingle not applicable
g-≤? {n} {.(Single _)} {.(Pi Dyn Dyn)} GSingle GPi = {!!}
g-≤? {n} {.(Single _)} {.(Sigma Dyn Dyn)} GSingle GSigma = {!!}

g-≤? {n} {.UnitT} {.UnitT} GUnit GUnit = yes ASubUnit
g-≤? {n} {(Label s)} {(Label s')} GLabel GLabel
  with s ⊆? s'
...  | yes sub = yes (ASubLabel sub)
...  | no ¬sub = no ϱ
     where ϱ : ¬ ([] ⊢ Label s ≤ᵀ Label s')
           ϱ (ASubLabel sub) = contradiction (λ {x} → sub{x}) ¬sub
g-≤? {n} {.(Pi Dyn Dyn)} {.(Pi Dyn Dyn)} GPi GPi = yes (ASubPi ASubDyn ASubDyn)
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Sigma Dyn Dyn)} GSigma GSigma = yes (ASubSigma ASubDyn ASubDyn)

g-≤? {n} {.UnitT} {.(Single _)} GUnit GSingle = no (λ ())
g-≤? {n} {.UnitT} {.(Label _)} GUnit GLabel = no (λ ())
g-≤? {n} {.UnitT} {.(Pi Dyn Dyn)} GUnit GPi = no (λ ())
g-≤? {n} {.UnitT} {.(Sigma Dyn Dyn)} GUnit GSigma = no (λ ())
g-≤? {n} {.(Label _)} {.(Single _)} GLabel GSingle = no (λ ())
g-≤? {n} {.(Label _)} {.UnitT} GLabel GUnit = no (λ ())
g-≤? {n} {.(Label _)} {.(Pi Dyn Dyn)} GLabel GPi = no (λ ())
g-≤? {n} {.(Label _)} {.(Sigma Dyn Dyn)} GLabel GSigma = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Single _)} GPi GSingle = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.UnitT} GPi GUnit = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Label _)} GPi GLabel = no (λ ())
g-≤? {n} {.(Pi Dyn Dyn)} {.(Sigma Dyn Dyn)} GPi GSigma = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Single _)} GSigma GSingle = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.UnitT} GSigma GUnit = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Label _)} GSigma GLabel = no (λ ())
g-≤? {n} {.(Sigma Dyn Dyn)} {.(Pi Dyn Dyn)} GSigma GPi = no (λ ())


------------------------------------------------------------------------
-- Small step semantics

-- Type reduction
data _↠_ {n : ℕ} : Ty {n} → Ty {n} → Set
-- Expression reduction
data _⇨_ {n : ℕ} : Exp {n} → Exp {n} → Set

data _↠_ {n} where
  ξ-Case : {e e' : Exp {n}} {U : ValU e} {U' : ValU e'} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → e ⇨ e' → CaseT U f ↠ CaseT U' f
--  ξ-Pi : {A A' B : Ty {n}} → A ↠ A' → Pi A B ↠ Pi A' B
--  ξ-Sigma : {A A' B : Ty {n}} → A ↠ A' → Sigma A B ↠ Sigma A' B
  β-Case : {l : Fin n} {s : Subset n} {ins : l ∈ s} {f : ∀ l → l ∈ s → Ty {n}} → CaseT (UValLab{x = l}) f ↠ f l ins
  Case-Bot : {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → CaseT UBlame f ↠ Bot

data _⇨_ {n} where
  ξ-App1 : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → App e₁ e ⇨ App e₁' e
  ξ-App2 : {e e₂ e₂' : Exp {n}} → e₂ ⇨ e₂' → App e e₂ ⇨ App e e₂'
  ξ-LetE : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → LetE e₁ e ⇨ LetE e₁' e
  ξ-Prod : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → Prod e₁ e ⇨ Prod e₁' e
  ξ-ProdV : {e e₂ e₂' : Exp {n}} {v : Val e} → e₂ ⇨ e₂' → ProdV v e₂ ⇨ ProdV v e₂'
  ξ-LetP : {e₁ e₁' e₂ : Exp {n}} → e₁ ⇨ e₁' → LetP e₁ e₂ ⇨ LetP e₁' e₂
  ξ-Cast : {e₁ e₂ : Exp {n}} {A B : Ty {n}} → e₁ ⇨ e₂ → Cast e₁ A B ⇨ Cast e₂ A B
  ξ-Case : {s : Subset n} {e₁ e₂ : Exp {n}} {U : ValU e₁} {U' : ValU e₂} {f : ∀ l → l ∈ s → Exp {n}} → e₁ ⇨ e₂ → CaseE U f ⇨ CaseE U' f 
  β-App : {e e' : Exp {n}} → (v : Val e') → (App (Abs e) e') ⇨ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e) ])
  β-Prod : {e e' : Exp {n}} {v : Val e} → Prod e e' ⇨ ProdV v (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
  β-LetE : {e e' : Exp {n}} → (v : Val e) → LetE e e' ⇨ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
  β-LetP : {e e' e'' : Exp {n}} → (v : Val e) → (v' : Val e')
                            → LetP (ProdV v e') e''
                              ⇨
                              ↑ (ℤ.negsuc 1) , 0 [ ([ 0 ↦ ↑ⱽ¹[ v ] ]
                                                     ([ 0 ↦ shift-val {n} {ℤ.pos 1} {1} v' ] e'')) ]
  β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} {x : Fin n} → (ins : x ∈ s)
           → CaseE (UValLab{x = x}) f ⇨ f x ins

  -- differs from paper, since substitution limited to values
  Cast-Func : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}} → App (Cast e (Pi A B) (Pi A' B')) e' ⇨ LetE (Cast e' A' A) (Cast (App e (Var 0)) B ([ 0 ↦ w ]ᵀ B'))
  Cast-Pair : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}}
              → Cast (ProdV v e') (Sigma A B) (Sigma A' B') ⇨ Prod (Cast e A A') (Cast e' B B')

  App1-Blame : {e : Exp {n}} → App Blame e ⇨ Blame
  App2-Blame : {e : Exp {n}} {v : Val e} → App e Blame ⇨ Blame
  LetE-Blame : {e : Exp {n}} → LetE Blame e ⇨ Blame
  Prod-Blame : {e : Exp {n}} → Prod Blame e ⇨ Blame
  ProdV-Blame : {e : Exp {n}} {v : Val e} → ProdV v Blame ⇨ Blame
  LetP-Blame : {e  : Exp {n}} → LetP Blame e ⇨ Blame
  Cast-Blame : {A B : Ty {n}} → Cast Blame A B ⇨ Blame 
  Case-Blame : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} → CaseE UBlame f ⇨ Blame
  --  Cast-Bot-L : {e : Exp {n}} {B : Ty {n}} → Cast e Bot B ⇨ Blame -- if taken back, cast-reduce-r has to be adjusted for determinism
  --  Cast-Bot-R : {e : Exp {n}} {A : Ty {n}} → TyNf A → A ≢ Bot → Cast e A Bot ⇨ Blame   
  

  -- TODO
  -- has to have subtyping, since * base type so singletons with base are possible
  Cast-Dyn : {e : Exp {n}} {v : Val e} → Cast e Dyn Dyn ⇨ e 
  Cast-Unit : {e : Exp {n}} {v : Val e} → Cast e UnitT UnitT ⇨ e
  Cast-Label : {e : Exp {n}} {v : Val e} {L L' : Subset n} → L ⊆ L' → Cast e (Label L) (Label L') ⇨ e
  Cast-Collapse-Label-Label : {e : Exp {n}} {v : Val e} {L L' : Subset n} → L ⊆ L' → Cast (Cast e (Label L) Dyn) Dyn (Label L') ⇨ e
  Cast-Collapse : {e : Exp {n}} {v : Val e} {G : Ty {n}} {g : TyG G} → Cast (Cast e G Dyn) Dyn G ⇨ e
  Cast-Collide : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {g : TyG G} {h : TyG H} → G ≢ H → Cast (Cast e G Dyn) Dyn H ⇨ Blame
  Cast-Reduce-L : {e : Exp {n}} {v : Val e} {A A' B : Ty {n}} → A ↠ A' → Cast e A B ⇨ Cast e A' B
  Cast-Reduce-R : {e : Exp {n}} {v : Val e} {A B B' : Ty {n}} → TyNf A → B ↠ B' → Cast e A B ⇨ Cast e A B'

  Cast-Factor-L : {e : Exp {n}} {v : Val e} {G nA : Ty {n}} {g : TyG G} {nfA : TyNf nA} → ([] ∣ [] ⊢ G ~ nA) → [] ⊢ nA → G ≢ nA → nA ≢ Dyn → Cast e nA Dyn ⇨ Cast (Cast e nA G) G Dyn
  Cast-Factor-R : {e : Exp {n}} {v : Val e} {G nB : Ty {n}} {g : TyG G} {nfB : TyNf nB} → ([] ∣ [] ⊢ G ~ nB) → [] ⊢ nB → G ≢ nB → nB ≢ Dyn → Cast e Dyn nB ⇨ Cast (Cast e Dyn G) G nB




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
venv ∶ UnitT ⇓ᵀ = UnitT , (NfUnit)∷ 
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
-}

