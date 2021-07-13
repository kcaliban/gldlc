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
cast : {n : ℕ} → Ty {n} → Ty {n} → Ty {n} → Maybe (Ty {n})

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
  SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {ok : Γ ⊢ A} → ⊢ Γ ok → Γ ⊢ e ◁ A → notSingle×Base A → Γ ⊢ Single e A
  CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ◁ Label L → Γ ⊢ CaseT e f

data _⊢_◁_ {n} where
  SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
             → Γ ⊢ M ▷ A
             → Γ ⊢ A ≤ᵀ B
             → Γ ⊢ M ◁ B

data _⊢_≤ᵀ_ {n} where
  ASubBot : {Γ : TEnv {n}} {T : Ty {n}} {ok : Γ ⊢ T} → Γ ⊢ Bot ≤ᵀ T
  ASubDyn : {Γ : TEnv {n}} → Γ ⊢ Dyn ≤ᵀ Dyn  
  ASubUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≤ᵀ UnitT
  ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⊢ Label L ≤ᵀ Label L'
  ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ≤ᵀ B → TyB B → notSingle B → Γ ⊢ Single e A ≤ᵀ B
  ASubSingleSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e e' : Exp {n}} {V : Val e} → e ≡ e' → Γ ⊢ A ≤ᵀ B → Γ ⊢ Single e A ≤ᵀ Single e' B
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
                → (∀ l → (i : l ∈ L) → (Is-just (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) × (Γ' ++ ⟨ Data.Maybe.fromMaybe Bot (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
                → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) f ≤ᵀ B
  ASubCaseCR : {Γ Γ' Θ : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Is-just (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D)) × (Γ' ++ ⟨ Data.Maybe.fromMaybe Bot (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ B ≤ᵀ (f l i))
                → Θ ⊢ B ≤ᵀ CaseT (Cast (Var (length Γ')) D (Label L)) f

data _⊢_▷_ {n} where
  BlameA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Blame ▷ Bot
  VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
  CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} {ok : Γ ⊢ A} {ok' : Γ ⊢ B}
           → Γ ⊢ M ▷ A' → (Is-just (cast A' A B)) ×  B' ≡ Data.Maybe.fromMaybe Bot (cast A' A B) → Γ ⊢ Cast M A B ▷ B'
  UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ▷ Single UnitE UnitT
  LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ▷ Single (LabI l) (Label ⁅ l ⁆)
  LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Exp {n}}
           → Γ ⊢ e ▷ Single (LabI l) (Label L')
           → (subs : L' ⊆ L)
           → (ins : l ∈ L')
           → Γ ⊢ (f l (subs ins)) ▷ B
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
            → (∀ l → (i : l ∈ L) → Is-just (cast (Single (LabI l) (Label L)) (Label L) D) × (Γ' ++ ⟨ ( Data.Maybe.fromMaybe Bot (cast (Single (LabI l) (Label L)) (Label L) D)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
            → Θ ⊢ CaseE (Cast (Var (length Γ')) D (Label L)) f ▷ CaseT (Cast (Var (length Γ')) D (Label L)) f-t
  PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ▷ B → Γ ⊢ Abs M ▷ Pi A B
  PiAE : {Γ : TEnv {n}} {A B D F : Ty {n}} {M N : Exp {n}} {eq : F ≡ [ 0 ↦ N ]ᵀ B}
         → Γ ⊢ M ▷ D
         → Γ ⊢ D ⇓ Pi A B
         → Γ ⊢ N ◁ A
         → Γ ⊢ F
         → Γ ⊢ App M N ▷ F     
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
               → (∀ l → (i : l ∈ L) → Is-just (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) × (Γ' ++ ⟨ Data.Maybe.fromMaybe Bot (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Pi (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) fᴬ ⇓ Pi (CaseT (Cast (Var (length Γ')) D (Label L)) fᴮ) (CaseT (Cast (Var (length Γ')) D (Label L)) fᶜ)            
  AUCaseXDyn-S : {Γ Γ' Θ : TEnv {n}} {D : Ty} {L : Subset n} {fᴬ fᴮ fᶜ : (∀ l → l ∈ L → Ty {n})} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
               → (∀ l → (i : l ∈ L) → Is-just (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) × (Γ' ++ ⟨ Data.Maybe.fromMaybe Bot (cast (Single (LabI l) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) D) , Γ ⟩) ⊢ (fᴬ l i) ⇓ Sigma (fᴮ l i) (fᶜ l i))
               → Θ ⊢ CaseT (Cast (Var (length Γ')) D (Label L)) fᴬ ⇓ Sigma (CaseT (Cast (Var (length Γ')) D (Label L)) fᴮ) (CaseT (Cast (Var (length Γ')) D (Label L)) fᶜ)            

------------------------------------------------------------------------
-- Type normal form, type matching, properties

data TyNf {n} : Ty {n} → Set where
  NfDyn : TyNf Dyn
  NfUnit : TyNf UnitT
  NfLabel : {s : Subset n} → TyNf (Label s)
  NfPi : {A B : Ty {n}} → TyNf (Pi A B)
  NfSigma : {A B : Ty {n}} → TyNf (Sigma A B)
  NfSingle : {B : Ty {n}} {e : Exp {n}} {V : Val e} {tybB : notSingle×Base B} → TyNf (Single e B)

TyG⊂TyNf : {n : ℕ} {A : Ty {n}} → TyG A → TyNf A
TyG⊂TyNf {n} {.UnitT} GUnit = NfUnit
TyG⊂TyNf {n} {.(Label _)} GLabel = NfLabel
TyG⊂TyNf {n} {.(Pi Dyn Dyn)} GPi = NfPi
TyG⊂TyNf {n} {.(Sigma Dyn Dyn)} GSigma = NfSigma
TyG⊂TyNf {n} {.(Single _ (Label _))} (GSingleLabel{V = V}) = NfSingle {V = V} {tybB = BLabel}
TyG⊂TyNf {n} {.(Single _ UnitT)} (GSingleUnit{V = V}) = NfSingle {V = V} {tybB = BUnit}

_match : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → TyNf A → Σ (Ty {n}) (TyG)
_match {neq = neq} NfDyn = contradiction refl neq
NfUnit match = UnitT , GUnit
NfLabel {s = s} match = Label s , GLabel
NfPi match = (Pi Dyn Dyn) , GPi
NfSigma match = Sigma Dyn Dyn , GSigma
NfSingle {B = .UnitT} {e = e} {V = V} {tybB = BUnit} match = Single e UnitT , (GSingleUnit{V = V})
NfSingle {B = (Label s)} {e = e} {V = V} {tybB = BLabel}  match = Single e (Label s) , GSingleLabel{V = V}

data TyG×¬TyB {n : ℕ} : Ty {n} → Set where
  Pi : {A B : Ty {n}} → TyG×¬TyB (Pi A B)
  Sigma : {A B : Ty {n}} → TyG×¬TyB (Sigma A B)
  SingleLabel : {s : Subset n} {e : Exp {n}} {V : Val e} → (∀ l → e ≢ LabI l) → TyG×¬TyB (Single e (Label s))
  SingleUnit : {e : Exp {n}} {V : Val e} → e ≢ UnitE → TyG×¬TyB (Single e UnitT)

TyG×¬TyB-in : {n : ℕ} {A : Ty {n}} → TyG A → ¬ (TyB A) → TyG×¬TyB A
TyG×¬TyB-in {n} {.UnitT} GUnit ¬tyba = contradiction BUnit ¬tyba
TyG×¬TyB-in {n} {.(Label _)} GLabel ¬tyba = contradiction BLabel ¬tyba
TyG×¬TyB-in {n} {.(Pi Dyn Dyn)} GPi ¬tyba = Pi
TyG×¬TyB-in {n} {.(Sigma Dyn Dyn)} GSigma ¬tyba = Sigma
TyG×¬TyB-in {n} {Single (LabI x) (Label s)} (GSingleLabel{V = V}) ¬tyba = contradiction BSingleLab ¬tyba
TyG×¬TyB-in {n} {Single UnitE (Label s)} (GSingleLabel{V = V}) ¬tyba = SingleLabel{V = V} λ l → λ ()
TyG×¬TyB-in {n} {Single (Abs e) (Label s)} (GSingleLabel{V = V}) ¬tyba = SingleLabel{V = V} λ l → λ ()
TyG×¬TyB-in {n} {Single (ProdV e e₁) (Label s)} (GSingleLabel{V = V}) ¬tyba = SingleLabel{V = V} λ l → λ ()
TyG×¬TyB-in {n} {Single (Cast e x x₁) (Label s)} (GSingleLabel{V = V}) ¬tyba = SingleLabel{V = V} λ l → λ ()
TyG×¬TyB-in {n} {Single UnitE UnitT} GSingleUnit ¬tyba = contradiction BSingleUnit ¬tyba
TyG×¬TyB-in {n} {Single (Abs e) UnitT} (GSingleUnit{V = V}) ¬tyba = SingleUnit{V = V} (λ ())
TyG×¬TyB-in {n} {Single (LabI x) UnitT} (GSingleUnit{V = V}) ¬tyba = SingleUnit{V = V} (λ ())
TyG×¬TyB-in {n} {Single (ProdV e e₁) UnitT} (GSingleUnit{V = V}) ¬tyba = SingleUnit{V = V} (λ ())
TyG×¬TyB-in {n} {Single (Cast e x x₁) UnitT} (GSingleUnit{V = V}) ¬tyba = SingleUnit{V = V} (λ ())

data ¬TyG×TyNf {n : ℕ} : Ty {n} → Set where
  Dyn : ¬TyG×TyNf Dyn
  Pi : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Pi A B)
  Sigma : {A B : Ty {n}} → (A ≢ Dyn ⊎ B ≢ Dyn) → ¬TyG×TyNf (Sigma A B)

¬TyG×TyNf-in : {n : ℕ} {A : Ty {n}} → ¬ (TyG A) → TyNf A → ¬TyG×TyNf A
¬TyG×TyNf-in {n} {.Dyn} ntyg NfDyn = Dyn
¬TyG×TyNf-in {n} {.UnitT} ntyg NfUnit = contradiction (GUnit) ntyg
¬TyG×TyNf-in {n} {.(Label _)} ntyg NfLabel = contradiction (GLabel) ntyg
¬TyG×TyNf-in {n} {.(Single _ UnitT)} ntyg (NfSingle {V = V} {tybB = BUnit}) = contradiction (GSingleUnit{V = V}) ntyg
¬TyG×TyNf-in {n} {.(Single _ (Label _))} ntyg (NfSingle {V = V} {tybB = BLabel}) = contradiction (GSingleLabel{V = V}) ntyg
¬TyG×TyNf-in {n} {(Pi A B)} ntyg NfPi
  with A ≡ᵀ? Dyn
...  | no ¬p = Pi (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬q = Pi (inj₂ ¬q)     
...     | yes q rewrite p | q = contradiction (GPi) ntyg
¬TyG×TyNf-in {n} {(Sigma A B)} ntyg NfSigma
  with A ≡ᵀ? Dyn
...  | no ¬p = Sigma (inj₁ ¬p)
...  | yes p
     with B ≡ᵀ? Dyn
...     | no ¬q = Sigma (inj₂ ¬q)     
...     | yes q rewrite p | q = contradiction (GSigma) ntyg

TyG⇒match-equiv : {n : ℕ} {A : Ty {n}} → (tyga : TyG A) → (proj₁ (_match{neq = TyG-notDyn tyga} (TyG⊂TyNf tyga))) ≡ A
TyG⇒match-equiv {n} {.UnitT} GUnit = refl
TyG⇒match-equiv {n} {.(Label _)} GLabel = refl
TyG⇒match-equiv {n} {.(Pi Dyn Dyn)} GPi = refl
TyG⇒match-equiv {n} {.(Sigma Dyn Dyn)} GSigma = refl
TyG⇒match-equiv {n} {.(Single _ (Label _))} GSingleLabel = refl
TyG⇒match-equiv {n} {.(Single _ UnitT)} GSingleUnit = refl

TyG×TyNf⇒match-equiv : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → (tyga : TyG A) → (tynf : TyNf A) → (proj₁ (_match{neq = neq} tynf)) ≡ A
TyG×TyNf⇒match-equiv {n} {.UnitT} GUnit NfUnit = refl
TyG×TyNf⇒match-equiv {n} {.(Label _)} GLabel NfLabel = refl
TyG×TyNf⇒match-equiv {n} {.(Pi Dyn Dyn)} GPi NfPi = refl
TyG×TyNf⇒match-equiv {n} {.(Sigma Dyn Dyn)} GSigma NfSigma = refl
TyG×TyNf⇒match-equiv {n} {.(Single _ (Label _))} GSingleLabel (NfSingle{tybB = BLabel}) = refl
TyG×TyNf⇒match-equiv {n} {.(Single _ UnitT)} GSingleUnit (NfSingle{tybB = BUnit}) = refl

¬TyG×TyNf-in⇒match-inequiv : {n : ℕ} {A : Ty {n}} {neq : A ≢ Dyn} → ¬ (TyG A) → (tynf : TyNf A) → (proj₁ (_match{neq = neq} tynf)) ≢ A
¬TyG×TyNf-in⇒match-inequiv {n} {A} {neq} ntyg tynf
  with ¬TyG×TyNf-in ntyg tynf
...  | Dyn = contradiction refl neq
¬TyG×TyNf-in⇒match-inequiv {n} {(Pi A B)} {neq} ntyg NfPi | Pi (inj₁ x) = λ x₁ → contradiction (proj₁ (Pi-equiv x₁)) (A≢B→B≢A x)
¬TyG×TyNf-in⇒match-inequiv {n} {(Pi A B)} {neq} ntyg NfPi | Pi (inj₂ y) = λ x₁ → contradiction (proj₂ (Pi-equiv x₁)) (A≢B→B≢A y)
¬TyG×TyNf-in⇒match-inequiv {n} {(Sigma A B)} {neq} ntyg NfSigma | Sigma (inj₁ x) = λ x₁ → contradiction (proj₁ (Sigma-equiv x₁)) (A≢B→B≢A x)
¬TyG×TyNf-in⇒match-inequiv {n} {(Sigma A B)} {neq} ntyg NfSigma | Sigma (inj₂ y) = λ x₁ → contradiction (proj₂ (Sigma-equiv x₁)) (A≢B→B≢A y)

------------------------------------------------------------------------
-- Algorithm for subtyping, limited to ground and base types

[]⊢_≤ᵀ?_ : {n : ℕ} {G H : Ty {n}} (tygG : TyG G) (tygH : TyG H) → Dec ([] ⊢ G ≤ᵀ H)
[]⊢_≤ᵀ?ᴮ_ : {n : ℕ} {B B' : Ty {n}} (tybB : TyB B) (tybB' : TyB B') → Dec ([] ⊢ B ≤ᵀ B')

[]⊢_≤ᵀ?_ {n} {.UnitT} {.UnitT} GUnit GUnit = yes ASubUnit
[]⊢_≤ᵀ?_ {n} {.UnitT} {.(Label _)} GUnit GLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.UnitT} {.(Pi Dyn Dyn)} GUnit GPi = no λ ()
[]⊢_≤ᵀ?_ {n} {.UnitT} {.(Sigma Dyn Dyn)} GUnit GSigma = no λ ()
[]⊢_≤ᵀ?_ {n} {.UnitT} {.(Single _ (Label _))} GUnit GSingleLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.UnitT} {.(Single _ UnitT)} GUnit GSingleUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Label _)} {.UnitT} GLabel GUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {(Label s)} {(Label s')} GLabel GLabel
  with s ⊆? s' 
...  | yes subs = yes (ASubLabel subs)
...  | no ¬subs = no ϱ
     where ϱ : ¬ ([] ⊢ Label s ≤ᵀ Label s')
           ϱ (ASubLabel subs) = ¬subs subs
[]⊢_≤ᵀ?_ {n} {.(Label _)} {.(Pi Dyn Dyn)} GLabel GPi = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Label _)} {.(Sigma Dyn Dyn)} GLabel GSigma = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Label _)} {.(Single _ (Label _))} GLabel GSingleLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Label _)} {.(Single _ UnitT)} GLabel GSingleUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.UnitT} GPi GUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.(Label _)} GPi GLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.(Pi Dyn Dyn)} GPi GPi = yes (ASubPi ASubDyn ASubDyn)
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.(Sigma Dyn Dyn)} GPi GSigma = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.(Single _ (Label _))} GPi GSingleLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Pi Dyn Dyn)} {.(Single _ UnitT)} GPi GSingleUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.UnitT} GSigma GUnit = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.(Label _)} GSigma GLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.(Pi Dyn Dyn)} GSigma GPi = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.(Sigma Dyn Dyn)} GSigma GSigma = yes (ASubSigma ASubDyn ASubDyn)
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.(Single _ (Label _))} GSigma GSingleLabel = no λ ()
[]⊢_≤ᵀ?_ {n} {.(Sigma Dyn Dyn)} {.(Single _ UnitT)} GSigma GSingleUnit = no λ ()

[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {.UnitT} GSingleLabel GUnit = no ϱ
  where ϱ : ¬ ([] ⊢ Single e (Label s) ≤ᵀ UnitT)
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {(Label s')} (GSingleLabel{V = V}) GLabel
  with s ⊆? s'
...  | yes subs = yes (ASubSingle{V = V} (ASubLabel subs) BLabel notsingle-label)
...  | no ¬subs = no ϱ
     where ϱ : ¬ ([] ⊢ Single e (Label s) ≤ᵀ Label s')
           ϱ (ASubSingle (ASubLabel subs) b c) = ¬subs subs
[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {.(Pi Dyn Dyn)} GSingleLabel GPi = no ϱ
  where ϱ : ¬ ([] ⊢ Single e (Label s) ≤ᵀ (Pi Dyn Dyn))
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {.(Sigma Dyn Dyn)} GSingleLabel GSigma = no ϱ
  where ϱ : ¬ ([] ⊢ Single e (Label s) ≤ᵀ (Sigma Dyn Dyn))
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {(Single e' (Label s'))} (GSingleLabel{V = V}) GSingleLabel
  with e ≡ᵉ? e'
...  | no ¬eq = no ϱ
     where ϱ :  ¬ ([] ⊢ Single e (Label s) ≤ᵀ Single e' (Label s'))
           ϱ (ASubSingleSingle x sub) = ¬eq x
...  | yes eq rewrite eq
     with s ⊆? s'
...     | no ¬subs = no ϱ
        where ϱ :  ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Single e' (Label s'))
              ϱ (ASubSingleSingle{V = V} x (ASubLabel subs)) = ¬subs subs     
...     | yes subs = yes (ASubSingleSingle{V = V} refl (ASubLabel subs))
[]⊢_≤ᵀ?_ {n} {Single e (Label s)} {(Single e' UnitT)} GSingleLabel GSingleUnit = no ϱ
  where ϱ : ¬ ([] ⊢ Single e (Label s) ≤ᵀ Single e' UnitT)
        ϱ (ASubSingleSingle x ())
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {.UnitT} (GSingleUnit{V = V}) GUnit = yes (ASubSingle{V = V} ASubUnit BUnit (notsingle (λ e B → λ ())))
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {(Label s)} GSingleUnit GLabel = no ϱ
  where ϱ : ¬ ([] ⊢ Single e UnitT ≤ᵀ Label s)
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {(Pi Dyn Dyn)} GSingleUnit GPi = no ϱ
  where ϱ : ¬ ([] ⊢ Single e UnitT ≤ᵀ Pi Dyn Dyn)
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {(Sigma Dyn Dyn)} GSingleUnit GSigma =  no ϱ
  where ϱ : ¬ ([] ⊢ Single e UnitT ≤ᵀ Sigma Dyn Dyn)
        ϱ (ASubSingle () y z)
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {(Single e' (Label s))} GSingleUnit GSingleLabel = no ϱ
  where ϱ : ¬ ([] ⊢ Single e UnitT ≤ᵀ Single e' (Label s))
        ϱ (ASubSingleSingle x ())
[]⊢_≤ᵀ?_ {n} {(Single e UnitT)} {(Single e' UnitT)} (GSingleUnit{V = V}) GSingleUnit
  with e ≡ᵉ? e'
...  | yes eq = yes (ASubSingleSingle{V = V} eq ASubUnit)
...  | no ¬eq = no ϱ
  where ϱ : ¬ ([] ⊢ Single e UnitT ≤ᵀ Single e' UnitT)
        ϱ (ASubSingleSingle eq sub) = ¬eq eq

[]⊢_≤ᵀ?ᴮ_{n} {B} {B'} tybB tybB'
  with []⊢_≤ᵀ?_ (TyB⊂TyG tybB) (TyB⊂TyG tybB')
...  | yes leq = yes leq
...  | no ¬leq = no ¬leq

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
  Cast-Sub : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H}
               {neqG : G ≢ Pi Dyn Dyn × G ≢ Sigma Dyn Dyn} {neqH : H ≢ Pi Dyn Dyn × H ≢ Sigma Dyn Dyn}
             → [] ⊢ G ≤ᵀ H → Cast e G H ⇨ e
  Cast-Fail : {e : Exp {n}} {v : Val e} {nA nB : Ty {n}} {tynfA : TyNf nA} {tynfB : TyNf nB} {neq : nA ≢ Dyn × nB ≢ Dyn}
              → ¬ ([] ⊢ proj₁ (_match{neq = proj₁ neq} tynfA) ≤ᵀ proj₁ (_match{neq = proj₂ neq} tynfB)) → Cast e nA nB ⇨ Blame
  Cast-Collapse : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H} → [] ⊢ G ≤ᵀ H → Cast (Cast e G Dyn) Dyn H ⇨ e
  Cast-Collide : {e : Exp {n}} {v : Val e} {G H : Ty {n}} {tygG : TyG G} {tygH : TyG H} → ¬ ([] ⊢ G ≤ᵀ H) → Cast (Cast e G Dyn) Dyn H ⇨ Blame
  Cast-Pair : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}}
              → Cast (ProdV e e') (Sigma A B) (Sigma A' B') ⇨ Prod (Cast e A A') (Cast e' B B') 
  Cast-Func : {e e' : Exp {n}} {v : Val e} {w : Val e'} {A A' B B' : Ty {n}} → App (Cast e (Pi A B) (Pi A' B')) e' ⇨ Cast (App e (Cast e' A' A)) ([ 0 ↦ Cast e' A' A ]ᵀ B) ([ 0 ↦ e' ]ᵀ B')
  Cast-Reduce-L : {e : Exp {n}} {v : Val e} {A A' B : Ty {n}} → A ↠ A' → Cast e A B ⇨ Cast e A' B
  Cast-Reduce-R : {e : Exp {n}} {v : Val e} {A B B' : Ty {n}} → TyNf A → B ↠ B' → Cast e A B ⇨ Cast e A B'
  Cast-Factor-L : {e : Exp {n}} {v : Val e} {nA : Ty {n}} {nfA : TyNf nA} → (neq : nA ≢ Dyn) → nA ≢ (proj₁ (_match{neq = neq} nfA)) → Cast e nA Dyn ⇨ Cast (Cast e nA (proj₁ (_match{neq = neq} nfA))) (proj₁ (_match{neq = neq} nfA)) Dyn
  Cast-Factor-R : {e : Exp {n}} {v : Val e} {nB : Ty {n}} {nfB : TyNf nB} → (neq : nB ≢ Dyn) → nB ≢ (proj₁ (_match{neq = neq} nfB)) → Cast e Dyn nB ⇨ Cast (Cast e Dyn (proj₁ (_match{neq = neq} nfB))) (proj₁ (_match{neq = neq} nfB)) nB
  App₁-Blame : {e : Exp {n}} → App Blame e ⇨ Blame
  App₂-Blame : {e : Exp {n}} {v : Val e} → App e Blame ⇨ Blame
  LetE-Blame : {e : Exp {n}} → LetE Blame e ⇨ Blame
  Prod-Blame : {e : Exp {n}} → Prod Blame e ⇨ Blame
  ProdV-Blame : {e : Exp {n}} {v : Val e} → ProdV e Blame ⇨ Blame
  LetP-Blame : {e  : Exp {n}} → LetP Blame e ⇨ Blame
  Cast-Blame : {A B : Ty {n}} → Cast Blame A B ⇨ Blame
--  Cast-Bot-L : {e : Exp {n}} {v : Val e} {B : Ty {n}} → Cast e Bot B ⇨ Blame
  Cast-Bot-R : {e : Exp {n}} {v : Val e} {A : Ty {n}} → TyNf A → Cast e A Bot ⇨ Blame
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
-- Properties of ↠, ⇨

↠-TyNf-noreduce : {n : ℕ} {A : Ty {n}} → TyNf A → (∀ A' → ¬ (A ↠ A'))
↠-TyNf-noreduce {n} {.Dyn} NfDyn A' = λ ()
↠-TyNf-noreduce {n} {.UnitT} NfUnit A' = λ ()
↠-TyNf-noreduce {n} {.(Label _)} NfLabel A' = λ ()
↠-TyNf-noreduce {n} {.(Pi _ _)} NfPi A' = λ ()
↠-TyNf-noreduce {n} {.(Sigma _ _)} NfSigma A' = λ ()
↠-TyNf-noreduce {n} {.(Single _ _)} NfSingle A' = λ ()

⇨-Val-noreduce : {n : ℕ} {e : Exp {n}} → Val e → (∀ e' → ¬ (e ⇨ e'))
⇨-Val-noreduce {n} {.UnitE} VUnit = λ e' → λ ()
⇨-Val-noreduce {n} {.(LabI _)} VLab = λ e' → λ ()
⇨-Val-noreduce {n} {.(Abs _)} VFun = λ e' → λ ()
⇨-Val-noreduce {n} {(ProdV e e'')} (VProd V V₁) e' = ϱ
  where ϱ : ¬ (ProdV e e'' ⇨ e')
        ϱ (ξ-ProdV{e₂' = e'''} cons) = contradiction cons (⇨-Val-noreduce V₁ e''') 
⇨-Val-noreduce {n} {(Cast e G Dyn)} (VCast V x) e' = ϱ
  where ϱ : ¬ (Cast e G Dyn ⇨ e')
        ϱ (ξ-Cast{e₂ = e'''} cons) = contradiction cons (⇨-Val-noreduce V e''') 
        ϱ (Cast-Fail{neq = neq₁ , neq₂} x) = contradiction refl neq₂
        ϱ (Cast-Reduce-L{A' = A'} x') = contradiction x' (↠-TyNf-noreduce (TyG⊂TyNf x) A')
        ϱ (Cast-Factor-L{nfA = nfA} neq neq') rewrite (TyG×TyNf⇒match-equiv{neq = neq} x nfA) = contradiction refl neq'
⇨-Val-noreduce {n} {(Cast e (Pi A B) (Pi A' B'))} (VCastFun V) e' = ϱ
  where ϱ : ¬ (Cast e (Pi A B) (Pi A' B') ⇨ e')
        ϱ (ξ-Cast{e₂ = e'''} cons) = contradiction cons (⇨-Val-noreduce V e''')
        ϱ (Cast-Sub{tygG = GPi}{tygH = GPi}{neqH = neq₁ , neq₂} x) = contradiction refl neq₁
        ϱ (Cast-Fail{tynfA = NfPi}{tynfB = NfPi} x) = contradiction (ASubPi ASubDyn ASubDyn) x

⇨-ValU-closed : {n : ℕ} {e e' : Exp {n}} → ValU e → e ⇨ e' → ValU e'
⇨-ValU-closed {n} {e} {e'} (UVal x) r = contradiction r (⇨-Val-noreduce x e')
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast _ Dyn _)} (UVarCast x) (ξ-Cast ())
⇨-ValU-closed {n} {.(Cast (Var _) Dyn Dyn)} {.(Var _)} (UVarCast x) (Cast-Dyn{v = ()})
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {.(Var _)} (UVarCast x) (Cast-Sub{v = ()} x₁)
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {.Blame} (UVarCast x) (Cast-Fail x₁) = UBlame
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Var _) _ _)} (UVarCast x) (Cast-Reduce-L ())
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {.(Cast (Var _) Dyn _)} (UVarCast x) (Cast-Reduce-R{v = v}{B' = B'} x₁ x₂) = contradiction x₂ (↠-TyNf-noreduce (TyG⊂TyNf x) B')
⇨-ValU-closed {n} {.(Cast (Var _) Dyn Dyn)} {_} (UVarCast x) (Cast-Factor-L neq x₁) = contradiction refl neq
⇨-ValU-closed {n} {.(Cast (Var _) Dyn _)} {_} (UVarCast x) (Cast-Factor-R{nfB = nfG} neq x₁) = contradiction (sym (TyG×TyNf⇒match-equiv x nfG)) x₁
⇨-ValU-closed {n} {.(Cast _ Dyn _)} {.(Cast _ Dyn _)} (UValCast x x₁) (ξ-Cast{e₂ = e₂} r) = contradiction r (⇨-Val-noreduce x e₂)
⇨-ValU-closed {n} {.(Cast _ Dyn _)} {.Blame} (UValCast x x₁) (Cast-Fail x₂) = UBlame
⇨-ValU-closed {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} (UValCast x x₁) (Cast-Collapse{v = v} x₂) = UVal v
⇨-ValU-closed {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} (UValCast x x₁) (Cast-Collide x₂) = UBlame
⇨-ValU-closed {n} {.(Cast _ Dyn _)} {.(Cast _ Dyn _)} (UValCast x x₁) (Cast-Reduce-R{v = v}{B' = B'} x₂ x₃) = contradiction x₃ (↠-TyNf-noreduce (TyG⊂TyNf x₁) B')
⇨-ValU-closed {n} {.(Cast _ Dyn _)} {_} (UValCast x x₁) (Cast-Factor-R{nfB = nfG} neq x₂) = contradiction (sym (TyG×TyNf⇒match-equiv x₁ nfG)) x₂

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
  with Val? x
...  | no ¬v = stuck
evaluate-step-type (Single x (Label x₁)) | yes v = result (RNf (NfSingle{V = v}{tybB = BLabel}))
evaluate-step-type (Single x UnitT) | yes v = result (RNf (NfSingle{V = v}{tybB = BUnit}))
evaluate-step-type (Single x (Single x₁ A)) | yes v = stuck
evaluate-step-type (Single x (Pi A A₁)) | yes v = stuck
evaluate-step-type (Single x (Sigma A A₁)) | yes v = stuck
evaluate-step-type (Single x (CaseT x₁ f)) | yes v = stuck
evaluate-step-type (Single x Bot) | yes v = stuck
evaluate-step-type (Single x Dyn) | yes v = stuck

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
...     | result RBot = stuck
...     | result (RNf nfA)
        with evaluate-step-type B
...        | step st = step (Cast-Reduce-R{v = v} nfA st)
...        | stuck = stuck
...        | result RBot = step (Cast-Bot-R{v = v} nfA)
...        | result (RNf nfB)
           with A ≡ᵀ? Dyn | B ≡ᵀ? Dyn
...           | yes eq | yes eq₁ rewrite eq | eq₁ = step (Cast-Dyn{v = v})
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | yes eq₁ rewrite eq₁
  with TyG? A
...  | yes tyga = result (RValue (VCast v tyga))
...  | no ¬tyga = step (Cast-Factor-L{v = v}{nfA = nfA} ¬eq (A≢B→B≢A (¬TyG×TyNf-in⇒match-inequiv ¬tyga nfA)))
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁
  with TyG? B
...  | no ¬tygb rewrite eq = step (Cast-Factor-R{v = v}{nfB = nfB} ¬eq₁ (A≢B→B≢A (¬TyG×TyNf-in⇒match-inequiv ¬tygb nfB)))
evaluate-step-expr (Cast .UnitE Dyn B) | result (RValue VUnit) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(LabI _) Dyn B) | result (RValue VLab) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(Abs _) Dyn B) | result (RValue VFun) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast .(ProdV _ _) Dyn B) | result (RValue (VProd v v₁)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast (Cast e (Pi A B₁) (Pi A' B')) Dyn B) | result (RValue (VCastFun v)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb = stuck
evaluate-step-expr (Cast (Cast e G Dyn) Dyn B) | result (RValue (VCast v tygg)) | result (RNf nfA) | result (RNf nfB) | yes eq | no ¬eq₁ | yes tygb
  with []⊢ tygg ≤ᵀ? tygb
...  | yes leq = step (Cast-Collapse{v = v}{tygG = tygg}{tygH = tygb} leq)
...  | no ¬leq = step (Cast-Collide{v = v}{tygG = tygg}{tygH = tygb} ¬leq)

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁
  with TyG? A | TyG? B
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB
  with A ≡ᵀ? Pi Dyn Dyn | B ≡ᵀ? Pi Dyn Dyn
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | yes eq' | yes eq₁' rewrite eq' | eq₁' = result (RValue (VCastFun v))
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | yes eq' | no ¬eq₁' rewrite eq'
  with tygB
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfUnit}{neq = (λ ()) , (λ ())} λ ())
...  | GLabel = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfLabel}{neq = (λ ()) , (λ ())} λ ())
...  | GPi = contradiction refl ¬eq₁'
...  | GSigma = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma}{neq = (λ ()) , (λ ())} λ ())
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BLabel}}{neq = (λ ()) , (λ ())} λ ())
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BUnit}}{neq = (λ ()) , (λ ())} λ ())
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | yes eq₁' rewrite eq₁'
  with tygA
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfPi}{neq = (λ ()) , (λ ())} λ ())
...  | GLabel =  step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfPi}{neq = (λ ()) , (λ ())} λ ())
...  | GPi = contradiction refl ¬eq'
...  | GSigma = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi}{neq = (λ ()) , (λ ())} λ ())
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfPi}{neq = (λ ()) , (λ ())} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Pi Dyn Dyn)
           ϱ (ASubSingle () x x₁)
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfPi}{neq = (λ ()) , (λ ())} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Pi Dyn Dyn)
           ϱ (ASubSingle () x x₁)
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | no ¬eq₁'
  with A ≡ᵀ? Sigma Dyn Dyn | B ≡ᵀ? Sigma Dyn Dyn
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | no ¬eq₁' | yes eq'' | yes eq₁'' rewrite eq'' | eq₁''
  with v
...  | VUnit = stuck
...  | VLab = stuck
...  | VFun = stuck
...  | VCast w x = stuck
...  | VCastFun w = stuck
...  | VProd w w₁ = step (Cast-Pair{v = w}{w = w₁})
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | no ¬eq₁' | yes eq'' | no ¬eq₁'' rewrite eq''
  with tygB
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfUnit}{neq = (λ ()) , (λ ())} λ ())
...  | GLabel = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfLabel}{neq = (λ ()) , (λ ())} λ ())
...  | GPi = contradiction refl ¬eq₁'
...  | GSigma = contradiction refl ¬eq₁''
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BLabel}}{neq = (λ ()) , (λ ())} λ ())
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BUnit}}{neq = (λ ()) , (λ ())} λ ())
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | no ¬eq₁' | no ¬eq'' | yes eq₁'' rewrite eq₁''
  with tygA
...  | GUnit = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfSigma}{neq = (λ ()) , (λ ())} λ ())
...  | GLabel =  step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfSigma}{neq = (λ ()) , (λ ())} λ ())
...  | GPi = contradiction refl ¬eq'
...  | GSigma = contradiction refl ¬eq''
...  | GSingleLabel{e = e'}{V = V}{s = s} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfSigma}{neq = (λ ()) , (λ ())} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Sigma Dyn Dyn)
           ϱ (ASubSingle () x x₁)
...  | GSingleUnit{e = e'}{V = V} = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfSigma}{neq = (λ ()) , (λ ())} ϱ)
     where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Sigma Dyn Dyn)
           ϱ (ASubSingle () x x₁)
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | yes tygB | no ¬eq' | no ¬eq₁' | no ¬eq'' | no ¬eq₁''
  with []⊢ tygA ≤ᵀ? tygB
...  | yes leq = step (Cast-Sub{v = v}{tygG = tygA}{tygH = tygB}{neqG = ¬eq' , ¬eq''}{neqH = ¬eq₁' , ¬eq₁''} leq)
...  | no ¬leq
        with λ leqq → (Cast-Fail{v = v}{tynfA = nfA}{tynfB = nfB}{neq = ¬eq , ¬eq₁} leqq)
...        | w rewrite (TyG×TyNf⇒match-equiv{neq = ¬eq} tygA nfA) | (TyG×TyNf⇒match-equiv{neq = ¬eq₁} tygB nfB) = step (w ¬leq)

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB
  with ¬TyG×TyNf-in ¬tygB nfB
...  | Dyn = contradiction refl ¬eq₁
-- A = Pi
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x
  with v | tygA
evaluate-step-expr (Cast e UnitT (Pi A B)) | result (RValue v) | result (RNf NfUnit) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Label s) (Pi A B)) | result (RValue v) | result (RNf NfLabel) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma Dyn Dyn) (Pi A B)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSigma
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Single e' G) (Pi A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSingleLabel{s = s}
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Pi Dyn Dyn)
        ϱ (ASubSingle constr () x₁)       
evaluate-step-expr (Cast e (Single e' G) (Pi A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GSingleUnit
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Pi Dyn Dyn)
        ϱ (ASubSingle constr () x₁)   

evaluate-step-expr (Cast e (Pi Dyn Dyn) (Pi A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Pi x | w | GPi = result (RValue (VCastFun v))
-- A = Sigma
evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x
  with v | tygA
evaluate-step-expr (Cast e UnitT (Sigma A B)) | result (RValue v) | result (RNf NfUnit) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfUnit}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Label s) (Sigma A B)) | result (RValue v) | result (RNf NfLabel) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfLabel}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GPi
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Single e' G) (Sigma A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSingleLabel{s = s}
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BLabel}}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' (Label s) ≤ᵀ Sigma Dyn Dyn)
        ϱ (ASubSingle constr () x₁)  
evaluate-step-expr (Cast e (Single e' G) (Sigma A B)) | result (RValue v) | result (RNf (NfSingle{V = V}{tybB = tybB})) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | w | GSingleUnit
  = step (Cast-Fail{v = v}{tynfA = NfSingle{V = V}{tybB = BUnit}}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} ϱ)
  where ϱ : ¬ ([] ⊢ Single e' UnitT ≤ᵀ Sigma Dyn Dyn)
        ϱ (ASubSingle constr () x₁)  
evaluate-step-expr (Cast .UnitE (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VUnit | GSigma = stuck
evaluate-step-expr (Cast .(LabI _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VLab | GSigma = stuck
evaluate-step-expr (Cast .(Abs _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VFun | GSigma = stuck
evaluate-step-expr (Cast .(Cast _ _ Dyn) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VCast w x₁ | GSigma = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VCastFun w | GSigma = stuck
evaluate-step-expr (Cast .(ProdV _ _) (Sigma Dyn Dyn) (Sigma A B)) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | yes tygA | no ¬tygB | Sigma x | VProd w w₁ | GSigma
 = step (Cast-Pair{v = w}{w = w₁})

evaluate-step-expr (Cast e A B) | result (RValue v) | result (RNf nfA) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB
  with ¬TyG×TyNf-in ¬tygA nfA
...  | Dyn = contradiction refl ¬eq
-- A = Pi
evaluate-step-expr (Cast e (Pi A B) C) | result (RValue v) | result (RNf NfPi) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x
  with tygB
evaluate-step-expr (Cast e (Pi A B) UnitT) | result (RValue v) | result (RNf NfPi) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfUnit}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Label s)) | result (RValue v) | result (RNf NfPi) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfLabel}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Sigma Dyn Dyn)) | result (RValue v) | result (RNf NfPi) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSigma
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSigma}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Single e' G)) | result (RValue v) | result (RNf NfPi) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSingleLabel{s = s}
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BLabel{s = s}}}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Pi A B) (Single e' G)) | result (RValue v) | result (RNf NfPi) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GSingleUnit
 = step (Cast-Fail{v = v}{tynfA = NfPi}{tynfB = NfSingle{V = V}{tybB = BUnit}}{neq = ¬eq , ¬eq₁} λ ())

evaluate-step-expr (Cast e (Pi A B) (Pi Dyn Dyn)) | result (RValue v) | result (RNf NfPi) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Pi x | GPi
 = result (RValue (VCastFun v))
-- A = Sigma
evaluate-step-expr (Cast e (Sigma A B) C) | result (RValue v) | result (RNf NfSigma) | result (RNf nfB) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x
  with tygB
evaluate-step-expr (Cast e (Sigma A B) UnitT) | result (RValue v) | result (RNf NfSigma) | result (RNf NfUnit) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GUnit
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfUnit}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Label s)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfLabel) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GLabel
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfLabel}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Pi Dyn Dyn)) | result (RValue v) | result (RNf NfSigma) | result (RNf NfPi) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GPi
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfPi}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Single e' G)) | result (RValue v) | result (RNf NfSigma) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSingleLabel{s = s}
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BLabel{s = s}}}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast e (Sigma A B) (Single e' G)) | result (RValue v) | result (RNf NfSigma) | result (RNf (NfSingle{V = V}{tybB = tybB})) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSingleUnit
 = step (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSingle{V = V}{tybB = BUnit}}{neq = ¬eq , ¬eq₁} λ ())
evaluate-step-expr (Cast .UnitE (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VUnit) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = stuck
evaluate-step-expr (Cast .(LabI _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VLab) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = stuck
evaluate-step-expr (Cast .(Abs _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue VFun) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = stuck
evaluate-step-expr (Cast .(Cast _ _ Dyn) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VCast v x₁)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = stuck
evaluate-step-expr (Cast .(Cast _ (Pi _ _) (Pi _ _)) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VCastFun v)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = stuck
evaluate-step-expr (Cast .(ProdV _ _) (Sigma A B) (Sigma Dyn Dyn)) | result (RValue (VProd v v₁)) | result (RNf NfSigma) | result (RNf NfSigma) | no ¬eq | no ¬eq₁ | no ¬tygA | yes tygB | Sigma x | GSigma = step (Cast-Pair{v = v}{w = v₁})

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
  with A ≡ᵀ? A'
...  | no ¬eq = nothing
...  | yes eq 
     with evaluate-full (gas 1000) (Cast e A B)
...     | fst , result RBlame = just Bot
...     | fst , result (RValue v) = just (Single fst B)
...     | fst , stuck = nothing
...     | fst , out-of-gas = nothing

cast UnitT A B
  with A ≡ᵀ? UnitT
...  | yes eq = just B
...  | no ¬eq = nothing
cast (Label x) A B
  with A ≡ᵀ? Label x
...  | yes eq = just B
...  | no ¬eq = nothing
cast (Pi A' A'') A B
  with A ≡ᵀ? Pi A' A''
...  | yes eq = just B
...  | no ¬eq = nothing
cast (Sigma A' A'') A B
  with A ≡ᵀ? Sigma A' A''
...  | yes eq = just B
...  | no ¬eq = nothing
cast (CaseT x f) A B
  with A ≡ᵀ? CaseT x f
...  | yes eq = just B
...  | no ¬eq = nothing
cast Bot A B
  with A ≡ᵀ? Bot
...  | yes eq = just B
...  | no ¬eq = nothing
cast Dyn A B
  with A ≡ᵀ? Dyn
...  | yes eq = just B
...  | no ¬eq = nothing

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
