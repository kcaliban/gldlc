module ldlc-algo where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Vec hiding (_++_ ; length)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Sum

-- REQUIRED PROPERTIES, TO BE MOVED TO SEPERATE FILE
empty-subset-outside : {n : ℕ} → (x : Fin n) → ¬ (⊥ [ x ]= inside)
empty-subset-outside {.(ℕ.suc _)} zero ()
empty-subset-outside {.(ℕ.suc _)} (Fin.suc x) (there ins) = empty-subset-outside x ins

x∈[l]⇒x≡l : {n : ℕ} {x l : Fin n} → x ∈ ⁅ l ⁆ → x ≡ l
x∈[l]⇒x≡l {.(ℕ.suc _)} {zero} {zero} ins = refl
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {zero} (there ins) = contradiction ins (empty-subset-outside x)
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {Fin.suc l} (there ins) = cong Fin.suc (x∈[l]⇒x≡l ins)

l∈L⇒[l]⊆L : {n : ℕ} {l : Fin n} {L : Subset n} → l ∈ L → ⁅ l ⁆ ⊆ L
l∈L⇒[l]⊆L {n} {l} {L} ins x rewrite (x∈[l]⇒x≡l x) = ins

module defs where
  data Exp {n : ℕ} : Set where
    Var : ℕ → Exp {n}
    UnitE : Exp {n}
    Abs : Exp {n} → Exp {n}
    App : Exp {n} → Exp {n} → Exp {n}
    LabI : Fin n → Exp {n}
    CaseE : {s : Subset n} → Exp {n} → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    ProdV : Exp {n} → Exp {n} → Exp {n}
    Let : Exp {n} → Exp {n} → Exp {n}

  data Val {n : ℕ} : Exp {n} → Set where
    VUnit : Val UnitE
    VVar : {i : ℕ} → Val (Var i)
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

  ----------------------------------------------------------------------
  ----------------------------------------------------------------------

  -- Useful shorthands
  data notSingle {n : ℕ} : Ty {n} → Set where
    notsingle : {A : Ty {n}} → (∀ W B → ¬ (A ≡ Single W B)) → notSingle A

  ---- Substitution and Shifting
  -- shifting and substitution

  -- shifting, required to avoid variable-capturing in substitution
  -- see Pierce 2002, pg. 78/79
  ↑ᴺ_,_[_] : ℤ → ℕ → ℕ → ℕ
  ↑ᴺ d , c [ x ]
    with (x <ᴺ? c)
  ...  | yes p = x
  ...  | no ¬p = ∣ ℤ.pos x +ᶻ d ∣
  
  ↑_,_[_] : ∀ {n} → ℤ → ℕ → Exp {n} → Exp
  ↑ d , c [ UnitE ] = UnitE
  ↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])
  ↑ d , c [ LabI x ] = LabI x
  ↑ d , c [ CaseE V f ] = CaseE ↑ d , c [ V ] (λ l x → ↑ d , c [ f l x ])
  ↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ ProdV e e' ] = ProdV (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ Let e e' ] = Let (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])

  -- shorthands
  ↑¹[_] : ∀ {n} → Exp {n} → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  -- see Pierce 2002, pg. 80
  [_↦_]_ : ∀ {n} → ℕ → Exp {n} → Exp → Exp
  [ k ↦ s ] UnitE = UnitE
  [ k ↦ s ] Var x
    with (_≟ᴺ_ x k)
  ...  | yes p = s
  ...  | no ¬p = Var x
  [ k ↦ s ] Abs t = Abs ([ ℕ.suc k ↦ ↑¹[ s ] ] t)
  [ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)
  [ k ↦ s ] LabI ins = LabI ins
  [ k ↦ s ] CaseE V f = CaseE ([ k ↦ s ] V) (λ l x → [ k ↦ s ] (f l x))
  [ k ↦ s ] Prod e e' = Prod ([ k ↦ s ] e) ([ ℕ.suc k ↦ ↑¹[ s ] ] e')
  [ k ↦ s ] ProdV e e' = Prod ([ k ↦ s ] e) ([ ℕ.suc k ↦ ↑¹[ s ] ] e')
  [ k ↦ s ] Let e e' = Let ([ k ↦ s ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ ↑ (ℤ.pos 2) , 0 [ s ] ] e')

  -- type substitution
  [_↦_]ᵀ_ : ∀ {n} → ℕ → Exp {n} → Ty {n} → Ty {n}
  [ k ↦ s ]ᵀ UnitT = UnitT
  [ k ↦ s ]ᵀ Single x T = Single ([ k ↦ s ] x) ([ k ↦ s ]ᵀ T)
  [ k ↦ s ]ᵀ Label x = Label x
  [ k ↦ s ]ᵀ Pi T T₁ = Pi ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [ k ↦ s ]ᵀ Sigma T T₁ = Sigma ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [ k ↦ s ]ᵀ CaseT x f = CaseT ([ k ↦ s ] x) λ l x₁ → [ k ↦ s ]ᵀ (f l x₁)

  -- variable in expression
  data _∈`_ {N : ℕ} : ℕ → Exp {N} → Set where
    
  -- variable in type
  data _∈`ᵀ_ {N : ℕ} : ℕ → Ty {N} → Set where

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

  length {n} [] = zero
  length {n} ⟨ T , Γ ⟩ = ℕ.suc (length Γ)
  
  data _⊢_ {n} where
    UnitF : {Γ : TEnv {n}} → Γ ⊢ UnitT
    LabF : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L
    PiF : {Γ : TEnv {n}} {A B : Ty {n}} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Pi A B
    SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Sigma A B
    SingleF : {Γ : TEnv {n}} {A : Ty {n}} {V : Exp {n}} {val : Val V} → Γ ⊢ V ⇐ A → notSingle A → Γ ⊢ Single V A
    CaseF : {Γ : TEnv {n}} {L : Subset n} {V : Exp {n}} {val : Val V} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ V ⇐ Label L → Γ ⊢ CaseT V f

  data _⊢_⇐_ {n} where
    SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
               → Γ ⊢ M ⇒ A
               → Γ ⇒ A ≤ B
               → Γ ⊢ M ⇐ B

  data _⇒_≤_ {n} where
    ASubUnit : {Γ : TEnv {n}} → Γ ⇒ UnitT ≤ UnitT
    ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⇒ Label L ≤ Label L'
    ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {V : Exp {n}} {val : Val V} → Γ ⇒ A ≤ B → Γ ⇒ Single V A ≤ B
    ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}} {ok : Γ ⊢ A}
             → Γ ⇒ A' ≤ A
             → ⟨ A , Γ ⟩ {ok} ⇒ B ≤ B'
             → Γ ⇒ Pi A B ≤ Pi A' B'
    ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}} {ok : Γ ⊢ A}
                → Γ ⇒ A ≤ A'
                → ⟨ A , Γ ⟩ {ok} ⇒ B ≤ B'
                → Γ ⇒ Sigma A B ≤ Sigma A' B'
    ASubCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {V : Exp {n}} {val : Val V} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ V ⇒ Single (LabI l) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ (f l ins) ≤ B
                 → Γ ⇒ CaseT V f ≤ B
    ASubCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {V : Exp {n}} {val : Val V} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ V ⇒ Single (LabI l) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ A ≤ (f l ins)
                 → Γ ⇒ A ≤ CaseT V f
    ASubCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (LabI l) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ (f l i) ≤ B)  -- ok req constr LabAI. ok in LabAEx req constr ASubLabel. fix: ok'
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ CaseT (Var (length Γ')) f ≤ B
    ASubCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (LabI l) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≤ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ A ≤ CaseT (Var (length Γ')) f               
             
    
  data _⊢_⇒_ {n} where
    VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → x ∶ A ∈ Γ → Γ ⊢ Var x ⇒ A
    UnitAI : {Γ : TEnv {n}} → Γ ⊢ UnitE ⇒ UnitT
    LabAI : {Γ : TEnv {n}} {l : Fin n} → Γ ⊢ LabI l ⇒ Single (LabI l) (Label ⁅ l ⁆)
    LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {V : Exp {n}} {val : Val V} {ins : l ∈ L} {f : ∀ l → l ∈ L → Exp {n}}
             → Γ ⊢ V ⇒ Single (LabI l) (Label L')
             → L' ⊆ L
             → Γ ⊢ (f l ins) ⇒ B
             → Γ ⊢ CaseE V f ⇒ B
    LabAEx : {Γ Γ' : TEnv {n}} {D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (LabI l) (Label L)} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}}
             → Γ ⇒ D ≤ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (LabI l) (Label L)) , Γ ⟩ {ok = ok' l i}) ⊢ (f l i) ⇒ (f-t l i))  -- reason for ok' see ASubCaseXL
             → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseE (Var (length Γ')) f ⇒ CaseT (Var (length Γ')) f-t
    PiAI : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {M : Exp {n}} → ⟨ A , Γ ⟩ {ok} ⊢ M ⇒ B → Γ ⊢ Abs M ⇒ Pi A B
    PiAE : {Γ : TEnv {n}} {A B D : Ty {n}} {M N : Exp {n}}
           → Γ ⊢ M ⇒ D
           → Γ ⊢ D ⇓ Pi A B
           → Γ ⊢ N ⇐ A
           → Γ ⊢ ([ 0 ↦ N ]ᵀ B)
           → Γ ⊢ App M N ⇒ ([ 0 ↦ N ]ᵀ B)
    SigmaAI : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {M N : Exp {n}}
              → Γ ⊢ M ⇐ A
              → ⟨ A , Γ ⟩ {ok} ⊢ N ⇒ B
              → Γ ⊢ Prod M N ⇒ Sigma A B
    PairAI : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {V N : Exp {n}} {val : Val V}
             → Γ ⊢ V ⇒ A
             → ⟨ A , Γ ⟩ {ok} ⊢ N ⇒ B
             → Γ ⊢ ProdV V N ⇒ Sigma A B
    SigmaAE : {Γ : TEnv {n}} {A B C D : Ty {n}} {ok : Γ ⊢ A} {ok' : ⟨ A , Γ ⟩ {ok} ⊢ B} {M N : Exp {n}}
            → Γ ⊢ M ⇒ D
            → Γ ⊢ D ⇓ Sigma A B
            → ⟨ B , ⟨ A , Γ ⟩ {ok = ok} ⟩ {ok = ok'} ⊢ N ⇒ C
            → (¬ (0 ∈`ᵀ C)) × (¬ (1 ∈`ᵀ C))
            → Γ ⊢ Let M N ⇒ C

  data _⊢_⇓_ {n} where
    AURefl-U : {Γ : TEnv {n}} → Γ ⊢ UnitT ⇓ UnitT
    AURefl-L : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ⇓ Label L
    AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
    AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
    AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {V : Exp {n}} {val : Val V} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
    AUCaseL : {Γ : TEnv {n}} {D : Ty {n}} {l : Fin n} {L L' : Subset n} {ins : l ∈ L} {f : ∀ l → l ∈ L → Ty {n}} {V : Exp {n}} {val : Val V}
              → Γ ⊢ V ⇒ Single (LabI l) (Label L')
              → L' ⊆ L
              → Γ ⊢ (f l ins) ⇓ D
              → Γ ⊢ CaseT V f ⇓ D
    AUCaseX-P : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (LabI l) (Label L)}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≤ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseT (Var (length Γ')) fᴮ ⇓ Pi A (CaseT (Var (length Γ')) fᴰ)
    AUCaseX-S : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (LabI l) (Label L)}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (LabI l) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≤ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseT (Var (length Γ')) fᴮ ⇓ Sigma A (CaseT (Var (length Γ')) fᴰ)

module examples where
  open defs

  -- x : {l₁, l₂} ⊢ case x of {l₁ : (), l₂ : l₃} ⇒ case x of {l₁ : Unit, l₂ : S{l₃ : {l₃}}}
  [l1,l2] : Subset 3
  [l1,l2] = inside ∷ (inside ∷ (outside ∷ []))

  [l3] : Subset 3
  [l3] = outside ∷ (outside ∷ (inside ∷ []))

  f₁ : (l : Fin 3) → l ∈ [l1,l2] → Exp {n = 3}
  f₁ zero here = UnitE
  f₁ (Fin.suc zero) (there here) = LabI (Fin.suc (Fin.suc zero))
  f₁ (Fin.suc (Fin.suc .(Fin.suc _))) (there (there (there ())))

  f₂ : (l : Fin 3) → l ∈ [l1,l2] → Ty {n = 3}
  f₂ zero here = UnitT
  f₂ (Fin.suc zero) (there here) = Single (LabI (Fin.suc (Fin.suc zero))) (Label [l3])
  f₂ (Fin.suc (Fin.suc .(Fin.suc _))) (there (there (there ())))

  _ : ⟨ Label [l1,l2] , [] ⟩ {ok = LabF} ⊢ CaseE{s = [l1,l2]} (Var 0) f₁ ⇒ CaseT{s = [l1,l2]} (Var 0) f₂
  _ = LabAEx (ASubLabel (λ x → x)) g
    where g : (l : Fin 3) → (i : l ∈ [l1,l2])
              → ⟨ Single (LabI l) (Label [l1,l2]) , [] ⟩ {ok = SingleF{val = VLab} (SubTypeA LabAI (ASubSingle{val = VLab} (ASubLabel (l∈L⇒[l]⊆L i)))) (notsingle (λ W B → λ ()))} ⊢ f₁ l i ⇒ f₂ l i
          g zero here = UnitAI
          g (Fin.suc zero) (there here) = LabAI
          g (Fin.suc (Fin.suc zero)) (there (there ()))

  ----------------------------------------------------------------------
  
  -- [] ⊢ ⟨ x : {l₁} = l₁ , case x of {l₁ : ()} ⟩ ⇒ Σ (x : {l₁}) (case x of {l₁ : Unit})
  [l1] : Subset 1
  [l1] = inside ∷ []

  premise : (⟨ Label [l1] , [] ⟩ {ok = LabF}) ⊢ CaseE (Var 0) (λ l x → UnitE) ⇒ CaseT (Var 0) (λ l x → UnitT)
  premise = (LabAEx{ok' = ok'} (ASubLabel (λ x → x)) (λ l i → UnitAI))
     where ok' : (l : Fin 1) → l ∈ [l1] → [] ⊢ Single (LabI l) (Label [l1])
           ok' zero here = SingleF{val = VLab} (SubTypeA LabAI (ASubSingle{val = VLab} (ASubLabel (λ x → x)))) (notsingle (λ W B → λ ()))
          
  J : [] ⊢ Prod (LabI zero) (CaseE{s = [l1]} (Var 0) (λ l x → UnitE)) ⇒ Sigma (Label [l1]) (CaseT{s = [l1]} (Var 0) (λ l x → UnitT))
  J = SigmaAI{ok = LabF} (SubTypeA LabAI (ASubSingle{val = VLab} (ASubLabel (λ x → x))))
                         premise

  -- The expression reduces as follows:
  --
  --   ⟨ x : {l₁} = l₁ , case x of {l₁ : ()} ⟩
  -- → ⟨⟨ l₁ , () ⟩⟩
  --
  -- Only typing rule applicable to ⟨⟨ l₁ , () ⟩⟩ is Pair-A-I
  -- {l₁} becomes S{l₁ : {l₁}}, since Pair-A-I requires type inference (⇒), not checking (⇐)
  premise' : ⟨ Single (LabI zero) (Label (inside ∷ ⊥)) , [] ⟩ ⊢ UnitE ⇒ UnitT
  
  J' : [] ⊢ ProdV (LabI zero) UnitE ⇒ Sigma (Single (LabI zero) (Label [l1])) UnitT
  J' = PairAI{ok = SingleF{val = VLab} (SubTypeA LabAI (ASubSingle{val = VLab} (ASubLabel (λ x → x)))) (notsingle (λ W B → λ ()))}{val = VLab} LabAI premise'

  -- Premise' is easy to infer in this example:
  premise' = UnitAI

  -- But the premise required for PairAI does not automatically follow from the premise require for SigmaAI
  -- Substitution lemma removes the variable from the environment, leaving us in this example only with
  premise'' : [] ⊢ UnitE{n = 1} ⇒ UnitT
  premise'' = UnitAI
  
