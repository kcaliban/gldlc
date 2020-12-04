-- {-# OPTIONS --show-implicit #-}
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
  data Exp {n : ℕ} : Set
  data Val {n : ℕ} : Exp {n} → Set
  data Ty {n : ℕ} : Set

  data Exp {n} where
    Var : ℕ → Exp {n}
    UnitE : Exp {n}
    Abs : Exp {n} → Exp {n}
    App : {e : Exp {n}} → Exp {n} → Val e → Exp {n}
    LabI : Fin n → Exp {n}
    CaseE : {s : Subset n} {e : Exp {n}} → Val e → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    ProdV : {e : Exp {n}} → Val e → Exp {n} → Exp {n}
    LetP : Exp {n} → Exp {n} → Exp {n}
    LetE : Exp {n} → Exp {n} → Exp {n}

  data Val {n} where
    VUnit : Val UnitE
    VVar : {i : ℕ} → Val (Var i)
    VLab : {x : Fin n} → Val (LabI x)
    VFun : {N : Exp} → Val (Abs N)
    VProd : {e e' : Exp} → (v : Val e) → Val e' → Val (ProdV v e')

  data Ty {n} where
    UnitT : Ty
    Single : {e : Exp {n}} → Val e → Ty {n} → Ty
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    CaseT : {s : Subset n} {e : Exp {n}} → Val e → (f : ∀ l → l ∈ s → Ty {n}) → Ty 

  ----------------------------------------------------------------------
  ----------------------------------------------------------------------

  -- Useful shorthands
  data notSingle {n : ℕ} : Ty {n} → Set where
    notsingle : {A : Ty {n}} {e : Exp {n}} → (∀ W B → ¬ (A ≡ Single{e = e} W B)) → notSingle A

  ---- Substitution and Shifting
  -- shifting and substitution
  ↑ᴺ_,_[_] : ℤ → ℕ → ℕ → ℕ
  ↑ᴺ d , c [ x ]
    with (x <ᴺ? c)
  ...  | yes p = x
  ...  | no ¬p = ∣ ℤ.pos x +ᶻ d ∣

  ↑_,_[_] : ∀ {n} → ℤ → ℕ → Exp {n} → Exp {n}
  shift-val : ∀ {n d c} {e : Exp {n}} → Val e → Val (↑ d , c [ e ])

  ↑ d , c [ UnitE ] = UnitE
  ↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t v ] = App (↑ d , c [ t ]) (shift-val{d = d}{c = c} v)
  ↑ d , c [ LabI x ] = LabI x
  ↑ d , c [ CaseE{e = e} V f ] = CaseE (shift-val{d = d}{c = c} V) (λ l x → ↑ d , c [ f l x ])
  ↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ ProdV e e' ] = ProdV (shift-val{d = d}{c = c} e) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ LetP e e' ] = LetP (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])
  ↑ d , c [ LetE e e' ] = LetE (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

  shift-val {n} {d} {c} {.UnitE} VUnit = VUnit
  shift-val {n} {d} {c} {.(Var _)} VVar = VVar
  shift-val {n} {d} {c} {.(LabI _)} VLab = VLab
  shift-val {n} {d} {c} {.(Abs _)} VFun = VFun
  shift-val {n} {d} {c} {.(ProdV V _)} (VProd V V₁) = VProd (shift-val V) (shift-val V₁)

  -- shorthands
  ↑¹[_] : ∀ {n} → Exp {n} → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  [_↦_]_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Exp {n} → Exp {n}
  sub-val : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → Val e → Val ([ k ↦ v ] e)
  [_↦_]_ {n} {e} k v (Var x)
    with (_≟ᴺ_ x k)
  ...  | yes p = e
  ...  | no ¬p = Var x
  [ k ↦ v ] UnitE = UnitE
  [ k ↦ v ] Abs e = Abs (([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e))
  [_↦_]_ {n} {e'} k v (App{e = e₁} e v') = App ([ k ↦ v ] e) (sub-val{n}{k}{e₁}{e'}{v} v') -- ([ k ↦ v ] e₁)
  [ k ↦ v ] LabI x = LabI x
  [_↦_]_ {n} {e} k v (CaseE v' f) = CaseE (sub-val{n}{k}{e' = e}{v = v} v') (λ l x₁ → [ k ↦ v ] (f l x₁))
  [ k ↦ v ] Prod e e₁ = Prod ([ k ↦ v ] e) ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)
  [_↦_]_ {n} {e} k v (ProdV v' e') = ProdV (sub-val{n}{k}{e' = e}{v = v} v') ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e')
  [ k ↦ v ] LetP e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ shift-val{d = ℤ.pos 2}{c = 0} v ] e₁)
  [ k ↦ v ] LetE e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc k) ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)

  sub-val {n} {k} {.UnitE} {e'} {v} VUnit = VUnit
  sub-val {n} {k} {(Var i)} {e'} {v} VVar
    with (_≟ᴺ_ i k)
  ...  | yes p = v
  ...  | no ¬p = VVar
  sub-val {n} {k} {.(LabI _)} {e'} {v} VLab = VLab
  sub-val {n} {k} {.(Abs _)} {e'} {v} VFun = VFun
  sub-val {n} {k} {.(ProdV v' _)} {e'} {v} (VProd v' v'') = VProd (sub-val v') (sub-val v'')

  -- type substitution
  [_↦_]ᵀ_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Ty {n} → Ty {n}
  [ k ↦ s ]ᵀ UnitT = UnitT
  [_↦_]ᵀ_ {n} {e} k v (Single x T) = Single (sub-val{n}{k}{e' = e}{v = v} x) ([ k ↦ v ]ᵀ T)
  [ k ↦ s ]ᵀ Label x = Label x
  [ k ↦ s ]ᵀ Pi T T₁ = Pi ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [ k ↦ s ]ᵀ Sigma T T₁ = Sigma ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [_↦_]ᵀ_ {n} {e} k v (CaseT x f) = CaseT (sub-val{n}{k}{e' = e}{v = v} x) λ l x₁ → [ k ↦ v ]ᵀ (f l x₁)

  -- variable in expression
  data _∈`_ {N : ℕ} : ℕ → Exp {N} → Set
    
  -- variable in type
  data _∈`ᵀ_ {N : ℕ} : ℕ → Ty {N} → Set

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
  -- Conversion
  data _⇒_≡_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set

  -- Type environment concatenation & required proofs
  _++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
  
  ∈++ : {n x : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} → x ∶ A ∈ Γ → x ∶ A ∈ (Γ ++ Γ')
  ⊢-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} → Γ ⊢ A → (Γ ++ Γ') ⊢ A
  ⊢⇒-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} {M : Exp {n}} → Γ ⊢ M ⇒ A → (Γ ++ Γ') ⊢ M ⇒ A
  ⊢⇐-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} {M : Exp {n}} → Γ ⊢ M ⇐ A → (Γ ++ Γ') ⊢ M ⇐ A
  ⇒≤-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A B : Ty {n}} → Γ ⇒ A ≤ B → (Γ ++ Γ') ⇒ A ≤ B
  ⇓-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A ⇓ B → (Γ ++ Γ') ⊢ A ⇓ B
  ⇒≡-++ : {n : ℕ} {Γ Γ' : TEnv {n}} {A B : Ty {n}} → Γ ⇒ A ≡ B → (Γ ++ Γ') ⇒ A ≡ B

  -- Type environment length
  length : {n : ℕ} → TEnv {n} → ℕ

  -- Implementations
  data TEnv {n} where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty) (Γ : TEnv {n}) {ok : Γ ⊢ T} → TEnv
--    _++_ : (Γ Γ' : TEnv {n}) → TEnv

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
    SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ e ⇐ A → notSingle A → Γ ⊢ Single V A
    CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {V : Val e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ⇐ Label L → Γ ⊢ CaseT V f

  data _⊢_⇐_ {n} where
    SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
               → Γ ⊢ M ⇒ A
               → Γ ⇒ A ≤ B
               → Γ ⊢ M ⇐ B

  data _⇒_≤_ {n} where
    ASubUnit : {Γ : TEnv {n}} → Γ ⇒ UnitT ≤ UnitT
    ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⇒ Label L ≤ Label L'
    ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⇒ A ≤ B → Γ ⇒ Single V A ≤ B
    ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}} {ok : Γ ⊢ A'}
             → Γ ⇒ A' ≤ A
             → ⟨ A' , Γ ⟩ {ok} ⇒ B ≤ B'
             → Γ ⇒ Pi A B ≤ Pi A' B'
    ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}} {ok : Γ ⊢ A}
                → Γ ⇒ A ≤ A'
                → ⟨ A , Γ ⟩ {ok} ⇒ B ≤ B'
                → Γ ⇒ Sigma A B ≤ Sigma A' B'
    ASubCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {V : Val e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ (f l ins) ≤ B
                 → Γ ⇒ CaseT V f ≤ B
    ASubCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ A ≤ (f l ins)
                 → Γ ⇒ A ≤ CaseT V f
    ASubCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ (f l i) ≤ B)  -- ok req constr LabAI. ok in LabAEx req constr ASubLabel. fix: ok'
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ CaseT (VVar{i = length Γ'}) f ≤ B
    ASubCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≤ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ A ≤ CaseT (VVar{i = length Γ'}) f               
             
  data _⊢_⇒_ {n} where
    VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → x ∶ A ∈ Γ → Γ ⊢ Var x ⇒ A
    UnitAI : {Γ : TEnv {n}} → Γ ⊢ UnitE ⇒ UnitT
    LabAI : {Γ : TEnv {n}} {l : Fin n} → Γ ⊢ LabI l ⇒ Single (VLab{x = l}) (Label ⁅ l ⁆)
    LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {e : Exp {n}} {V : Val e} {ins : l ∈ L} {f : ∀ l → l ∈ L → Exp {n}}
             → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
             → L' ⊆ L
             → Γ ⊢ (f l ins) ⇒ B
             → Γ ⊢ CaseE V f ⇒ B
    LabAEx : {Γ Γ' : TEnv {n}} {D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}}
             → Γ ⇒ D ≤ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (VLab{x = l}) (Label L)) , Γ ⟩ {ok = ok' l i}) ⊢ (f l i) ⇒ (f-t l i))  -- reason for ok' see ASubCaseXL
             → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseE (VVar{i = length Γ'}) f ⇒ CaseT (VVar{i = length Γ'}) f-t
    PiAI : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {M : Exp {n}} → ⟨ A , Γ ⟩ {ok} ⊢ M ⇒ B → Γ ⊢ Abs M ⇒ Pi A B
    PiAE : {Γ : TEnv {n}} {A B D : Ty {n}} {M e : Exp {n}} {V : Val e}
           → Γ ⊢ M ⇒ D
           → Γ ⊢ D ⇓ Pi A B
           → Γ ⊢ e ⇐ A
           → Γ ⊢ ([ 0 ↦ V ]ᵀ B)
           → Γ ⊢ App M V ⇒ ([ 0 ↦ V ]ᵀ B)
    SigmaAI : {Γ : TEnv {n}} {A A' B : Ty {n}} {ok : Γ ⊢ A'} {M N : Exp {n}}
              → Γ ⊢ M ⇐ A
              → Γ ⇒ A' ≤ A
              → ⟨ A' , Γ ⟩ {ok} ⊢ N ⇒ B
              → Γ ⊢ Prod M N ⇒ Sigma A B
    PairAI : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {e N : Exp {n}} {V : Val e}
             → Γ ⊢ e ⇒ A
             → Γ ⊢ N ⇒ B
             → Γ ⊢ ProdV V N ⇒ Sigma A B
    SigmaAE : {Γ : TEnv {n}} {A B C D : Ty {n}} {ok : Γ ⊢ A} {ok' : ⟨ A , Γ ⟩ {ok} ⊢ B} {M N : Exp {n}}
            → Γ ⊢ M ⇒ D
            → Γ ⊢ D ⇓ Sigma A B
            → ⟨ B , ⟨ A , Γ ⟩ {ok = ok} ⟩ {ok = ok'} ⊢ N ⇒ C
            → (¬ (0 ∈`ᵀ C)) × (¬ (1 ∈`ᵀ C))
            → Γ ⊢ LetP M N ⇒ C
    Let : {Γ : TEnv {n}} {A B : Ty {n}} {ok : Γ ⊢ A} {M N : Exp {n}}
          → ¬(0 ∈`ᵀ B)
          → Γ ⊢ M ⇒ A
          → ⟨ A , Γ ⟩ {ok} ⊢ N ⇒ B
          → Γ ⊢ LetE M N ⇒ B

  data _⊢_⇓_ {n} where
    AURefl-U : {Γ : TEnv {n}} → Γ ⊢ UnitT ⇓ UnitT
    AURefl-L : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ⇓ Label L
    AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
    AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
    AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
    AUCaseL : {Γ : TEnv {n}} {D : Ty {n}} {l : Fin n} {L L' : Subset n} {ins : l ∈ L} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {V : Val e}
              → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
              → L' ⊆ L
              → Γ ⊢ (f l ins) ⇓ D
              → Γ ⊢ CaseT V f ⇓ D
    AUCaseX-P : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≡ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseT (VVar{i = length Γ'}) fᴮ ⇓ Pi A (CaseT (VVar{i = length Γ'}) fᴰ)
    AUCaseX-S : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≡ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⊢ CaseT (VVar{i = length Γ'}) fᴮ ⇓ Sigma A (CaseT (VVar{i = length Γ'}) fᴰ)

  data _⇒_≡_ {n} where
    AConvUnit : {Γ : TEnv {n}} → Γ ⇒ UnitT ≡ UnitT
    AConvLabel : {Γ : TEnv {n}} {L : Subset n} → Γ ⇒ Label L ≡ Label L
    AConvSingle : {Γ : TEnv {n}} {A : Ty} {e : Exp {n}} {V : Val e} {j : Γ ⊢ Single V A} → Γ ⇒ Single V A ≡ Single V A
    AConvPi : {Γ : TEnv {n}} {A A' B B' : Ty} {ok : Γ ⊢ A'} → Γ ⇒ A ≡ A' → ⟨ A' , Γ ⟩ {ok} ⇒ B ≡ B' → Γ ⇒ Pi A B ≡ Pi A' B'
    AConvSigma : {Γ : TEnv {n}} {A A' B B' : Ty} {ok : Γ ⊢ A} → Γ ⇒ A ≡ A' → ⟨ A , Γ ⟩ {ok} ⇒ B ≡ B' → Γ ⇒ Sigma A B ≡ Sigma A' B'
    AConvCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {V : Val e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                  → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                  → L ⊆ L'
                  → Γ ⇒ (f l ins) ≡ B
                  → Γ ⇒ CaseT V f ≡ B
    AConvCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                  → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                  → L ⊆ L'
                  → Γ ⇒ A ≡ (f l ins)
                  → Γ ⇒ A ≡ CaseT V f               
    AConvCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ (f l i) ≡ B)
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ CaseT (VVar{i = length Γ'}) f ≡ B
    ASubCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {ok : Γ ⊢ D} {L : Subset n} {ok' : ∀ l → l ∈ L → Γ ⊢ Single (VLab{x = l}) (Label L)} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩ {ok = ok' l i}) ⇒ A ≡ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩ {ok = ok}) ⇒ A ≡ CaseT (VVar{i = length Γ'}) f

  ++-assoc : {n : ℕ} {Γ Γ' Γ'' : TEnv {n}} → (Γ'' ++ Γ') ++ Γ ≡ Γ'' ++ (Γ' ++ Γ)

  ∈++ {n} {.0} {.(⟨ A , _ ⟩)} {Γ'} {A} here = here
  ∈++ {n} {.(ℕ.suc _)} {.(⟨ _ , _ ⟩)} {Γ'} {A} (there ins) = there (∈++ ins)
  
  ⊢-++ {n} {Γ} {Γ'} {.UnitT} UnitF = UnitF
  ⊢-++ {n} {Γ} {Γ'} {.(Label _)} LabF = LabF
  ⊢-++ {n} {Γ} {Γ'} {.(Pi _ _)} (PiF j j₁) = PiF (⊢-++ j) (⊢-++ j₁)
  ⊢-++ {n} {Γ} {Γ'} {.(Sigma _ _)} (SigmaF j j₁) = SigmaF (⊢-++ j) (⊢-++ j₁)
  ⊢-++ {n} {Γ} {Γ'} {.(Single _ _)} (SingleF x x₁) = SingleF (⊢⇐-++ x) x₁
  ⊢-++ {n} {Γ} {Γ'} {.(CaseT _ _)} (CaseF{f-ok = f-ok} x) = CaseF{f-ok = λ l i → ⊢-++ (f-ok l i)} (⊢⇐-++ x)

  ⊢-refl : {n : ℕ} {Γ : TEnv {n}} {A : Ty {n}} → (ok : Γ ⊢ A) → (ok' : Γ ⊢ A) → ok ≡ ok'

  -- ⟨ A , Γ ++ Γ' ⟩ ≡ ⟨ A , Γ ⟩ ++ Γ'
  ++, : {n : ℕ} {Γ Γ' : TEnv {n}} {A : Ty {n}} {ok : Γ ⊢ A} → (⟨ A , Γ ++ Γ' ⟩) ≡ (⟨ A , Γ ⟩ {ok} ++ Γ')
  ++, {n} {Γ} {Γ'} {A} {ok} = refl
  
  -- Γ'' ++ ⟨ A , Γ ++ Γ' ⟩ ≡ (Γ'' ++ ⟨ A , Γ ⟩) ++ Γ'
  ++,' : {n : ℕ} {Γ Γ' Γ'' : TEnv {n}} {A : Ty {n}} {ok : Γ ⊢ A} {ok' : (Γ ++ Γ') ⊢ A} → Γ'' ++ ⟨ A , Γ ++ Γ' ⟩ {ok'} ≡ Γ'' ++ (⟨ A , Γ ⟩ {ok} ++ Γ')
  ++,' {n} {Γ} {Γ'} {Γ''} {A} {ok} {ok'} rewrite (⊢-refl ok' (⊢-++ {n} {Γ} {Γ'} {A} ok)) = cong (_++_ Γ'') (++,)

  ⊢⇒-++ {n} {Γ} {Γ'} {A} {.(Var _)} (VarA x) = VarA (∈++ x)
  ⊢⇒-++ {n} {Γ} {Γ'} {.UnitT} {.UnitE} UnitAI = UnitAI
  ⊢⇒-++ {n} {Γ} {Γ'} {.(Single VLab (Label ⁅ _ ⁆))} {.(LabI _)} LabAI = LabAI
  ⊢⇒-++ {n} {Γ} {Γ'} {A} {.(CaseE _ _)} (LabAEl j x j₁) = LabAEl (⊢⇒-++ j) x (⊢⇒-++ j₁)
  ⊢⇒-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {.(CaseT VVar _)} {.(CaseE VVar _)} (LabAEx{Γ = Γ}{Γ' = Γ''}{D = D}{ok = ok} x x₁)
    rewrite (++-assoc {n} {{!!}} {{!!}} {{!!}}) = {!!} -- LabAEx (⇒≤-++ x) {!!}
  ⊢⇒-++ {n} {Γ} {Γ'} {.(Pi _ _)} {.(Abs _)} (PiAI j) = PiAI (⊢⇒-++ j)
  ⊢⇒-++ {n} {Γ} {Γ'} {.([ 0 ↦ _ ]ᵀ _)} {.(App _ _)} (PiAE j x x₁ x₂) = PiAE (⊢⇒-++ j) (⇓-++ x) (⊢⇐-++ x₁) (⊢-++ x₂)
  ⊢⇒-++ {n} {Γ} {Γ'} {.(Sigma _ _)} {.(Prod _ _)} (SigmaAI x x₁ j) = SigmaAI (⊢⇐-++ x) (⇒≤-++ x₁) (⊢⇒-++ j)
  ⊢⇒-++ {n} {Γ} {Γ'} {.(Sigma _ _)} {.(ProdV _ _)} (PairAI{ok = ok} j j₁) = PairAI{ok = ⊢-++ ok} (⊢⇒-++ j) (⊢⇒-++ j₁)
  ⊢⇒-++ {n} {Γ} {Γ'} {A} {.(LetP _ _)} (SigmaAE j x j₁ x₁) = SigmaAE (⊢⇒-++ j) (⇓-++ x) (⊢⇒-++ j₁) x₁
  ⊢⇒-++ {n} {Γ} {Γ'} {A} {.(LetE _ _)} (Let x j j₁) = Let x (⊢⇒-++ j) (⊢⇒-++ j₁)

  ⊢⇐-++ {n} {Γ} {Γ'} {A} {e} (SubTypeA x x₁) = SubTypeA (⊢⇒-++ x) (⇒≤-++ x₁)

  ⇒≤-++ {n} {Γ} {Γ'} {.UnitT} {.UnitT} ASubUnit = ASubUnit
  ⇒≤-++ {n} {Γ} {Γ'} {.(Label _)} {.(Label _)} (ASubLabel x) = ASubLabel x
  ⇒≤-++ {n} {Γ} {Γ'} {.(Single _ _)} {B} (ASubSingle j) = ASubSingle (⇒≤-++ j)
  ⇒≤-++ {n} {Γ} {Γ'} {.(Pi _ _)} {.(Pi _ _)} (ASubPi j j₁) = ASubPi (⇒≤-++ j) (⇒≤-++ j₁)
  ⇒≤-++ {n} {Γ} {Γ'} {.(Sigma _ _)} {.(Sigma _ _)} (ASubSigma j j₁) = ASubSigma (⇒≤-++ j) (⇒≤-++ j₁)
  ⇒≤-++ {n} {Γ} {Γ'} {.(CaseT _ _)} {B} (ASubCaseLL x x₁ j) = ASubCaseLL (⊢⇒-++ x) x₁ (⇒≤-++ j)
  ⇒≤-++ {n} {Γ} {Γ'} {A} {.(CaseT _ _)} (ASubCaseLR x x₁ j) = ASubCaseLR (⊢⇒-++ x) x₁ (⇒≤-++ j)
  ⇒≤-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {.(CaseT VVar _)} {B} (ASubCaseXL j x) = {!!}
  ⇒≤-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {A} {.(CaseT VVar _)} (ASubCaseXR j x) = {!!}

  ⇓-++ {n} {Γ} {Γ'} {.UnitT} {.UnitT} AURefl-U = AURefl-U
  ⇓-++ {n} {Γ} {Γ'} {.(Label _)} {.(Label _)} AURefl-L = AURefl-L
  ⇓-++ {n} {Γ} {Γ'} {.(Pi _ _)} {.(Pi _ _)} AURefl-P = AURefl-P
  ⇓-++ {n} {Γ} {Γ'} {.(Sigma _ _)} {.(Sigma _ _)} AURefl-S = AURefl-S
  ⇓-++ {n} {Γ} {Γ'} {.(Single _ _)} {B} (AUSingle j) = AUSingle (⇓-++ j)
  ⇓-++ {n} {Γ} {Γ'} {.(CaseT _ _)} {B} (AUCaseL x x₁ j) = AUCaseL (⊢⇒-++ x) x₁ (⇓-++ j)
  ⇓-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {.(CaseT VVar _)} {.(Pi _ (CaseT VVar _))} (AUCaseX-P x x₁ x₂) = {!!}
  ⇓-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {.(CaseT VVar _)} {.(Sigma _ (CaseT VVar _))} (AUCaseX-S x x₁ x₂) = {!!}

  ⇒≡-++ {n} {Γ} {Γ'} {.UnitT} {.UnitT} AConvUnit = AConvUnit
  ⇒≡-++ {n} {Γ} {Γ'} {.(Label _)} {.(Label _)} AConvLabel = AConvLabel
  ⇒≡-++ {n} {Γ} {Γ'} {.(Single _ _)} {.(Single _ _)} AConvSingle = AConvSingle
  ⇒≡-++ {n} {Γ} {Γ'} {.(Pi _ _)} {.(Pi _ _)} (AConvPi j j₁) = AConvPi (⇒≡-++ j) (⇒≡-++ j₁)
  ⇒≡-++ {n} {Γ} {Γ'} {.(Sigma _ _)} {.(Sigma _ _)} (AConvSigma j j₁) = AConvSigma (⇒≡-++ j) (⇒≡-++ j₁)
  ⇒≡-++ {n} {Γ} {Γ'} {.(CaseT _ _)} {B} (AConvCaseLL x x₁ j) = AConvCaseLL (⊢⇒-++ x) x₁ (⇒≡-++ j) 
  ⇒≡-++ {n} {Γ} {Γ'} {A} {.(CaseT _ _)} (AConvCaseLR x x₁ j) = AConvCaseLR (⊢⇒-++ x) x₁ (⇒≡-++ j) 
  ⇒≡-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {.(CaseT VVar _)} {B} (AConvCaseXL x x₁) = {!!}
  ⇒≡-++ {n} {.(_ ++ ⟨ _ , _ ⟩)} {Γ'} {A} {.(CaseT VVar _)} (ASubCaseXR x x₁) = {!!}

{-
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
  J = SigmaAI {ok = LabF}
        (SubTypeA LabAI (ASubSingle {val = VLab} (ASubLabel (λ x → x)))) (ASubLabel (λ x → x)) premise

  -- The expression reduces as follows:
  --
  --   ⟨ x : {l₁} = l₁ , case x of {l₁ : ()} ⟩
  -- → ⟨⟨ l₁ , () ⟩⟩
  --
  -- Only typing rule applicable to ⟨⟨ l₁ , () ⟩⟩ is Pair-A-I
  -- {l₁} becomes S{l₁ : {l₁}}, since Pair-A-I requires type inference (⇒), not checking (⇐)
  premise' : [] ⊢ UnitE {1} ⇒ UnitT
  premise' = UnitAI
  
  J' : [] ⊢ ProdV (LabI zero) UnitE ⇒ Sigma (Single (LabI zero) (Label [l1])) UnitT
  J' = PairAI{ok = SingleF{val = VLab} (SubTypeA LabAI (ASubSingle{val = VLab} (ASubLabel (λ x → x)))) (notsingle (λ W B → λ ()))}{val = VLab} LabAI premise'
-}

 
