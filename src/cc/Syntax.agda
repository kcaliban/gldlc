------------------------------------------------------------------------
-- Syntax, decidable equality, useful predicates
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Sum
open import Data.Empty

open import Aux

-- required for termination checking on decidability of syntactic equality of functions (l : Fin n → l ∈ s → Ty) in
-- CaseT U f ≡ᵀ CaseT U' f'
-- Agda does not recognize that (f l i) is structurally smaller than (CaseT U f)
open import Size renaming (↑_ to ↑ˡ)

------------------------------------------------------------------------
-- Syntax definitions

data Exp {n : ℕ} : {i : Size} → Set
data Val {n : ℕ} : {i : Size} → Exp {n} {i} → Set
data ValU {n : ℕ} : {i : Size} → Exp {n} {i} → Set
data Ty {n : ℕ} : {i : Size} → Set
data TyG {n : ℕ} : Ty {n} → Set
data TyG' {n : ℕ} : Ty {n} → Set
data TyB {n : ℕ} : Ty {n} → Set

data Exp {n} where
  Var : {i : Size} → ℕ → Exp {n} {↑ˡ i}
  UnitE : {i : Size} → Exp {n} {↑ˡ i}
  Abs : {i : Size} → Exp {n} {i} → Exp {n} {↑ˡ i}
  App : {i : Size} → Exp {n} {i} → Exp {n} {i} → Exp {n} {↑ˡ i}
  LabI : {i : Size} → Fin n → Exp {n} {↑ˡ i}
  CaseE : {i : Size} → {s : Subset n} {e : Exp {n} {i}} → ValU {n} {i} e → (f : ∀ l → l ∈ s → Exp {n} {i}) → Exp {n} {↑ˡ i}
  Prod : {i : Size} → Exp {n} {i} → Exp {n} {i} → Exp {n} {↑ˡ i}
  ProdV : {i : Size} {e : Exp {n} {i}} → Val {n} {i} e → Exp {n} {i} → Exp {n} {↑ˡ i}
  LetP : {i : Size} → Exp {n} {i} → Exp {n} {i} → Exp {n} {↑ˡ i}
  LetE : {i : Size} → Exp {n} {i} → Exp {n} {i} → Exp {n} {↑ˡ i}
  Blame : {i : Size} → Exp {n} {↑ˡ i}
  Cast : {i : Size} → Exp {n} {i} → Ty {n} {i} → Ty {n} {i} → Exp {n} {↑ˡ i}

data Ty {n} where
  UnitT : {i : Size} → Ty {n} {↑ˡ i}
  Single : {i : Size} → {e : Exp {n} {i}} → Val {n} {i} e → Ty {n} {i} → Ty {n} {↑ˡ i}
  Label : {i : Size} → Subset n → Ty {n} {↑ˡ i}
  Pi : {i : Size} → Ty {n} {i} → Ty {n} {i} → Ty {n} {↑ˡ i}
  Sigma : {i : Size} → Ty {n} {i} → Ty {n} {i} → Ty {n} {↑ˡ i}
  CaseT : {i : Size} {s : Subset n} {e : Exp {n} {i}} → ValU {n} {i} e → (f : ∀ l → l ∈ s → Ty {n} {i}) → Ty {n} {↑ˡ i}
  Bot : {i : Size} → Ty {n} {↑ˡ i}
  Dyn : {i : Size} → Ty {n} {↑ˡ i}

data ValU {n} where
  UVar : {x : ℕ} → ValU (Var x)
  -- determinism for Cast e A B ⇒ split (ValU V) to all except VCast/VCastFun
  UValUnit : ValU UnitE
  UValLab : {x : Fin n} → ValU (LabI x)
  UValFun : {N : Exp} → ValU (Abs N)
  UValProd : {e e' : Exp} → (v : Val e) → Val e' → ValU (ProdV v e')
  UVarCast : {x : ℕ} {A B : Ty {n}} → ValU (Cast (Var x) A B)
  UValCast : {e : Exp {n}} {A B : Ty {n}} → Val e → ValU (Cast e A B)
  UBlame : ValU Blame

data Val {n} where
  VUnit : Val UnitE
  VLab : {x : Fin n} → Val (LabI x)
  VFun : {N : Exp} → Val (Abs N)
  VProd : {e e' : Exp} → (v : Val e) → Val e' → Val (ProdV v e')
  VCast : {e : Exp} {G : Ty {n}} → Val e → TyG G → Val (Cast e G Dyn)
  VCastFun : {e : Exp} {A A' B B' : Ty {n}}  → Val e → Val (Cast e (Pi A B) (Pi A' B'))

data TyG' {n} where
  GUnit : TyG' UnitT
  GLabel : {s : Subset n} → TyG' (Label s)
  GPi : TyG' (Pi Dyn Dyn)
  GSigma : TyG' (Sigma Dyn Dyn)  

data TyG {n} where
  GSingle : {e : Exp {n}} {V : Val e} {G : Ty} {tygG : TyG' G} → TyG (Single V G)
  GG' : {T : Ty {n}} → TyG' T → TyG T

data TyB {n} where
  BUnit : TyB UnitT
  BLabel : {s : Subset n} → TyB (Label s)
  BSingleLab : {l : Fin n} {L : Subset n} → TyB (Single (VLab{x = l}) (Label L))
  BSingleUnit : TyB (Single (VUnit) UnitT)
--  BDyn : TyB Dyn

------------------------------------------------------------------------
-- predicates, relations, views

data notSingle {n : ℕ} : Ty {n} → Set where
  notsingle : {A : Ty {n}} → (∀ e B → (W : Val e) → ¬ (A ≡ Single{e = e} W B)) → notSingle A

data notCase{n : ℕ} : Ty {n} → Set where
  notcase : {A : Ty {n}} → (∀ e s → (U : ValU e) → (f : (∀ l → l ∈ s → Ty)) → ¬ (A ≡ CaseT{s = s} U f)) → notCase A

notsingle-label : {n : ℕ} {L : Subset n} → notSingle (Label L)
notsingle-label {n} {L} = notsingle λ e A W ()

notsingle-dyn : {n : ℕ} → notSingle {n} Dyn
notsingle-dyn {n} = notsingle λ e A W ()

notnotsingle-single : {n : ℕ} {e : Exp {n}} {V : Val e} {A : Ty {n}} → ¬ (notSingle (Single V A))
notnotsingle-single {n} {e} {V} {A} (notsingle x) = contradiction refl (x e A V) 

notcase-label : {n : ℕ} {L : Subset n} → notCase (Label L)
notcase-label {n} = notcase λ e s U f ()

notcase-dyn : {n : ℕ} → notCase {n} Dyn
notcase-dyn {n} = notcase λ e s U f ()

-- variable in expression
data _∈`ᵀ_ {n : ℕ} : ℕ → Ty {n} → Set
data _∈`_ {n : ℕ} : ℕ → Exp {n} → Set where
  in-var : {m : ℕ} → m ∈` Var m
  in-abs : {m : ℕ} {e : Exp {n}} → (ℕ.suc m) ∈` e → m ∈` (Abs e)
  in-app : {m : ℕ} {e e' : Exp {n}} → (m ∈` e ⊎ m ∈` e') → m ∈` (App e e')
  in-casee : {x : ℕ} {s : Subset n} {f : (∀ l → l ∈ s → Exp {n})} {e : Exp {n}} {U : ValU e} → (∃₂ λ l i → x ∈` (f l i)) ⊎ x ∈` e → x ∈` CaseE U f
  in-prod : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` Prod e e'
  in-prodv : {x : ℕ} {e e' : Exp {n}} {v : Val e} → x ∈` e ⊎ x ∈` e' → x ∈` ProdV v e'  -- (Pair-A-I => e' has 0 substituted away => just x, not suc x)
  in-letp : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc (ℕ.suc x)) ∈` e' → x ∈` LetP e e'
  in-lete : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` LetE e e'
  in-cast : {x : ℕ} {e : Exp {n}} {A B : Ty {n}} → x ∈` e ⊎ x ∈`ᵀ A ⊎ x ∈`ᵀ B → x ∈` Cast e A B

-- variable in type
data _∈`ᵀ_ {n} where
  in-single : {x : ℕ} {e : Exp {n}} {A : Ty {n}} {v : Val e} → x ∈` e → x ∈`ᵀ Single v A 
  in-pi : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ (ℕ.suc n) ∈`ᵀ B → n ∈`ᵀ Pi A B
  in-pigma : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ (ℕ.suc n) ∈`ᵀ B → n ∈`ᵀ Sigma A B
  in-case : {x : ℕ} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} {e : Exp {n}} {U : ValU e} → (∃₂ λ l i → x ∈`ᵀ (f l i)) ⊎ x ∈` e → x ∈`ᵀ CaseT U f

-- generalized values incorporate values
val⊂valu : {n : ℕ} {e : Exp {n}} → Val e → ValU e
val⊂valu {n} {.UnitE} VUnit = UValUnit
val⊂valu {n} {.(LabI _)} VLab = UValLab
val⊂valu {n} {.(Abs _)} VFun = UValFun
val⊂valu {n} {.(ProdV v _)} (VProd v v₁) = UValProd v v₁
val⊂valu {n} {.(Cast _ _ Dyn)} (VCast v x) = UValCast v
val⊂valu {n} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun v) = UValCast v

-- makes differentiating between cast and non-cast subexpressions
-- in progress simpler
data CastView {n : ℕ} : Exp {n} → Set where
  cast-v : {e : Exp {n}} {A B : Ty {n}} → CastView (Cast e A B)
  other-v : {e : Exp {n}} {neq : ∀ e' A B → e ≢ Cast e' A B} → CastView e

castView : {n : ℕ} → (e : Exp {n}) → CastView e
castView (Var x) = other-v{neq = λ e' A B → λ ()}
castView UnitE = other-v{neq = λ e' A B → λ ()}
castView Blame = other-v{neq = λ e' A B → λ ()}
castView (Abs e) = other-v{neq = λ e' A B → λ ()}
castView (App e x) = other-v{neq = λ e' A B → λ ()}
castView (LabI x) = other-v{neq = λ e' A B → λ ()}
castView (CaseE x f) = other-v{neq = λ e' A B → λ ()}
castView (Prod e e₁) = other-v{neq = λ e' A B → λ ()}
castView (ProdV x e) = other-v{neq = λ e' A B → λ ()}
castView (LetP e e₁) = other-v{neq = λ e' A B → λ ()}
castView (LetE e e₁) = other-v{neq = λ e' A B → λ ()}
castView (Cast e x x₁) = cast-v

data PiView {n : ℕ} : Ty {n} → Set where
  pi-v : {A B : Ty {n}} → PiView (Pi A B)
  other-v : {A : Ty {n}} {neq : ∀ B C → A ≢ Pi B C} → PiView A

piView : {n : ℕ} → (T : Ty {n}) → PiView T
piView {n} Bot = other-v{neq = λ B C → λ ()}
piView {n} UnitT = other-v{neq = λ B C → λ ()}
piView {n} Dyn = other-v{neq = λ B C → λ ()}
piView {n} (Single x A) = other-v{neq = λ B C → λ ()}
piView {n} (Label x) = other-v{neq = λ B C → λ ()}
piView {n} (Sigma T T₁) = other-v{neq = λ B C → λ ()}
piView {n} (CaseT x f) = other-v{neq = λ B C → λ ()}
piView {n} (Pi T T₁) = pi-v

data SingleView {n : ℕ} : Ty {n} → Set where
  single-v : {A : Ty {n}} {e : Exp {n}} {V : Val e} → SingleView (Single V A)
  other-v : {A : Ty {n}} {neq : ∀ e B V → A ≢ Single{e = e} V B} → SingleView A

singleView : {n : ℕ} → (T : Ty {n}) → SingleView T
singleView {n} Bot = other-v{neq = λ e B V → λ ()}
singleView {n} UnitT = other-v{neq = λ e B V → λ ()}
singleView {n} Dyn = other-v{neq = λ e B V → λ ()}
singleView {n} (Label x) = other-v{neq = λ e B V → λ ()}
singleView {n} (Pi T T₁) = other-v{neq = λ e B V → λ ()}
singleView {n} (Sigma T T₁) = other-v{neq = λ e B V → λ ()}
singleView {n} (CaseT x f) = other-v{neq = λ e B V → λ ()}
singleView {n} (Single x A) = single-v

------------------------------------------------------------------------
-- properties, inverse lemmas

TyG'-uniqueness : {n : ℕ} {G : Ty {n}} → (x x' : TyG' G) → x ≡ x'
TyG'-uniqueness {n} {.UnitT} GUnit GUnit = refl
TyG'-uniqueness {n} {.(Label _)} GLabel GLabel = refl
TyG'-uniqueness {n} {.(Pi Dyn Dyn)} GPi GPi = refl
TyG'-uniqueness {n} {.(Sigma Dyn Dyn)} GSigma GSigma = refl

TyG-uniqueness : {n : ℕ} {G : Ty {n}} → (x x' : TyG G) → x ≡ x'
TyG-uniqueness {n} {.(Single _ _)} (GSingle{tygG = tygG}) (GSingle{tygG = tygG'})
  rewrite TyG'-uniqueness tygG tygG' = refl  
TyG-uniqueness {n} {G} (GG' x) (GG' x₁)
  rewrite TyG'-uniqueness x x₁ = refl

Val-uniqueness : {n : ℕ} {i : Size} {e : Exp {n} {i}} → (x x' : Val {n} {i} e) → x ≡ x'
Val-uniqueness {n} {.(↑ˡ ∞)} {.UnitE} VUnit VUnit = refl
Val-uniqueness {n} {.(↑ˡ ∞)} {.(LabI _)} VLab VLab = refl
Val-uniqueness {n} {.(↑ˡ ∞)} {.(Abs _)} VFun VFun = refl
Val-uniqueness {n} {.(↑ˡ ∞)} {.(ProdV v _)} (VProd v v₁) (VProd .v v')
  rewrite (Val-uniqueness v₁ v') = refl
Val-uniqueness {n} {.(↑ˡ ∞)} {.(Cast _ _ Dyn)} (VCast v x) (VCast v' x₁)
  rewrite (Val-uniqueness v v') | (TyG-uniqueness x x₁) = refl
Val-uniqueness {n} {.(↑ˡ (↑ˡ ∞))} {.(Cast _ (Pi _ _) (Pi _ _))} (VCastFun v) (VCastFun v')
  rewrite (Val-uniqueness v v') = refl

ValU-uniqueness : {n : ℕ} {i : Size} {e : Exp {n} {i}} → (x x' : ValU {n} {i} e) → x ≡ x'
ValU-uniqueness {n} {.(↑ˡ ∞)} {.(Var _)} UVar UVar = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.UnitE} UValUnit UValUnit = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.(LabI _)} UValLab UValLab = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.(Abs _)} UValFun UValFun = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.(ProdV v _)} (UValProd v x) (UValProd .v x₁)
  rewrite (Val-uniqueness x x₁) = refl
ValU-uniqueness {n} {.(↑ˡ (↑ˡ ∞))} {.(Cast (Var _) _ _)} UVarCast UVarCast = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.(Cast _ _ _)} (UValCast x) (UValCast x₁)
  rewrite (Val-uniqueness x x₁) = refl
ValU-uniqueness {n} {.(↑ˡ ∞)} {.Blame} UBlame UBlame = refl

TyG'-Pi-inv : {n : ℕ} {A B : Ty {n}} → TyG' (Pi A B) → A ≡ Dyn × B ≡ Dyn
TyG'-Pi-inv {n} {.Dyn} {.Dyn} GPi = refl , refl

TyG'-Sigma-inv : {n : ℕ} {A B : Ty {n}} → TyG' (Sigma A B) → A ≡ Dyn × B ≡ Dyn
TyG'-Sigma-inv {n} {.Dyn} {.Dyn} GSigma = refl , refl

Val-ProdV-inv : {n : ℕ} {e e' : Exp {n}} {v : Val e} → Val (ProdV v e') → Val e'
Val-ProdV-inv {n} {e} {e'} {v} (VProd .v val) = val

Val-Cast-inv : {n : ℕ} {e : Exp {n}} {A B : Ty {n}} → Val (Cast e A B) → (Val e × (TyG A × B ≡ Dyn ⊎ ∃[ A° ](∃[ B° ](∃[ A°° ](∃[ B°° ](A ≡ Pi A° B° × B ≡ Pi A°° B°°))))))
Val-Cast-inv {n} {e} {A} {.Dyn} (VCast val x) = val , (inj₁ (x , refl))
Val-Cast-inv {n} {e} {(Pi A° B°)} {(Pi A°° B°°)} (VCastFun val) = val , (inj₂ (A° , (B° , (A°° , (B°° , (refl , (refl)))))))

Pi-equiv : {n : ℕ} {A A' B B' : Ty {n}} → Pi A B ≡ Pi A' B' → A ≡ A' × B ≡ B'
Pi-equiv {n} {A} {.A} {B} {.B} refl = refl , refl

Sigma-equiv : {n : ℕ} {A A' B B' : Ty {n}} → Sigma A B ≡ Sigma A' B' → A ≡ A' × B ≡ B'
Sigma-equiv {n} {A} {.A} {B} {.B} refl = refl , refl

Single-equiv : {n : ℕ} {e e' : Exp {n}} {A A' : Ty {n}} {V : Val e} {V' : Val e'} → Single V A ≡ Single V' A' → e ≡ e'
Single-equiv {n} {e} {.e} {A} {.A} {V} {.V} refl = refl

notsingle×TyB⊂TyG' : {n : ℕ} {A : Ty {n}} → notSingle A → TyB A → TyG' A
notsingle×TyB⊂TyG' (notsingle neq) BUnit = GUnit
notsingle×TyB⊂TyG' (notsingle neq) BLabel = GLabel
notsingle×TyB⊂TyG' (notsingle neq) (BSingleLab{l = l}{L = L}) = contradiction refl (neq (LabI l) (Label L) (VLab))
notsingle×TyB⊂TyG' (notsingle neq) BSingleUnit = contradiction refl (neq UnitE UnitT VUnit)

TyG'⇒notSingle : {n : ℕ} {A : Ty {n}} → TyG' A → notSingle A
TyG'⇒notSingle {n} {.UnitT} GUnit = notsingle λ e B W → λ ()
TyG'⇒notSingle {n} {.(Label _)} GLabel = notsingle λ e B W → λ ()
TyG'⇒notSingle {n} {.(Pi Dyn Dyn)} GPi = notsingle λ e B W → λ ()
TyG'⇒notSingle {n} {.(Sigma Dyn Dyn)} GSigma = notsingle λ e B W → λ ()

TyB⊂TyG : {n : ℕ} {A : Ty {n}} → TyB A → TyG A
TyB⊂TyG BUnit = GG' GUnit
TyB⊂TyG BLabel = GG' GLabel
TyB⊂TyG BSingleLab = GSingle {tygG = GLabel}
TyB⊂TyG BSingleUnit = GSingle {tygG = GUnit}

------------------------------------------------------------------------
-- decidable


 -- Decidable syntactic equalities
_≡ᵀ?_ : {n : ℕ} {i : Size} (A B : Ty {n} {i}) → Dec (A ≡ B)
_≡ᵉ?_ : {n : ℕ} {i : Size} (e e' : Exp {n} {i}) → Dec (e ≡ e')

-- Decidable predicates
Val?_ : {n : ℕ} (e : Exp {n}) → Dec (Val e)
TyG'?_ : {n : ℕ} (A : Ty {n}) → Dec (TyG' A)
TyG?_ : {n : ℕ} (A : Ty {n}) → Dec (TyG A)
TyB?_ : {n : ℕ} (A : Ty {n}) → Dec (TyB A)

-- Predicate implementations
TyG'? Bot = no λ ()
TyG'? UnitT = yes GUnit
TyG'? Dyn = no (λ ())
TyG'? Single x A = no λ ()
TyG'? Label x = yes GLabel
TyG'? Pi x x₁
  with x ≡ᵀ? x₁
...  | no ¬p = no (λ x₂ → contradiction (≡-trans (proj₁ (TyG'-Pi-inv x₂)) (sym (proj₂ (TyG'-Pi-inv x₂)))) ¬p)
...  | yes p
     rewrite (sym p)
     with x ≡ᵀ? Dyn
...     | yes p' rewrite p' = yes GPi
...     | no ¬p' = no λ x₂ → contradiction (proj₁ (TyG'-Pi-inv x₂)) ¬p'
TyG'? Sigma x x₁
  with x ≡ᵀ? x₁
...  | no ¬p = no (λ x₂ → contradiction (≡-trans (proj₁ (TyG'-Sigma-inv x₂)) (sym (proj₂ (TyG'-Sigma-inv x₂)))) ¬p)
...  | yes p
     rewrite (sym p)
     with x ≡ᵀ? Dyn
...     | yes p' rewrite p' = yes GSigma
...     | no ¬p' = no  λ x₂ → contradiction (proj₁ (TyG'-Sigma-inv x₂)) ¬p'  
TyG'? CaseT x f = no λ ()

TyG? UnitT = yes (GG' GUnit)
TyG? Label x = yes (GG' GLabel)

TyG? Single x G
  with TyG'? G
... | yes p = yes (GSingle{tygG = p})
... | no ¬p = no ϱ
    where ϱ : TyG (Single x G) → Data.Empty.⊥
          ϱ (GSingle{tygG = tygG}) = contradiction tygG ¬p
TyG? Pi G G₁
  with TyG'? (Pi G G₁)
...  | yes p = yes (GG' p)
...  | no ¬p = no ϱ
     where ϱ : TyG (Pi G G₁) → Data.Empty.⊥
           ϱ (GG' x) = contradiction x ¬p
TyG? Sigma G G₁
  with TyG'? (Sigma G G₁)
...  | yes p = yes (GG' p)
...  | no ¬p = no ϱ
     where ϱ : TyG (Sigma G G₁) → Data.Empty.⊥
           ϱ (GG' x) = contradiction x ¬p

TyG? CaseT x f = no ϱ
  where ϱ : TyG (CaseT x f) → Data.Empty.⊥
        ϱ (GG' x) = contradiction x λ ()
TyG? Bot = no ϱ
  where ϱ : TyG Bot → Data.Empty.⊥
        ϱ (GG' x) = contradiction x λ ()
TyG? Dyn = no ϱ
  where ϱ : TyG Dyn → Data.Empty.⊥
        ϱ (GG' x) = contradiction x λ ()

Val? LetP e e₁ = no (λ ())
Val? LetE e e₁ = no (λ ())
Val? UnitE = yes VUnit
Val? Var x = no (λ ())
Val? Blame = no (λ ())
Val? Abs e = yes VFun
Val? App e x = no (λ ())
Val? LabI x = yes VLab
Val? CaseE x f = no (λ ())
Val? Prod e e₁ = no (λ ())
Val? ProdV x e
  with Val? e
...  | yes v = yes (VProd x v)
...  | no ¬v = no (λ x₁ → contradiction (Val-ProdV-inv x₁) ¬v)  
Val? Cast e A B
  with Val? e
...  | no ¬v = no (λ x₂ → contradiction (proj₁ (Val-Cast-inv x₂)) ¬v)
Val? Cast e A B | yes v
  with piView A | piView B
Val? Cast e (Pi A° B°) (Pi A°° B°°) | yes v | pi-v | pi-v = yes (VCastFun v)
Val? Cast e A (Pi A°° B°°) | yes v | other-v{neq = neq} | pi-v = no ϱ
  where ϱ : ¬ Val (Cast e A (Pi A°° B°°))
        ϱ v°
          with (Val-Cast-inv v°)
        ...  | fst , inj₂ (fst' , snd , thd , fth , ffth , sxth) = contradiction ffth (neq fst' snd )
Val? Cast e A B | yes v | _ | other-v{neq = neq}
  with TyG? A | B ≡ᵀ? Dyn
...  | yes tyg | yes eq rewrite eq = yes (VCast v tyg)
Val? Cast e A B | yes v | _ | other-v{neq = neq} | no ¬tyg | yes eq = no ϱ
  where ϱ : ¬ Val (Cast e A B)
        ϱ v°
          with (Val-Cast-inv v°)
        ...  | fst , inj₁ (fst' , snd) = contradiction fst' ¬tyg
        ...  | fst , inj₂ (fst' , snd , thd , fth , ffth , sxth) = contradiction (≡-trans (sym sxth) eq) (λ ())
Val? Cast e A B | yes v | _ | other-v{neq = neq} | _ | no ¬eq = no ϱ
  where ϱ : ¬ Val (Cast e A B)
        ϱ v°
          with (Val-Cast-inv v°)
        ...  | fst , inj₁ (fst₁ , snd) = contradiction snd ¬eq
        ...  | fst , inj₂ (fst' , snd , thd , fth , ffth , sxth) = contradiction sxth (neq thd fth)

TyB? UnitT = yes BUnit
TyB? Label x = yes BLabel
TyB? Single VLab (Label x) = yes BSingleLab
TyB? Single VUnit UnitT = yes BSingleUnit

TyB? Single VUnit (Single x A) = no λ ()
TyB? Single VUnit (Label x) = no λ ()
TyB? Single VUnit (Pi A A₁) = no λ ()
TyB? Single VUnit (Sigma A A₁) = no λ ()
TyB? Single VUnit (CaseT x f) = no λ ()
TyB? Single VUnit Bot = no λ ()
TyB? Single VUnit Dyn = no λ ()
TyB? Single VLab UnitT = no λ ()
TyB? Single VLab (Single x A) = no λ ()
TyB? Single VLab (Pi A A₁) = no λ ()
TyB? Single VLab (Sigma A A₁) = no λ ()
TyB? Single VLab (CaseT x f) = no λ ()
TyB? Single VLab Bot = no λ ()
TyB? Single VLab Dyn = no λ ()
TyB? Single VFun A = no λ ()
TyB? Single (VProd x x₁) A = no λ ()
TyB? Single (VCast x x₁) A = no λ ()
TyB? Single (VCastFun x) A = no λ ()
TyB? Pi A A₁ = no λ ()
TyB? Sigma A A₁ = no λ ()
TyB? CaseT x f = no λ ()
TyB? Bot = no λ ()
TyB? Dyn = no λ ()

-- Syntactic equality implementations
UnitE ≡ᵉ? UnitE = yes refl
Blame ≡ᵉ? Blame = yes refl

_≡ᵉ?_{n} .{↑ˡ i} (Var{i} m) (Var m')
  with m Data.Nat.≟ m'
...  | yes p rewrite p = yes refl
...  | no ¬p = no ϱ
     where
     ϱ : ¬ (Var{n}{i} m ≡ Var{n}{i} m')
     ϱ refl = contradiction refl ¬p
Abs e ≡ᵉ? Abs e'
  with e ≡ᵉ? e'
...  | yes p rewrite p = yes refl
...  | no ¬p = no ϱ
     where
     ϱ : ¬ (Abs e ≡ Abs e')
     ϱ refl = contradiction refl ¬p
LabI l ≡ᵉ? LabI l'
  with l Data.Fin.≟ l'
...  | yes p rewrite p = yes refl
...  | no ¬p = no ϱ
     where
     ϱ : ¬ (LabI l ≡ LabI l')
     ϱ refl = contradiction refl ¬p

_≡ᵉ?_ {n} .{↑ˡ i} (App{i} e e*) (App e' e**)
  with e ≡ᵉ? e' | e* ≡ᵉ? e**
...  | yes p | yes p' rewrite p | p' = yes refl
... | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (App e e* ≡ App e' e**)
  ϱ refl = contradiction refl ¬p'
... | no ¬p | _ = no ϱ'
  where
  ϱ' :  ¬ (App e e* ≡ App e' e**)
  ϱ' refl = contradiction refl ¬p 
_≡ᵉ?_ {n} .{↑ˡ i} (ProdV{i}{e = e*} v e) (ProdV{e = e**} v' e')
  with e ≡ᵉ? e' | e* ≡ᵉ? e**
...  | yes p | yes p' rewrite p | p' | (Val-uniqueness v v') = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (ProdV v e ≡ ProdV v' e')
  ϱ refl = contradiction refl ¬p'
... | no ¬p | _ = no ϱ
  where
  ϱ :  ¬ (ProdV v e ≡ ProdV v' e')
  ϱ refl = contradiction refl ¬p  

Prod e₁ e₂ ≡ᵉ? Prod e₁' e₂'
  with e₁ ≡ᵉ? e₁' | e₂ ≡ᵉ? e₂'
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (Prod e₁ e₂ ≡ Prod e₁' e₂')
  ϱ refl = contradiction refl ¬p'
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (Prod e₁ e₂ ≡ Prod e₁' e₂')
  ϱ refl = contradiction refl ¬p
LetP e₁ e₂ ≡ᵉ? LetP e₁' e₂'
  with e₁ ≡ᵉ? e₁' | e₂ ≡ᵉ? e₂'
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (LetP e₁ e₂ ≡ LetP e₁' e₂')
  ϱ refl = contradiction refl ¬p'
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (LetP e₁ e₂ ≡ LetP e₁' e₂')
  ϱ refl = contradiction refl ¬p  
LetE e₁ e₂ ≡ᵉ? LetE e₁' e₂'
  with e₁ ≡ᵉ? e₁' | e₂ ≡ᵉ? e₂'
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (LetE e₁ e₂ ≡ LetE e₁' e₂')
  ϱ refl = contradiction refl ¬p'
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (LetE e₁ e₂ ≡ LetE e₁' e₂')
  ϱ refl = contradiction refl ¬p  

_≡ᵉ?_ {n} .{↑ˡ i} (CaseE{i = i}{s = s}{e = e} U f) (CaseE{i = .i}{s = s'}{e = e'} U' f')
  with e ≡ᵉ? e' | s ≡ˢ? s'
...  | yes p | yes p'
     rewrite p | p'
     with (_≡ᶠ?_{dec = λ a a' → _≡ᵉ?_{i = i} a a' } f f')  -- needs s ≡ s'
...     | yes p'' rewrite p'' | (ValU-uniqueness U U') = yes refl
...     | no ¬p'' = no ϱ
        where 
        ϱ : ¬ (_≡_ (CaseE{i = i}{s = s'}{e = e'} U f) (CaseE{i = i}{s = s'}{e = e'} U' f'))
        ϱ refl = contradiction refl ¬p''
_≡ᵉ?_ {n} .{↑ˡ i} (CaseE{i = i}{s = s}{e = e} U f) (CaseE{i = .i}{s = s'}{e = e'} U' f') | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (_≡_ (CaseE{i = i}{s = s}{e = e} U f) (CaseE{i = i}{s = s'}{e = e'} U' f'))
  ϱ refl = contradiction refl ¬p'
_≡ᵉ?_ {n} .{↑ˡ i} (CaseE{i = i}{s = s}{e = e} U f) (CaseE{i = .i}{s = s'}{e = e'} U' f') | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (_≡_ (CaseE{i = i}{s = s}{e = e} U f) (CaseE{i = i}{s = s'}{e = e'} U' f'))
  ϱ refl = contradiction refl ¬p

Cast e A B ≡ᵉ? Cast e' A' B'
  with e ≡ᵉ? e' | A ≡ᵀ? A' | B ≡ᵀ? B'
...  | yes p | yes p' | yes p'' rewrite p | p' | p'' = yes refl
...  | no ¬p | _ | _ = no ϱ
  where
  ϱ : ¬ (Cast e A B ≡ Cast e' A' B')
  ϱ refl = contradiction refl ¬p
...  | _ | no ¬p' | _ = no ϱ
  where
  ϱ : ¬ (Cast e A B ≡ Cast e' A' B')
  ϱ refl = contradiction refl ¬p'
...  | _ | _ | no ¬p'' = no ϱ
  where
  ϱ : ¬ (Cast e A B ≡ Cast e' A' B')
  ϱ refl = contradiction refl ¬p''

-- automatically generated (hence the creative naming of subexpressions) boring cases

Var i ≡ᵉ? UnitE = no λ ()
Var i ≡ᵉ? Blame = no λ ()
Var i ≡ᵉ? Abs e = no λ ()
Var i ≡ᵉ? App e* v = no λ ()
Var i ≡ᵉ? LabI l = no λ ()
Var i ≡ᵉ? CaseE U f = no λ ()
Var i ≡ᵉ? Prod e1 e2 = no λ ()
Var i ≡ᵉ? ProdV e` w = no λ ()
Var i ≡ᵉ? LetP e' e'' = no λ ()
Var i ≡ᵉ? LetE e# e## = no λ ()
Var i ≡ᵉ? Cast e- A B = no λ ()
UnitE ≡ᵉ? Var i = no λ ()
UnitE ≡ᵉ? Blame = no λ ()
UnitE ≡ᵉ? Abs e = no λ ()
UnitE ≡ᵉ? App e* v = no λ ()
UnitE ≡ᵉ? LabI l = no λ ()
UnitE ≡ᵉ? CaseE U f = no λ ()
UnitE ≡ᵉ? Prod e1 e2 = no λ ()
UnitE ≡ᵉ? ProdV e` w = no λ ()
UnitE ≡ᵉ? LetP e' e'' = no λ ()
UnitE ≡ᵉ? LetE e# e## = no λ ()
UnitE ≡ᵉ? Cast e- A B = no λ ()
Blame ≡ᵉ? Var i = no λ ()
Blame ≡ᵉ? UnitE = no λ ()
Blame ≡ᵉ? Abs e = no λ ()
Blame ≡ᵉ? App e* v = no λ ()
Blame ≡ᵉ? LabI l = no λ ()
Blame ≡ᵉ? CaseE U f = no λ ()
Blame ≡ᵉ? Prod e1 e2 = no λ ()
Blame ≡ᵉ? ProdV e` w = no λ ()
Blame ≡ᵉ? LetP e' e'' = no λ ()
Blame ≡ᵉ? LetE e# e## = no λ ()
Blame ≡ᵉ? Cast e- A B = no λ ()
Abs e ≡ᵉ? Var i = no λ ()
Abs e ≡ᵉ? UnitE = no λ ()
Abs e ≡ᵉ? Blame = no λ ()
Abs e ≡ᵉ? App e* v = no λ ()
Abs e ≡ᵉ? LabI l = no λ ()
Abs e ≡ᵉ? CaseE U f = no λ ()
Abs e ≡ᵉ? Prod e1 e2 = no λ ()
Abs e ≡ᵉ? ProdV e` w = no λ ()
Abs e ≡ᵉ? LetP e' e'' = no λ ()
Abs e ≡ᵉ? LetE e# e## = no λ ()
Abs e ≡ᵉ? Cast e- A B = no λ ()
App e* v ≡ᵉ? Var i = no λ ()
App e* v ≡ᵉ? UnitE = no λ ()
App e* v ≡ᵉ? Blame = no λ ()
App e* v ≡ᵉ? Abs e = no λ ()
App e* v ≡ᵉ? LabI l = no λ ()
App e* v ≡ᵉ? CaseE U f = no λ ()
App e* v ≡ᵉ? Prod e1 e2 = no λ ()
App e* v ≡ᵉ? ProdV e` w = no λ ()
App e* v ≡ᵉ? LetP e' e'' = no λ ()
App e* v ≡ᵉ? LetE e# e## = no λ ()
App e* v ≡ᵉ? Cast e- A B = no λ ()
LabI l ≡ᵉ? Var i = no λ ()
LabI l ≡ᵉ? UnitE = no λ ()
LabI l ≡ᵉ? Blame = no λ ()
LabI l ≡ᵉ? Abs e = no λ ()
LabI l ≡ᵉ? App e* v = no λ ()
LabI l ≡ᵉ? CaseE U f = no λ ()
LabI l ≡ᵉ? Prod e1 e2 = no λ ()
LabI l ≡ᵉ? ProdV e` w = no λ ()
LabI l ≡ᵉ? LetP e' e'' = no λ ()
LabI l ≡ᵉ? LetE e# e## = no λ ()
LabI l ≡ᵉ? Cast e- A B = no λ ()
CaseE U f ≡ᵉ? Var i = no λ ()
CaseE U f ≡ᵉ? UnitE = no λ ()
CaseE U f ≡ᵉ? Blame = no λ ()
CaseE U f ≡ᵉ? Abs e = no λ ()
CaseE U f ≡ᵉ? App e* v = no λ ()
CaseE U f ≡ᵉ? LabI l = no λ ()
CaseE U f ≡ᵉ? Prod e1 e2 = no λ ()
CaseE U f ≡ᵉ? ProdV e` w = no λ ()
CaseE U f ≡ᵉ? LetP e' e'' = no λ ()
CaseE U f ≡ᵉ? LetE e# e## = no λ ()
CaseE U f ≡ᵉ? Cast e- A B = no λ ()
Prod e1 e2 ≡ᵉ? Var i = no λ ()
Prod e1 e2 ≡ᵉ? UnitE = no λ ()
Prod e1 e2 ≡ᵉ? Blame = no λ ()
Prod e1 e2 ≡ᵉ? Abs e = no λ ()
Prod e1 e2 ≡ᵉ? App e* v = no λ ()
Prod e1 e2 ≡ᵉ? LabI l = no λ ()
Prod e1 e2 ≡ᵉ? CaseE U f = no λ ()
Prod e1 e2 ≡ᵉ? ProdV e` w = no λ ()
Prod e1 e2 ≡ᵉ? LetP e' e'' = no λ ()
Prod e1 e2 ≡ᵉ? LetE e# e## = no λ ()
Prod e1 e2 ≡ᵉ? Cast e- A B = no λ ()
ProdV e` w ≡ᵉ? Var i = no λ ()
ProdV e` w ≡ᵉ? UnitE = no λ ()
ProdV e` w ≡ᵉ? Blame = no λ ()
ProdV e` w ≡ᵉ? Abs e = no λ ()
ProdV e` w ≡ᵉ? App e* v = no λ ()
ProdV e` w ≡ᵉ? LabI l = no λ ()
ProdV e` w ≡ᵉ? CaseE U f = no λ ()
ProdV e` w ≡ᵉ? Prod e1 e2 = no λ ()
ProdV e` w ≡ᵉ? LetP e' e'' = no λ ()
ProdV e` w ≡ᵉ? LetE e# e## = no λ ()
ProdV e` w ≡ᵉ? Cast e- A B = no λ ()
LetP e' e'' ≡ᵉ? Var i = no λ ()
LetP e' e'' ≡ᵉ? UnitE = no λ ()
LetP e' e'' ≡ᵉ? Blame = no λ ()
LetP e' e'' ≡ᵉ? Abs e = no λ ()
LetP e' e'' ≡ᵉ? App e* v = no λ ()
LetP e' e'' ≡ᵉ? LabI l = no λ ()
LetP e' e'' ≡ᵉ? CaseE U f = no λ ()
LetP e' e'' ≡ᵉ? Prod e1 e2 = no λ ()
LetP e' e'' ≡ᵉ? ProdV e` w = no λ ()
LetP e' e'' ≡ᵉ? LetE e# e## = no λ ()
LetP e' e'' ≡ᵉ? Cast e- A B = no λ ()
LetE e# e## ≡ᵉ? Var i = no λ ()
LetE e# e## ≡ᵉ? UnitE = no λ ()
LetE e# e## ≡ᵉ? Blame = no λ ()
LetE e# e## ≡ᵉ? Abs e = no λ ()
LetE e# e## ≡ᵉ? App e* v = no λ ()
LetE e# e## ≡ᵉ? LabI l = no λ ()
LetE e# e## ≡ᵉ? CaseE U f = no λ ()
LetE e# e## ≡ᵉ? Prod e1 e2 = no λ ()
LetE e# e## ≡ᵉ? ProdV e` w = no λ ()
LetE e# e## ≡ᵉ? LetP e' e'' = no λ ()
LetE e# e## ≡ᵉ? Cast e- A B = no λ ()
Cast e- A B ≡ᵉ? Var i = no λ ()
Cast e- A B ≡ᵉ? UnitE = no λ ()
Cast e- A B ≡ᵉ? Blame = no λ ()
Cast e- A B ≡ᵉ? Abs e = no λ ()
Cast e- A B ≡ᵉ? App e* v = no λ ()
Cast e- A B ≡ᵉ? LabI l = no λ ()
Cast e- A B ≡ᵉ? CaseE U f = no λ ()
Cast e- A B ≡ᵉ? Prod e1 e2 = no λ ()
Cast e- A B ≡ᵉ? ProdV e` w = no λ ()
Cast e- A B ≡ᵉ? LetP e' e'' = no λ ()
Cast e- A B ≡ᵉ? LetE e# e## = no λ ()

Bot ≡ᵀ? Bot = yes refl
UnitT ≡ᵀ? UnitT = yes refl
Dyn ≡ᵀ? Dyn = yes refl

Label L ≡ᵀ? Label L'
  with L ≡ˢ? L'
...  | yes p rewrite p = yes refl
...  | no ¬p = no ϱ
  where
  ϱ : ¬(Label L ≡ Label L')
  ϱ refl = contradiction refl ¬p

Single{e = e} V A ≡ᵀ? Single{e = e'} V' A'
  with e ≡ᵉ? e' | A ≡ᵀ? A'
...  | yes p | yes p' rewrite p | p' | Val-uniqueness V V' = yes refl
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (Single V A ≡ Single V' A')
  ϱ refl = contradiction refl ¬p
...  | _ | no ¬p = no ϱ
  where
  ϱ : ¬ (Single V A ≡ Single V' A')
  ϱ refl = contradiction refl ¬p    
Pi nA B ≡ᵀ? Pi nA' B'
  with nA ≡ᵀ? nA' | B ≡ᵀ? B'
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (Pi nA B ≡ Pi nA' B')
  ϱ refl = contradiction refl ¬p'
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (Pi nA B ≡ Pi nA' B')
  ϱ refl = contradiction refl ¬p  
Sigma nA B ≡ᵀ? Sigma nA' B'
  with nA ≡ᵀ? nA' | B ≡ᵀ? B'
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (Sigma nA B ≡ Sigma nA' B')
  ϱ refl = contradiction refl ¬p'
...  | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (Sigma nA B ≡ Sigma nA' B')
  ϱ refl = contradiction refl ¬p    
_≡ᵀ?_ {n} .{↑ˡ i} (CaseT{i = i}{s = s}{e = e} U f) (CaseT{i = .i}{s = s'}{e = e'} U' f')
  with e ≡ᵉ? e' | s ≡ˢ? s'
...  | yes p | yes p'
     rewrite p | p'
     with (_≡ᶠ?_{dec = λ a a' → _≡ᵀ?_{i = i} a a' } f f')  -- needs s ≡ s'
...     | yes p'' rewrite p'' | (ValU-uniqueness U U') = yes refl
...     | no ¬p'' = no ϱ
        where 
        ϱ : ¬ (_≡_ (CaseT{i = i}{s = s'}{e = e'} U f) (CaseT{i = i}{s = s'}{e = e'} U' f'))
        ϱ refl = contradiction refl ¬p''
_≡ᵀ?_ {n} .{↑ˡ i} (CaseT{i = i}{s = s}{e = e} U f) (CaseT{i = .i}{s = s'}{e = e'} U' f') | yes p | no ¬p' = no ϱ
  where
  ϱ : ¬ (_≡_ (CaseT{i = i}{s = s}{e = e} U f) (CaseT{i = i}{s = s'}{e = e'} U' f'))
  ϱ refl = contradiction refl ¬p'
_≡ᵀ?_ {n} .{↑ˡ i} (CaseT{i = i}{s = s}{e = e} U f) (CaseT{i = .i}{s = s'}{e = e'} U' f') | no ¬p | _ = no ϱ
  where
  ϱ : ¬ (_≡_ (CaseT{i = i}{s = s}{e = e} U f) (CaseT{i = i}{s = s'}{e = e'} U' f'))
  ϱ refl = contradiction refl ¬p

-- automatically generated (hence the creative naming of subexpressions) boring cases

Bot ≡ᵀ? UnitT = no λ ()
Bot ≡ᵀ? Dyn = no λ ()
Bot ≡ᵀ? Single V A = no λ ()
Bot ≡ᵀ? Label L = no λ ()
Bot ≡ᵀ? Pi nA B = no λ ()
Bot ≡ᵀ? Sigma nA' B' = no λ ()
Bot ≡ᵀ? CaseT U f = no λ ()
UnitT ≡ᵀ? Bot = no λ ()
UnitT ≡ᵀ? Dyn = no λ ()
UnitT ≡ᵀ? Single V A = no λ ()
UnitT ≡ᵀ? Label L = no λ ()
UnitT ≡ᵀ? Pi nA B = no λ ()
UnitT ≡ᵀ? Sigma nA' B' = no λ ()
UnitT ≡ᵀ? CaseT U f = no λ ()
Dyn ≡ᵀ? Bot = no λ ()
Dyn ≡ᵀ? UnitT = no λ ()
Dyn ≡ᵀ? Single V A = no λ ()
Dyn ≡ᵀ? Label L = no λ ()
Dyn ≡ᵀ? Pi nA B = no λ ()
Dyn ≡ᵀ? Sigma nA' B' = no λ ()
Dyn ≡ᵀ? CaseT U f = no λ ()
Single V A ≡ᵀ? Bot = no λ ()
Single V A ≡ᵀ? UnitT = no λ ()
Single V A ≡ᵀ? Dyn = no λ ()
Single V A ≡ᵀ? Label L = no λ ()
Single V A ≡ᵀ? Pi nA B = no λ ()
Single V A ≡ᵀ? Sigma nA' B' = no λ ()
Single V A ≡ᵀ? CaseT U f = no λ ()
Label L ≡ᵀ? Bot = no λ ()
Label L ≡ᵀ? UnitT = no λ ()
Label L ≡ᵀ? Dyn = no λ ()
Label L ≡ᵀ? Single V A = no λ ()
Label L ≡ᵀ? Pi nA B = no λ ()
Label L ≡ᵀ? Sigma nA' B' = no λ ()
Label L ≡ᵀ? CaseT U f = no λ ()
Pi nA B ≡ᵀ? Bot = no λ ()
Pi nA B ≡ᵀ? UnitT = no λ ()
Pi nA B ≡ᵀ? Dyn = no λ ()
Pi nA B ≡ᵀ? Single V A = no λ ()
Pi nA B ≡ᵀ? Label L = no λ ()
Pi nA B ≡ᵀ? Sigma nA' B' = no λ ()
Pi nA B ≡ᵀ? CaseT U f = no λ ()
Sigma nA' B' ≡ᵀ? Bot = no λ ()
Sigma nA' B' ≡ᵀ? UnitT = no λ ()
Sigma nA' B' ≡ᵀ? Dyn = no λ ()
Sigma nA' B' ≡ᵀ? Single V A = no λ ()
Sigma nA' B' ≡ᵀ? Label L = no λ ()
Sigma nA' B' ≡ᵀ? Pi nA B = no λ ()
Sigma nA' B' ≡ᵀ? CaseT U f = no λ ()
CaseT U f ≡ᵀ? Bot = no λ ()
CaseT U f ≡ᵀ? UnitT = no λ ()
CaseT U f ≡ᵀ? Dyn = no λ ()
CaseT U f ≡ᵀ? Single V A = no λ ()
CaseT U f ≡ᵀ? Label L = no λ ()
CaseT U f ≡ᵀ? Pi nA B = no λ ()
CaseT U f ≡ᵀ? Sigma nA' B' = no λ ()
