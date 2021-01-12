-- {-# OPTIONS --show-implicit #-} -- in case of emergency
module ldlc-cc-algo where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.Fin hiding (cast)
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
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

open import aux

----------------------------------------------------------------------

module syntx where
  data Exp {n : ℕ} : Set
  data Val {n : ℕ} : Exp {n} → Set
  data ValU {n : ℕ} : Exp {n} → Set
  data Ty {n : ℕ} : Set
  data TyG {n : ℕ} : Ty {n} → Set
  data TyNf {n : ℕ} : Ty {n} → Set
  data _∈`ᵀ_ {n : ℕ} : ℕ → Ty {n} → Set

  data Exp {n} where
    Var : ℕ → Exp {n}
    UnitE : Exp {n}
    Bot : Exp {n}
    Abs : Exp {n} → Exp {n}
    App : {e : Exp {n}} → Exp {n} → Val e → Exp {n}
    LabI : Fin n → Exp {n}
    CaseE : {s : Subset n} {e : Exp {n}} → ValU e → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    ProdV : {e : Exp {n}} → Val e → Exp {n} → Exp {n}
    LetP : Exp {n} → Exp {n} → Exp {n}
    LetE : Exp {n} → Exp {n} → Exp {n}
    Cast : Exp {n} → Ty {n} → Ty {n} → Exp {n}

  data Ty {n} where
    UnitT : Ty
    Dyn : Ty
    Single : {e : Exp {n}} → Val e → Ty {n} → Ty
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    CaseT : {s : Subset n} {e : Exp {n}} → ValU e → (f : ∀ l → l ∈ s → Ty {n}) → Ty

  data TyNf {n} where
    NfDyn : TyNf Dyn
    NfUnit : TyNf UnitT
    NfLabel : {s : Subset n} → TyNf (Label s)
    NfPi : {A B : Ty {n}} {nfA : TyNf A} → TyNf (Pi A B)
    NfSigma : {A B : Ty {n}} {nfA : TyNf A} → TyNf (Sigma A B)
    
  data ValU {n} where
    UVal : {e : Exp {n}} → Val e → ValU e
    UCast : {e : Exp {n}} {G : Ty {n}} → Val e → TyG G → ValU (Cast e Dyn G)
    
  data Val {n} where
    VUnit : Val UnitE
    VBot : Val Bot
    VVar : {i : ℕ} → Val (Var i)
    VLab : {x : Fin n} → Val (LabI x)
    VFun : {N : Exp} → Val (Abs N)
    VProd : {e e' : Exp} → (v : Val e) → Val e' → Val (ProdV v e')
    VCast : {e : Exp} {G : Ty {n}} {v : Val e} {g : TyG G} → Val (Cast e G Dyn)
    VCastFun : {e : Exp} {nA nA' B B' : Ty {n}} {v : Val e} {nfA : TyNf nA} {nfA' : TyNf nA'} → Val (Cast e (Pi nA B) (Pi nA' B'))

  data TyG {n} where
    GUnit : TyG UnitT
    GLabel : {s : Subset n} → TyG (Label s)
    GPi : TyG (Pi Dyn Dyn)
    GSigma : TyG (Sigma Dyn Dyn)
    GSingle : {l : Fin n} {s : Subset n} {ins : l ∈ s} → TyG (Single (VLab{x = l}) (Label s))

  -- Negative predicates
  data notSingle {n : ℕ} : Ty {n} → Set where
    notsingle : {A : Ty {n}} → (∀ e B → (W : Val e) → ¬ (A ≡ Single{e = e} W B)) → notSingle A

  data notCase{n : ℕ} : Ty {n} → Set where
    notcase : {A : Ty {n}} → (∀ e s → (U : ValU e) → (f : (∀ l → l ∈ s → Ty)) → ¬ (A ≡ CaseT{s = s} U f)) → notCase A

  notsingle-label : {n : ℕ} {L : Subset n} → notSingle (Label L)
  notsingle-label {n} {L} = notsingle λ e B W ()

  notsingle-dyn : {n : ℕ} → notSingle {n} Dyn
  notsingle-dyn {n} = notsingle λ e B W ()

  -- variable in expression
  data _∈`_ {n : ℕ} : ℕ → Exp {n} → Set where
  {-
    in-var : {x : ℕ} → x ∈` (Var x)
    in-abs : {x : ℕ} {e : Exp {n}} → x ∈` e → (ℕ.suc x) ∈` (Abs e)
    in-app : {x : ℕ} {e e' : Exp {n}} {v : Val e'} → x ∈` e ⊎ x ∈` e' → x ∈` App e v
    in-casee : {x : ℕ} {s : Subset n} {f : (∀ l → l ∈ s → Exp {n})} {e : Exp {n}} {v : Val e} → (∃₂ λ l i → x ∈` (f l i)) ⊎ x ∈` e → {!!}
    in-prod : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` Prod e e'
    in-prodv : {x : ℕ} {e e' : Exp {n}} {v : Val e} → x ∈` e ⊎ x ∈` e' → x ∈` ProdV v e'  -- (Pair-A-I => e' has 0 substituted away => just x, not suc x)
    in-letp : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc (ℕ.suc x)) ∈` e' → x ∈` LetP e e'
    in-lete : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` LetE e e'
  -}

  -- variable in type
  data _∈`ᵀ_ {n} where
  {-
    in-single : {x : ℕ} {e : Exp {n}} {v : Val e} {A : Ty {n}} → x ∈` e ⊎ x ∈`ᵀ A → x ∈`ᵀ Single v A
    in-pi : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ n ∈`ᵀ B → n ∈`ᵀ Pi A B
    in-pigma : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ n ∈`ᵀ B → n ∈`ᵀ Sigma A B
    in-case : {x : ℕ} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} {e : Exp {n}} {v : Val e} → (∃₂ λ l i → x ∈`ᵀ (f l i)) ⊎ x ∈` e → {!!}
  -}

  -- Decidable Type equality
  _≡ᵀ?_ : {n : ℕ} (A B : Ty {n}) → Dec (A ≡ B)
  _≡ᵉ?_ : {n : ℕ} (e e' : Exp {n}) → Dec (e ≡ e')

  Val?_ : {n : ℕ} (e : Exp {n}) → Dec (Val e)

  TyG?_ : {n : ℕ} (A : Ty {n}) → Dec (TyG A)
  TyG? UnitT = {!!}
  TyG? Dyn = {!!}
  TyG? Single VLab (Label s) = yes GSingle
  TyG? Single x A = no {!!} 
  TyG? Label x = yes GLabel
  TyG? Pi A A₁ = {!!}
  TyG? Sigma A A₁ = {!!}
  TyG? CaseT x f = {!!}

  Val? Var x = yes VVar
  Val? UnitE = yes VUnit
  Val? Bot = yes VBot
  Val? Abs e = yes VFun
  Val? App e x = no (λ ())
  Val? LabI x = yes VLab
  Val? CaseE x f = no (λ ())
  Val? Prod e e₁ = no (λ ())
  Val? ProdV x e
    with Val? e
  ...  | yes v = yes (VProd x v)
  ...  | no ¬v = no {!!}
  Val? LetP e e₁ = no (λ ())
  Val? LetE e e₁ = no (λ ())
  Val? Cast e x x₁ = {!!}

  UnitT ≡ᵀ? UnitT = yes refl
  Dyn ≡ᵀ? Dyn = yes refl
  Single x A ≡ᵀ? Single x' A' = {!!}
  Label x ≡ᵀ? Label x'
    with x ≡ˢ? x'
  ...  | yes p rewrite p = yes refl
  ...  | no ¬p = no {!!}
--  ...  | yes p = ?
  Pi A A₁ ≡ᵀ? B = {!!}
  Sigma A A₁ ≡ᵀ? B = {!!}
  CaseT x f ≡ᵀ? B = {!!}

  Var x ≡ᵉ? e' = {!!}
  UnitE ≡ᵉ? e' = {!!}
  Bot ≡ᵉ? e' = {!!}
  Abs e ≡ᵉ? e' = {!!}
  App e x ≡ᵉ? e' = {!!}
  LabI x ≡ᵉ? LabI x'
    with x Data.Fin.≟ x'
  ...  | yes p rewrite p = yes refl
  ...  | no ¬p = no {!!}
  CaseE x f ≡ᵉ? e' = {!!}
  Prod e e₁ ≡ᵉ? e' = {!!}
  ProdV x e ≡ᵉ? e' = {!!}
  LetP e e₁ ≡ᵉ? e' = {!!}
  LetE e e₁ ≡ᵉ? e' = {!!}
  Cast e x x₁ ≡ᵉ? e' = {!!}


----------------------------------------------------------------------
----------------------------------------------------------------------

module substitution where
  ---- Shifting and substitution
  open syntx

  -- shifting
  ↑ᴺ_,_[_] : ℤ → ℕ → ℕ → ℕ
  ↑ᴺ d , c [ x ]
    with (x <ᴺ? c)
  ...  | yes p = x
  ...  | no ¬p = ∣ ℤ.pos x +ᶻ d ∣ᴺ

  ↑_,_[_] : ∀ {n} → ℤ → ℕ → Exp {n} → Exp {n}
  ↑ᵀ_,_[_] : ∀ {n} → ℤ → ℕ → Ty {n} → Ty {n}

  shift-val : ∀ {n d c} {e : Exp {n}} → Val e → Val (↑ d , c [ e ])
  shift-valu : ∀ {n d c} {e : Exp {n}} → ValU e → ValU (↑ d , c [ e ])
  shift-tyg : ∀ {n d c} {A : Ty {n}} → TyG A → TyG (↑ᵀ d , c [ A ])
  shift-tynf : ∀ {n d c} {A : Ty {n}} → TyNf A → TyNf (↑ᵀ d , c [ A ])  

  ↑ d , c [ UnitE ] = UnitE
  ↑ d , c [ Bot ] = Bot
  ↑ d , c [ Cast e A B ] = Cast ↑ d , c [ e ] ↑ᵀ d , c [ A ] ↑ᵀ d , c [ B ] 
  ↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t v ] = App (↑ d , c [ t ]) (shift-val{d = d}{c = c} v)
  ↑ d , c [ LabI x ] = LabI x
  ↑ d , c [ CaseE{e = e} U f ] = CaseE (shift-valu{d = d}{c = c} U) (λ l x → ↑ d , c [ f l x ])
  ↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ ProdV e e' ] = ProdV (shift-val{d = d}{c = c} e) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ LetP e e' ] = LetP (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])
  ↑ d , c [ LetE e e' ] = LetE (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

  ↑ᵀ d , c [ UnitT ] = UnitT
  ↑ᵀ d , c [ Dyn ] = Dyn
  ↑ᵀ d , c [ Single x A ] = Single (shift-val{d = d}{c = c} x) ↑ᵀ d , c [ A ]
  ↑ᵀ d , c [ Label x ] = Label x
  ↑ᵀ d , c [ Pi A A₁ ] = Pi ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
  ↑ᵀ d , c [ Sigma A A₁ ] = Sigma ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
  ↑ᵀ d , c [ CaseT x f ] = CaseT (shift-valu{d = d}{c = c} x) (λ l x₁ → ↑ᵀ d , c [ f l x₁ ])

  shift-val {n} {d} {c} {.UnitE} VUnit = VUnit
  shift-val {n} {d} {c} {.Bot} VBot = VBot
  shift-val {n} {d} {c} {(Cast e A B)} (VCast{v = v}{g = g}) = VCast{v = shift-val v}{g = shift-tyg g}
  shift-val {n} {d} {c} {(Cast e A B)} (VCastFun{v = v}{nfA = nfA}{nfA' = nfA'}) = VCastFun{v = shift-val v}{nfA = shift-tynf nfA}{nfA' = shift-tynf nfA'}
  shift-val {n} {d} {c} {.(Var _)} VVar = VVar
  shift-val {n} {d} {c} {.(LabI _)} VLab = VLab
  shift-val {n} {d} {c} {.(Abs _)} VFun = VFun
  shift-val {n} {d} {c} {.(ProdV V _)} (VProd V V₁) = VProd (shift-val V) (shift-val V₁)

  shift-valu {n} {d} {c} {e} (UVal x) = UVal (shift-val x)
  shift-valu {n} {d} {c} {.(Cast _ Dyn _)} (UCast v g) = UCast (shift-val v) (shift-tyg g)

  shift-tyg {n} {d} {c} {.UnitT} GUnit = GUnit
  shift-tyg {n} {d} {c} {.(Label _)} GLabel = GLabel
  shift-tyg {n} {d} {c} {.(Pi Dyn Dyn)} GPi = GPi
  shift-tyg {n} {d} {c} {.(Sigma Dyn Dyn)} GSigma = GSigma

  shift-tynf {n} {d} {c} {.Dyn} NfDyn = NfDyn
  shift-tynf {n} {d} {c} {.UnitT} NfUnit = NfUnit
  shift-tynf {n} {d} {c} {.(Label _)} NfLabel = NfLabel
  shift-tynf {n} {d} {c} {.(Pi _ _)} (NfPi{nfA = nfA}) = NfPi{nfA = shift-tynf nfA}
  shift-tynf {n} {d} {c} {.(Sigma _ _)} (NfSigma{nfA = nfA}) = NfSigma{nfA = shift-tynf nfA}

  -- shorthands
  ↑¹[_] : ∀ {n} → Exp {n} → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑ⱽ¹[_] : ∀ {n} {e : Exp {n}} → Val e → Val (↑ (ℤ.pos 1) , 0 [ e ])
  ↑ⱽ¹[_] {n} {e} v = shift-val v

  ↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  [_↦_]_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Exp {n} → Exp {n}
  [_↦_]ᵀ_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Ty {n} → Ty {n}
  
  sub-val : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → Val e → Val ([ k ↦ v ] e)
  sub-valu : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → ValU e → ValU ([ k ↦ v ] e)
  sub-tyg : ∀ {n k} {A : Ty {n}} {e : Exp {n}} {v : Val e} → TyG A → TyG ([ k ↦ v ]ᵀ A)
  sub-tynf : ∀ {n k} {A : Ty {n}} {e : Exp {n}} {v : Val e} → TyNf A → TyNf ([ k ↦ v ]ᵀ A)
  
  [_↦_]_ {n} {e} k v (Var x)
    with (_≟ᴺ_ x k)
  ...  | yes p = e
  ...  | no ¬p = Var x
  [ k ↦ v ] UnitE = UnitE
  [ k ↦ v ] Bot = Bot
  [ k ↦ v ] Cast e A B = Cast ([ k ↦ v ] e) ([ k ↦ v ]ᵀ A) ([ k ↦ v ]ᵀ B)
  [ k ↦ v ] Abs e = Abs (([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e))
  [_↦_]_ {n} {e'} k v (App{e = e₁} e v') = App ([ k ↦ v ] e) (sub-val{n}{k}{e₁}{e'}{v} v') -- ([ k ↦ v ] e₁)
  [ k ↦ v ] LabI x = LabI x
  [_↦_]_ {n} {e} k v (CaseE v' f) = CaseE (sub-valu{n}{k}{e' = e}{v = v} v') (λ l x₁ → [ k ↦ v ] (f l x₁))
  [ k ↦ v ] Prod e e₁ = Prod ([ k ↦ v ] e) ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)
  [_↦_]_ {n} {e} k v (ProdV v' e') = ProdV (sub-val{n}{k}{e' = e}{v = v} v') ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e')
  [ k ↦ v ] LetP e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ shift-val{d = ℤ.pos 2}{c = 0} v ] e₁)
  [ k ↦ v ] LetE e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc k) ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)

  [ k ↦ s ]ᵀ UnitT = UnitT
  [ k ↦ s ]ᵀ Dyn = Dyn
  [_↦_]ᵀ_ {n} {e} k v (Single x T) = Single (sub-val{n}{k}{e' = e}{v = v} x) ([ k ↦ v ]ᵀ T)
  [ k ↦ s ]ᵀ Label x = Label x
  [ k ↦ s ]ᵀ Pi T T₁ = Pi ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [ k ↦ s ]ᵀ Sigma T T₁ = Sigma ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [_↦_]ᵀ_ {n} {e} k v (CaseT x f) = CaseT (sub-valu{n}{k}{e' = e}{v = v} x) λ l x₁ → [ k ↦ v ]ᵀ (f l x₁)

  sub-val {n} {k} {.UnitE} {e'} {v} VUnit = VUnit
  sub-val {n} {k} {.Bot} {e'} {v} VBot = VBot
  sub-val {n} {k} {Cast e A B} {e'} {v} (VCast{v = v'}{g = g}) = VCast{v = sub-val v'}{g = sub-tyg g}
  sub-val {n} {k} {Cast e A B} {e'} {v} (VCastFun{v = v'}{nfA = nfA}{nfA' = nfA'}) = VCastFun{v = sub-val v'}{nfA = sub-tynf nfA}{nfA' = sub-tynf nfA'}
  sub-val {n} {k} {(Var i)} {e'} {v} VVar
    with (_≟ᴺ_ i k)
  ...  | yes p = v
  ...  | no ¬p = VVar
  sub-val {n} {k} {.(LabI _)} {e'} {v} VLab = VLab
  sub-val {n} {k} {.(Abs _)} {e'} {v} VFun = VFun
  sub-val {n} {k} {.(ProdV v' _)} {e'} {v} (VProd v' v'') = VProd (sub-val v') (sub-val v'')

  sub-valu {n} {k} {e} {e'} {v} (UVal x) = UVal (sub-val x)
  sub-valu {n} {k} {.(Cast _ Dyn _)} {e'} {v} (UCast v' g) = UCast (sub-val v') (sub-tyg g)

  sub-tyg {n} {k} {.UnitT} {e} {v} GUnit = GUnit
  sub-tyg {n} {k} {.(Label _)} {e} {v} GLabel = GLabel
  sub-tyg {n} {k} {.(Pi Dyn Dyn)} {e} {v} GPi = GPi
  sub-tyg {n} {k} {.(Sigma Dyn Dyn)} {e} {v} GSigma = GSigma

  sub-tynf {n} {k} {.Dyn} {e} {v} NfDyn = NfDyn
  sub-tynf {n} {k} {.UnitT} {e} {v} NfUnit = NfUnit
  sub-tynf {n} {k} {.(Label _)} {e} {v} NfLabel = NfLabel
  sub-tynf {n} {k} {.(Pi _ _)} {e} {v} (NfPi{nfA = nfA}) = NfPi{nfA = sub-tynf nfA}
  sub-tynf {n} {k} {.(Sigma _ _)} {e} {v} (NfSigma{nfA = nfA}) = NfSigma{nfA = sub-tynf nfA}

----------------------------------------------------------------------
----------------------------------------------------------------------

module typing+semantics where
  open syntx
  open substitution

  -- Type environment
  data TEnv {n : ℕ} : Set where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty {n}) (Γ : TEnv {n}) → TEnv

  _++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
  [] ++ Γ' = Γ'
  ⟨ T , Γ ⟩ ++ Γ' = ⟨ T , Γ ++ Γ' ⟩

  ++-assoc : {n : ℕ} {Γ Γ' Γ'' : TEnv {n}} → Γ ++ (Γ' ++ Γ'') ≡ (Γ ++ Γ') ++ Γ''
  ++-assoc {n} {[]} {Γ'} {Γ''} = refl
  ++-assoc {n} {⟨ T , Γ ⟩} {Γ'} {Γ''} = cong (λ x → ⟨ T , x ⟩) (++-assoc{n}{Γ}{Γ'}{Γ''})

  length : {n : ℕ} → TEnv {n} → ℕ
  length {n} [] = zero
  length {n} ⟨ T , Γ ⟩ = ℕ.suc (length Γ)

  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set where
    here : {T : Ty} {Γ : TEnv} → 0 ∶ T ∈ ⟨ T , Γ ⟩
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩

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
  -- Type reduction
  data _↠_ {n : ℕ} : Ty {n} → Ty {n} → Set
  -- Expression reduction
  data _⇨_ {n : ℕ} : Exp {n} → Exp {n} → Set
  -- precise cast function
  cast : {n : ℕ} → Ty {n} → Ty {n} → Ty {n} → Ty {n}

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
    LabF : {Γ : TEnv {n}} {L : Subset n} → ⊢ Γ ok → Γ ⊢ Label L
    PiF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Pi A B
    SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Sigma A B
    SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} → ⊢ Γ ok → Γ ⊢ e ▷ A → notSingle A → Γ ⊢ Single V A
    CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {U : ValU e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ◁ Label L → Γ ⊢ CaseT U f

  data _⊢_◁_ {n} where
    SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
               → Γ ⊢ M ▷ A
               → Γ ⊢ A ≤ᵀ B
               → Γ ⊢ M ◁ B

  data _⊢_≤ᵀ_ {n} where
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
    ASubCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
               → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) f ≤ᵀ B
    ASubCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ A ≤ᵀ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩) ⊢ A ≤ᵀ CaseT (UVal (VVar{i = length Γ'})) f
    ASubCaseXLDyn : {Γ Γ' : TEnv {n}} {B : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                  → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (f l i) ≤ᵀ B)
                  → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f ≤ᵀ B
    ASubCaseXRDyn : {Γ Γ' : TEnv {n}} {A : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                  → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ A ≤ᵀ (f l i))
                  → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ A ≤ᵀ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f 


  data _⊢_▷_ {n} where
    BotA : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ Bot ▷ A
    VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ▷ A
    CastA : {Γ : TEnv {n}} {A B A' B' : Ty {n}} {M : Exp {n}} → Γ ⊢ M ▷ A' → Γ ∣ Γ ⊢ A ~ B → cast A' A B ≡ B' → Γ ⊢ Cast M A B ▷ B'
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
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (VLab{x = l}) (Label L)) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
             → Θ ⊢ CaseE (UVal (VVar{i = length Γ'})) f ▷ CaseT (UVal (VVar{i = length Γ'})) f-t
    LabAExDyn : {Γ Γ' Θ : TEnv {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ Dyn , Γ ⟩)}
                → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (f l i) ▷ (f-t l i))
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
    Let : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
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
    AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
    AUCaseL : {Γ : TEnv {n}} {D : Ty {n}} {l : Fin n} {L L' : Subset n} {ins : l ∈ L} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {U : ValU e}
              → Γ ⊢ e ▷ Single (VLab{x = l}) (Label L')
              → L' ⊆ L
              → Γ ⊢ (f l ins) ⇓ D
              → Γ ⊢ CaseT U f ⇓ D         
    AUCaseX-P : {Γ Γ' : TEnv {n}} {D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {l₀ : Fin n}
              → Γ ⊢ D ≤ᵀ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
              → (∀ l l' → (i : l ∈ L) → (i' : l' ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴬ l i) ≡ᵀ (fᴬ l' i'))
              → (ins : l₀ ∈ L)
              → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) fᴮ ⇓ Pi (fᴬ l₀ ins) (CaseT (UVal (VVar{i = length Γ'})) fᴰ)
    AUCaseX-S : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {l₀ : Fin n}
              → Γ ⊢ D ≤ᵀ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
              → (∀ l l' → (i : l ∈ L) → (i' : l' ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴬ l i) ≡ᵀ (fᴬ l' i'))
              → (ins : l₀ ∈ L)
              → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) fᴮ ⇓ Sigma (fᴬ l₀ ins) (CaseT (UVal (VVar{i = length Γ'})) fᴰ)
    AUCaseXDyn-P : {Γ Γ' : TEnv {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {l₀ : Fin n}
                   → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
                   → (∀ l l' → (i : l ∈ L) → (i' : l' ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (fᴬ l i) ≡ᵀ (fᴬ l' i'))
                   → (ins : l₀ ∈ L)
                   → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴮ ⇓ Pi (fᴬ l₀ ins) (CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴰ)
    AUCaseXDyn-S : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})} {l₀ : Fin n}
                   → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
                   → (∀ l l' → (i : l ∈ L) → (i' : l' ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (fᴬ l i) ≡ᵀ (fᴬ l' i'))
                   → (ins : l₀ ∈ L)
                   → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴮ ⇓ Sigma (fᴬ l₀ ins) (CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) fᴰ)

  data _⊢_≡ᵀ_ {n} where
    AConvUnit : {Γ : TEnv {n}} → Γ ⊢ UnitT ≡ᵀ UnitT
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
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (f l i) ≡ᵀ B)
               → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) f ≡ᵀ B
    AConvCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ A ≡ᵀ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩) ⊢ A ≡ᵀ CaseT (UVal (VVar{i = length Γ'})) f
    AConvCaseXLDyn : {Γ Γ' : TEnv {n}} {B : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                     → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ (f l i) ≡ᵀ B)
                     → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f ≡ᵀ B
    AConvCaseXRDyn : {Γ Γ' : TEnv {n}} {A : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                     → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ⊢ A ≡ᵀ (f l i))
                    → (Γ' ++ ⟨ Dyn , Γ ⟩) ⊢ A ≡ᵀ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f

  data _∣_⊢_~_ {n} where
    AConsDynL : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ Dyn ~ A
    AConsDynR : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ Dyn
    AConsRefl : {Γ Γ' : TEnv {n}} {A : Ty {n}} → ⊢ Γ ∣ Γ' ok → Γ ∣ Γ' ⊢ A ~ A
    AConsSingleL : {Γ Γ' : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ∣ Γ' ⊢ A ~ B → Γ ⊢ e ▷ A → Γ ∣ Γ' ⊢ Single V A ~ B
    AConsSingleR : {Γ Γ' : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ∣ Γ' ⊢ A ~ B → Γ' ⊢ e ▷ A → Γ ∣ Γ' ⊢ A ~ Single V B
    AConsPi : {Γ Γ' : TEnv {n}} {A A' B B' : Ty {n}}
              → ⟨ A , Γ ⟩ ∣ ⟨ A' , Γ' ⟩ ⊢ B ~ B'
              → Γ ∣ Γ' ⊢ Pi A B ~ Pi A' B'
    AConsSigma : {Γ Γ' : TEnv {n}} {A A' B B' : Ty {n}}
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
    AConvCaseXL : {Γ Γ' Δ Δ' : TEnv {n}} {B D D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ D ≤ᵀ Label L
               → (∀ l → (i : l ∈ L) → (Δ ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ∣ (Δ' ++ ⟨ cast (Single (VLab{x = l}) (Label L)) (Label L) D' , Γ' ⟩) ⊢ (f l i) ~ B)
               → (Δ ++ ⟨ D , Γ ⟩) ∣ (Δ' ++ ⟨ D' , Γ' ⟩) ⊢ CaseT (UVal (VVar{i = length Γ'})) f ~ B
    AConvCaseXR : {Γ Γ' Δ Δ' : TEnv {n}} {A D D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⊢ D' ≤ᵀ Label L
               → (∀ l → (i : l ∈ L) → (Δ ++ ⟨ cast (Single (VLab{x = l}) (Label L)) (Label L) D , Γ ⟩) ∣ (Δ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ' ⟩) ⊢ A ~ (f l i))
               → (Δ ++ ⟨ D , Γ ⟩) ∣ (Δ' ++ ⟨ D' , Γ' ⟩) ⊢ A ~ CaseT (UVal (VVar{i = length Γ'})) f
    AConvCaseXLDyn : {Γ Γ' Δ Δ' : TEnv {n}} {B D' : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                     → (∀ l → (i : l ∈ L)
                       → (Δ ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ ⟩) ∣ (Δ' ++ ⟨ cast (Single (VLab{x = l}) (Label L)) (Label L) D' , Γ' ⟩) ⊢ (f l i) ~ B)
                     → (Δ ++ ⟨ Dyn , Γ ⟩) ∣ (Δ' ++ ⟨ D' , Γ' ⟩) ⊢ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f ~ B
    AConvCaseXRDyn : {Γ Γ' Δ Δ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
                     → (∀ l → (i : l ∈ L)
                       → (Δ ++ ⟨ cast (Single (VLab{x = l}) (Label L)) (Label L) D , Γ ⟩) ∣ (Δ' ++ ⟨ Single (VCast{G = Label L}{v = VLab{x = l}}{g = GLabel}) (Dyn) , Γ' ⟩) ⊢ A ~ (f l i))
                     → (Δ ++ ⟨ D , Γ ⟩) ∣ (Δ' ++ ⟨ Dyn , Γ' ⟩) ⊢ A ~ CaseT (UCast{G = Label L} (VVar{i = length Γ'}) GLabel) f

  data _↠_ {n} where
    ξ-Case : {e e' : Exp {n}} {U : ValU e} {U' : ValU e'} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} → e ⇨ e' → CaseT U f ↠ CaseT U' f
    ξ-Pi : {A A' B : Ty {n}} → A ↠ A' → Pi A B ↠ Pi A' B
    ξ-Sigma : {A A' B : Ty {n}} → A ↠ A' → Sigma A B ↠ Sigma A' B
    β-Case : {l : Fin n} {s : Subset n} {ins : l ∈ s} {f : ∀ l → l ∈ s → Ty {n}} → CaseT (UVal (VLab{x = l})) f ↠ f l ins

  data _⇨_ {n} where
    ξ-App : {e₁ e₁' e : Exp {n}} {v : Val e} → e₁ ⇨ e₁' → App e₁ v ⇨ App e₁' v
    ξ-LetE : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → LetE e₁ e ⇨ LetE e₁' e
    ξ-Prod : {e₁ e₁' e : Exp {n}} → e₁ ⇨ e₁' → Prod e₁ e ⇨ Prod e₁' e
    ξ-ProdV : {e e₂ e₂' : Exp {n}} {v : Val e} → e₂ ⇨ e₂' → ProdV v e₂ ⇨ ProdV v e₂'
    ξ-LetP : {e₁ e₁' e₂ : Exp {n}} → e₁ ⇨ e₁' → LetP e₁ e₂ ⇨ LetP e₁' e₂
    ξ-Cast : {e₁ e₂ : Exp {n}} {A B : Ty {n}} → e₁ ⇨ e₂ → Cast e₁ A B ⇨ Cast e₂ A B
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
    Cast-Collapse-Single-Label : {e : Exp {n}} {v : Val e} {L L' : Subset n} {l : Fin n} → l ∈ L → L ⊆ L' → Cast (Cast e (Single (VLab{x = l}) (Label L)) Dyn) Dyn (Label L') ⇨ e
    Cast-Collapse : {e : Exp {n}} {v : Val e} {G : Ty {n}} {g : TyG G} → Cast (Cast e G Dyn) Dyn G ⇨ e
    Cast-Collide : {e : Exp {n}} {v : Val e} {G H : Ty {n}} → G ≢ H → Cast (Cast e G Dyn) Dyn H ⇨ Bot  -- Bot as blame?
    Cast-Reduce-L : {e : Exp {n}} {v : Val e} {A A' B : Ty {n}} → A ↠ A' → Cast e A B ⇨ Cast e A' B
    Cast-Reduce-R : {e : Exp {n}} {v : Val e} {A B B' : Ty {n}} → B ↠ B' → Cast e A B ⇨ Cast e A B'
    Cast-Factor-L : {e : Exp {n}} {v : Val e} {G nA : Ty {n}} {g : TyG G} {nfA : TyNf nA} → ([] ∣ [] ⊢ G ~ nA) → [] ⊢ nA → G ≢ nA → nA ≢ Dyn → Cast e nA Dyn ⇨ Cast (Cast e nA G) G Dyn
    Cast-Factor-R : {e : Exp {n}} {v : Val e} {G nB : Ty {n}} {g : TyG G} {nfB : TyNf nB} → ([] ∣ [] ⊢ G ~ nB) → [] ⊢ nB → G ≢ nB → nB ≢ Dyn → Cast e Dyn nB ⇨ Cast (Cast e Dyn G) G nB

  -- Big step semantics, cast function
  Env : {ℕ} → Set
  Env {n} = List (Exp {n})

  access : {n : ℕ} {Γ : Env {n}} → (m : ℕ) → All Val Γ → Σ (Exp {n}) Val
  access {n} {.[]} m [] = Bot , VBot
  access {n} {(e ∷ Γ)} zero (px ∷ venv) = e , px
  access {n} {.(_ ∷ _)} (ℕ.suc m) (px ∷ venv) = access m venv

  castreduce : {n : ℕ} {e : Exp {n}} → Val e → Ty {n} → Ty {n} → Σ (Exp {n}) Val
  -- Cast-Collapse-Label-Label
  castreduce {n} {e} (VCast{e = e'}{Label s}{v}{g}) Dyn (Label s')
    with s ⊆? s'
  ...  | yes p = e' , v
  ...  | no ¬p = Bot , VBot
  -- Cast-Collapse-Single-Label
  castreduce {n} {e} (VCast{e'}{Single (VLab{x = x}) (Label s)}{v}{g}) Dyn (Label s')
    with x ∈? s | s ⊆? s'
  ...  | yes ins | yes subset = e' , v
  ...  | _ | _ = Bot , VBot
  -- Collapse/Collide
  castreduce {n} {e} (VCast{e = e'}{G}{v}{g}) Dyn B
    with G ≡ᵀ? B
  ...  | yes p = e' , v
  ...  | no ¬p = Bot , VBot
  -- Illegal
  castreduce {n} {e} (VCast{e = e'}{G}{v}{g}) A B = Bot , VBot
  -- Collapse/Collide
  castreduce {n} {e} (VCastFun{e = e'}{nA}{nA'}{B}{B'}{v}) A B*
    with A ≡ᵀ? Pi nA' B'
  ...  | no ¬p = Bot , VBot
  ...  | yes p
       with B* ≡ᵀ? Pi nA B
  ...     | yes p' = e' , v
  ...     | no ¬p' = Bot , VBot
  -- Base Cases
  castreduce {n} {e} V UnitT UnitT = e , V
  castreduce {n} {e} V Dyn Dyn = e , V    
  castreduce {n} {e} V (Label s) (Label s')
    with (s ⊆? s')
  ...  | yes p = e , V
  ...  | no ¬p = Bot , VBot
  -- Value
  castreduce {n} {e} V G Dyn
    with TyG? G
  ...  | yes p = (Cast e G Dyn) , (VCast{v = V}{g = p})
  ...  | no ¬p = Bot , VBot
  -- Illegal
  castreduce {n} {e} V A B = Bot , VBot

  -- If term stuck, result is Bot / Singleton with Bot as expression
  _∶_⇓ : {n : ℕ} {Γ : Env {n}} (venv : All Val Γ) (e : Exp {n}) →  Σ (Exp {n}) Val
  _∶_⇓ᵀ : {n : ℕ} {Γ : Env {n}} (venv : All Val Γ) (T : Ty {n}) → Ty {n}

  _∶_⇓ {n} {Γ} venv (Var x) = access x venv 
  _∶_⇓ {n} {Γ} venv UnitE = UnitE , VUnit
  _∶_⇓ {n} {Γ} venv Bot = Bot , VBot
  _∶_⇓ {n} {Γ} venv (Abs e) = Abs e , VFun
  -- Cast-Function
  _∶_⇓ {n} {Γ} venv (App{e = e'} (Cast (Abs e) A B) x)
    with venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ | venv ∶ e' ⇓   -- evaluate "x" again, could be a variable
  ...  | Pi Â B̂ | Pi Â' B̂' | ê , v̂ = venv ∶ LetE (Cast e' Â' Â) (Cast (App (Abs e) (VVar{i = 0})) B̂ ([ 0 ↦ v̂ ]ᵀ B̂')) ⇓
  ...  | _ | _ | _ = Bot , VBot
  _∶_⇓ {n} {Γ} venv (App{e = e'} e x)   -- evaluate "x" again, could be a variable
    with venv ∶ e ⇓ | venv ∶ e' ⇓
  ...  | (Abs e*) , VFun | ê , v̂ = (v̂ ∷ venv) ∶ e* ⇓ 
  ...  | e* | _  = Bot , VBot
  _∶_⇓ {n} {Γ} venv (LabI x) = LabI x , VLab
  _∶_⇓ {n} {Γ} venv (CaseE{s = s}{e = e} x f)
    with venv ∶ e ⇓
  ...  | (LabI l) , VLab
       with l ∈? s
  ...     | yes ins = venv ∶ (f l ins) ⇓ 
  ...     | no ¬ins = Bot , VBot
  _∶_⇓ {n} {Γ} venv (CaseE{e = e} x f) | e' = Bot , VBot
  _∶_⇓ {n} {Γ} venv (Prod e e₁)
    with venv ∶ e ⇓
  ...  | e' , v
       with ((v ∷ venv) ∶ e₁ ⇓)
  ...     | e₁' , v' = (ProdV v e₁') , (VProd v v')
  _∶_⇓ {n} {Γ} venv (ProdV x e)
    with venv ∶ e ⇓
  ...  | e' , v = (ProdV x e') , (VProd x v)
  _∶_⇓ {n} {Γ} venv (LetP e e')
    with venv ∶ e ⇓
  ...  | ProdV{e = e*} v₁ e₂ , VProd .v₁ v₂
       with venv ∶ e* ⇓ | venv ∶ e₂ ⇓   -- same as in App, what if one of them is a "Var"?
  ...     | e₁' , v₁' | e₂' , v₂' = (v₂' ∷ (v₁' ∷ venv)) ∶ e' ⇓
  _∶_⇓ {n} {Γ} venv (LetP e e') | e'' = Bot , VBot
  _∶_⇓ {n} {Γ} venv (LetE e e₁)
    with venv ∶ e ⇓
  ...  | e' , v = _∶_⇓{Γ = e' ∷ Γ} (v ∷ venv) e₁
  _∶_⇓ {n} {Γ} venv (Cast e A B)
    with venv ∶ e ⇓ | venv ∶ A ⇓ᵀ | venv ∶ B ⇓ᵀ
  -- Cast-Pair
  ...  | ProdV{e = e₁} v₁ e₂ , VProd .v₁ v₂ | Sigma Â B̂ | Sigma Â' B̂' = venv ∶ LetE (Cast e₁ Â Â') (ProdV (VVar{i = 0}) (Cast e₂ ([ 0 ↦ v₁ ]ᵀ B̂) B̂')) ⇓
  ...  | e' , v' | A' | B' = castreduce v' A' B'

  venv ∶ UnitT ⇓ᵀ = UnitT
  venv ∶ Dyn ⇓ᵀ = Dyn
  venv ∶ Single x A ⇓ᵀ = Single x A
  venv ∶ Label x ⇓ᵀ = Label x
  venv ∶ Pi A A₁ ⇓ᵀ
    with venv ∶ A ⇓ᵀ
  ...  | A' = Pi A' A₁
  venv ∶ Sigma A A₁ ⇓ᵀ
    with venv ∶ A ⇓ᵀ
  ...  | A' = Sigma A' A₁
  venv ∶ CaseT{s = s}{e = e} x f ⇓ᵀ
    with venv ∶ e ⇓
  ...  | (LabI l) , VLab
         with l ∈? s
  ...       | yes ins = venv ∶ (f l ins) ⇓ᵀ
  ...       | no nins = CaseT{e = LabI l} (UVal VLab) f
  venv ∶ CaseT{e = e} x f ⇓ᵀ | e' , v' = CaseT{e = e'} (UVal v') f

  cast (Single {e = e} V A) (Single {e = e'} W A') B
    with A ≡ᵀ? A' | e ≡ᵉ? e'
  ...  | yes p | yes p' = B
  ...  | _ | _ = Single VBot B
  cast (Single {e = e} V A) A' B
    with A ≡ᵀ? A' | [] ∶ (Cast e A B) ⇓
  ...  | yes p | e' , W = Single W B
  ...  | no ¬p | e' , W = Single VBot B
  cast A A' B
    with A ≡ᵀ? A'
  ...  | yes p = B
  ...  | no ¬p = Single VBot B

----------------------------------------------------------------------
----------------------------------------------------------------------

module examples where
  open syntx
  open substitution
  open typing+semantics

  [l] : Subset 2
  [l] = inside ∷ (outside ∷ [])

  [l'] : Subset 2
  [l'] = outside ∷ (inside ∷ [])

  [l,l'] : Subset 2
  [l,l'] = inside ∷ (inside ∷ [])

  -- Big step semantics, cast reduction
  -- (λx . case (x : * => {l}) {l : ()}) (l : S{l : {l}} => *) ⇓ ()
  example-case : proj₁ ([] ∶ App (Abs (CaseE{s = [l]} (UCast{G = Label [l]} (VVar{i = 0}) GLabel) λ l x → UnitE))
                                 (VCast{e = LabI zero}{G = Single (VLab{x = zero}) (Label [l])}{v = VLab}{g = GSingle{ins = here}}) ⇓) ≡ UnitE
  example-case = refl

  --  l : S{l : {l}} => Unit ⇓ ⊥
  example-bad : proj₁ ([] ∶ Cast (LabI zero) (Single (VLab{x = zero}) (Label [l])) UnitT ⇓) ≡ Bot
  example-bad = refl    

  -- (λx . (case (x : * => [l,l']) of {l : (), l' : LabI l'}) : Π(x : *)(case ...) => Π(x : {l, l'})(case ...)) l
  f : (l : Fin 2) → l ∈ [l,l'] → Exp {2}
  f zero i = UnitE
  f (Fin.suc zero) i = LabI (Fin.suc zero)
  
  fᵀ : (l : Fin 2) → l ∈ [l,l'] → Ty {2}
  fᵀ zero i = UnitT
  fᵀ (Fin.suc zero) i = Single (VLab{x = Fin.suc zero}) (Label [l'])
  
  example-function-f : Exp {2}
  example-function-f = Abs (CaseE (UCast{e = Var 0}{G = Label [l,l']} VVar GLabel) f)
  
  example-function-f-cast : Exp {2}
  example-function-f-cast = Cast example-function-f (Pi Dyn ((CaseT (UCast{e = Var 0}{G = Label [l,l']} VVar GLabel) fᵀ))) (Pi (Label [l,l']) (CaseT (UVal (VVar{i = 0})) fᵀ))

  
  example-function : proj₁ ([] ∶ App example-function-f-cast (VLab{x = zero}) ⇓) ≡ UnitE
  example-function = refl
  
  -- Cast function
  -- cast S{l : {l}} {l} {l, l'} => S{l : {l, l'}}
  _ : cast (Single (VLab{x = zero}) (Label [l])) (Label [l]) (Label [l,l']) ≡ Single (VLab{x = zero}) (Label [l,l'])
  _ = refl


  -- ∅ ⊢ ⟨ l : S{l : {l}} ⇒ * , case (0 : * => {l, l'}) of {l : (), l' : LabI l'} ⟩
  --     : Σ(0 : *)(case (0 : * => {l, l'}) of {l : Unit, l' : S{l' : {l'}}}) ⇒ Σ(0 : {l, l'})(case 0 of {l : Unit, l' : S{l' : {l'}}}
  --     ▷ Σ(0 : {l, l'})(case 0 of {l : Unit, l' : S{l' : {l'}}}
  B : Ty {2}
  B = CaseT (UCast{G = Label [l,l']} (VVar{i = 0}) GLabel) fᵀ

  B' : Ty {2}
  B' = CaseT (UVal (VVar{i = 0})) fᵀ

  T : Ty {2}
  T = Sigma Dyn B

  T' : Ty {2}
  T' = Sigma (Label [l,l']) B'
  
  e : Exp {2}
  e = Cast (Prod (Cast (LabI zero) (Single (VLab{x = zero}) (Label [l])) Dyn) (CaseE{s = [l,l']} (UCast{G = Label [l,l']} (VVar{i = 0}) GLabel) f))
      T T' 

  lawl : cast (Single{n = 2} (VLab{x = zero}) (Label ⁅ zero ⁆)) (Label ⁅ zero ⁆) Dyn ≡ Single (VCast{e = LabI zero}{G =  Label ⁅ zero ⁆}{v = VLab}{g = GLabel}) Dyn
  lawl = refl
  
  lol : (l : Fin 2) (i : l ∈ [l,l']) → cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) Dyn ≡ Single (VCast{e = LabI l}{G = Label ⁅ l ⁆}{v = VLab}{g = GLabel} ) Dyn
  lol zero i = refl
  lol (Fin.suc zero) i = refl
  
  f-j-env-ok : (l : Fin 2) (i : l ∈ [l,l']) → ⊢ ⟨ Single (VCast{e = LabI l}{G = Single (VLab{x = l}) (Label ⁅ l ⁆)}{v = VLab}{g = GSingle}) Dyn , [] ⟩ ok
  f-j-env-ok l i = entry empty (SingleF empty (CastA (LabAI empty) (AConsDynR empty) {!refl!}) notsingle-dyn)
  -- !!! result of cast function is Singleton, S{(l : {l} => *) : *} never well-formed
  
  f-j : (l : Fin 2) (i : l ∈ [l,l']) → ⟨ Single (VCast{e = LabI l}{G = Label [l,l']}{v = VLab}{g = GLabel}) Dyn , [] ⟩ ⊢ f l i ▷ fᵀ l i
  f-j zero i = UnitAI {!!}
  f-j (Fin.suc zero) i = LabAI {!!}
  
  j : [] ⊢ e ▷ B'
  j = CastA (SigmaAI (SubTypeA (CastA (LabAI empty) (AConsDynR empty) refl) ASubDyn) (LabAExDyn{eq = refl} f-j)) (AConsSigma {!!}) {!!}

{-
module progress where
  open syntx
  open substitution
  open typing
  open semantics

  -- To eliminate the possible typing judgement (LabAEx) for case expressions,
  -- we need ([] ≢ Γ' ++ ⟨ D , Γ ⟩. Agda does not know that no possible constructor
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
  env-len->-++ {n} {Γ} {⟨ T , Γ' ⟩} gt rewrite (env-len-++ {n} {Γ} {⟨ T , Γ' ⟩})= ≤-trans gt (m≤n+m (length ⟨ T , Γ' ⟩) (length Γ))

  env-len-eq : {n : ℕ} {Γ : TEnv {n}} {Γ' : TEnv {n}} → Γ ≡ Γ' → length Γ ≡ length Γ'
  env-len-eq {n} {Γ} {.Γ} refl = refl
  
  env-empty-++ : {n : ℕ} {Γ' Γ : TEnv {n}} {D : Ty {n}} → ¬ ([] ≡ Γ' ++ ⟨ D , Γ ⟩)
  env-empty-++ {n} {Γ} {Γ'} {D} eq = contradiction (env-len-eq eq) (<⇒≢ (env-len->-++ (env-len->{T = D})))

  -- Canonical forms
  canonical-forms-pi : {n : ℕ} {e : Exp {n}} {A B D : Ty {n}} → [] ⊢ e ⇒ D → [] ⊢ D ⇓ Pi A B → Val e → (∃[ e' ](e ≡ Abs e'))
  canonical-forms-pi {n} {.(LabI _)} {A} {B} {.(Single VLab (Label ⁅ _ ⁆))} (LabAI x) (AUSingle ()) v
  canonical-forms-pi {n} {.(Abs _)} {A} {B} {.(Pi _ _)} (PiAI{M = M} j) u v = M , refl

  canonical-forms-sigma : {n : ℕ} {e : Exp {n}} {A B D : Ty {n}} → [] ⊢ e ⇒ D → [] ⊢ D ⇓ Sigma A B → Val e → (∃{A = Exp {n}} λ e' → ∃{A = Val e'} λ v → ∃ λ e'' → e ≡ ProdV{e = e'} v e'')
  canonical-forms-sigma {n} {.(LabI _)} {A} {B} {.(Single VLab (Label ⁅ _ ⁆))} (LabAI x) (AUSingle ()) v
  canonical-forms-sigma {n} {.(ProdV _ _)} {A} {B} {.(Sigma _ _)} (PairAI{e = e}{N}{V} j j₁) u v = e , (V , (N , refl))

  -- Main theorem
  data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ⇒ T} : Set where
    step : {e' : Exp{n}} → e ⇨ e' → Progress e
    value : Val e → Progress e

  progress : {n : ℕ} {e : Exp {n}} {T : Ty} → (j : [] ⊢ e ⇒ T) → Progress e {T} {j}
  progress {n} {Var x} {T} (VarA x₁ x₂) = value VVar
  progress {n} {UnitE} {.UnitT} (UnitAI x) = value VUnit
  progress {n} {Abs e} {.(Pi _ _)} (PiAI j) = value VFun
  progress {n} {App e x} {.([ 0 ↦ x ]ᵀ _)} (PiAE{A = A}{B = B}{D = D} j x₁ x₂ x₃)
    with progress {n} {e} {D} j
  ...  | step x₄ = step (ξ-App x₄)
  ...  | value x₄
       with canonical-forms-pi {n} {e} {A} {B} {D} j x₁ x₄
  ...     | fst , snd rewrite snd = step (β-App x)
  progress {n} {LabI x} {.(Single VLab (Label ⁅ x ⁆))} (LabAI x₁) = value VLab
  progress {n} {Prod e e₁} {.(Sigma A B)} (SigmaAI {A = A} {B = B} (SubTypeA{A = A₁} x x₂) x₁ j)
    with progress {n} {e} {A₁} x
  ...  | step x₃ = step (ξ-Prod x₃)
  ...  | value x₃ = step (β-Prod{v = x₃})
  progress {n} {ProdV x e} {.(Sigma _ _)} (PairAI{A = A} {B = B} j j₁)
    with progress {n} {e} {B} j₁
  ...  | step x₁ = step (ξ-ProdV x₁)
  ...  | value x₁ = value (VProd x x₁)
  progress {n} {LetP e e₁} {T} (SigmaAE{A = A}{B = B}{D = D} j x j₁ x₁)
    with progress {n} {e} {D} j
  ...  | step x₂ = step (ξ-LetP x₂)
  ...  | value x₂
       with canonical-forms-sigma {n} {e} {A} {B} {D} j x x₂
  ...     | fst , fst₁ , fst₂ , snd rewrite snd
          with x₂
  ...        | VProd v v₁ = step (β-LetP v v₁)
  progress {n} {LetE e e₁} {T} (Let{A = A} x j j₁)
    with progress {n} {e} {A} j
  ...  | step x₁ = step (ξ-LetE x₁)
  ...  | value x₁ = step (β-LetE x₁)
  progress {n} {CaseE {e = .(Var _)} VVar f} {T} (LabAEl {l = l} {ins = ins} (VarA x₁ ()) x j₁)
  progress {n} {CaseE {e = .(LabI _)} VLab f} {T} (LabAEl {l = _} {ins = ins} (LabAI x₁) x j₁) = step (β-LabE ins)
  progress {n} {CaseE .VVar f} {.(CaseT VVar _)} (LabAEx{eq = eq} x x₁) = contradiction eq env-empty-++

-}
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
  f₂ (Fin.suc zero) (there here) = Single (VLab{x = (Fin.suc (Fin.suc zero))}) (Label [l3])
  f₂ (Fin.suc (Fin.suc .(Fin.suc _))) (there (there (there ())))

  _ : ⟨ Label [l1,l2] , [] ⟩ ⊢ CaseE{s = [l1,l2]} (VVar{i = 0}) f₁ ⇒ CaseT{s = [l1,l2]} (VVar{i = 0}) f₂
  _ = LabAEx (ASubLabel (λ x → x)) g
    where g : (l : Fin 3) → (i : l ∈ [l1,l2])
              → ⟨ Single (VLab{x = l}) (Label [l1,l2]) , [] ⟩ ⊢ f₁ l i ⇒ f₂ l i
          g zero here = UnitAI (entry empty (SingleF empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (l∈L⇒[l]⊆L here)))) notsingle-label))
          g (Fin.suc zero) (there here) = LabAI (entry empty (SingleF empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (l∈L⇒[l]⊆L (there here))))) notsingle-label))
          g (Fin.suc (Fin.suc zero)) (there (there ()))

  ----------------------------------------------------------------------
  
  -- [] ⊢ ⟨ x : {l₁} = l₁ , case x of {l₁ : ()} ⟩ ⇒ Σ (x : {l₁}) (case x of {l₁ : Unit})
  [l1] : Subset 1
  [l1] = inside ∷ []

  premise : ⟨ Label [l1] , [] ⟩ ⊢ CaseE (VVar{i = 0}) (λ l x → UnitE) ⇒ CaseT (VVar{i = 0}) (λ l x → UnitT)
  premise = (LabAEx (ASubLabel (λ x → x)) (λ l i → (UnitAI (entry empty (SingleF empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (l∈L⇒[l]⊆L i)))) (notsingle (λ e B W ())))))))
     where ok' : (l : Fin 1) → l ∈ [l1] → [] ⊢ Single (VLab{x = l}) (Label [l1])
           ok' zero here = SingleF empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (λ x → x)))) (notsingle (λ e B W → λ ()))
         
  _ : [] ⊢ Prod (LabI zero) (CaseE{s = [l1]} (VVar{i = 0}) (λ l x → UnitE)) ⇒ Sigma (Label [l1]) (CaseT{s = [l1]} (VVar{i = 0}) (λ l x → UnitT))
  _ = SigmaAI
        (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (λ x → x)))) (ASubLabel (λ x → x)) premise
-}
