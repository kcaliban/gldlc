------------------------------------------------------------------------
-- Shifting and Substitution
------------------------------------------------------------------------

module Substitution where

open import Data.Nat renaming (_≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Fin hiding (cast)
open import Relation.Nullary

open import Syntax
open import Aux

------------------------------------------------------------------------
-- Shifting

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

↑ d , c [ UnitE ] = UnitE
↑ d , c [ Blame ] = Blame
↑ d , c [ Cast e A B ] = Cast ↑ d , c [ e ] ↑ᵀ d , c [ A ] ↑ᵀ d , c [ B ] 
↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
↑ d , c [ App t v ] = App (↑ d , c [ t ]) (↑ d , c [ v ])
↑ d , c [ LabI x ] = LabI x
↑ d , c [ CaseE{e = e} U f ] = CaseE (shift-valu{d = d}{c = c} U) (λ l x → ↑ d , c [ f l x ])
↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
↑ d , c [ ProdV e e' ] = ProdV (shift-val{d = d}{c = c} e) (↑ d , c [ e' ])
↑ d , c [ LetP e e' ] = LetP (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])
↑ d , c [ LetE e e' ] = LetE (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

↑ᵀ d , c [ UnitT ] = UnitT
↑ᵀ d , c [ Bot ] = Bot
↑ᵀ d , c [ Dyn ] = Dyn
↑ᵀ d , c [ Single x ] = Single (shift-val{d = d}{c = c} x)
↑ᵀ d , c [ Label x ] = Label x
↑ᵀ d , c [ Pi A A₁ ] = Pi ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
↑ᵀ d , c [ Sigma A A₁ ] = Sigma ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
↑ᵀ d , c [ CaseT x f ] = CaseT (shift-valu{d = d}{c = c} x) (λ l x₁ → ↑ᵀ d , c [ f l x₁ ])

shift-val {n} {d} {c} {.UnitE} VUnit = VUnit
shift-val {n} {d} {c} {(Cast e A B)} (VCast v g) = VCast (shift-val v) (shift-tyg g)
shift-val {n} {d} {c} {(Cast e A B)} (VCastFun v) = VCastFun (shift-val v)
shift-val {n} {d} {c} {.(LabI _)} VLab = VLab
shift-val {n} {d} {c} {.(Abs _)} VFun = VFun
shift-val {n} {d} {c} {.(ProdV V _)} (VProd V V₁) = VProd (shift-val V) (shift-val V₁)

shift-valu {n} {d} {c} {.(Var _)} UVar = UVar
shift-valu {n} {d} {c} {.UnitE} UValUnit = UValUnit
shift-valu {n} {d} {c} {.(LabI _)} UValLab = UValLab
shift-valu {n} {d} {c} {.(Abs _)} UValFun = UValFun
shift-valu {n} {d} {c} {.(ProdV v _)} (UValProd v x) = UValProd (shift-val v) (shift-val x)
shift-valu {n} {d} {c} {.(Cast (Var _) _ _)} UVarCast = UVarCast
shift-valu {n} {d} {c} {.(Cast _ _ _)} (UValCast x) = UValCast (shift-val x)
shift-valu {n} {d} {c} {.Blame} UBlame = UBlame

shift-tyg {n} {d} {c} {.UnitT} GUnit = GUnit
shift-tyg {n} {d} {c} {.(Label _)} GLabel = GLabel
shift-tyg {n} {d} {c} {.(Pi Dyn Dyn)} GPi = GPi
shift-tyg {n} {d} {c} {.(Sigma Dyn Dyn)} GSigma = GSigma
shift-tyg {n} {d} {c} {Single V} GSingle = GSingle

-- shorthands
↑¹[_] : ∀ {n} → Exp {n} → Exp
↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

↑ⱽ¹[_] : ∀ {n} {e : Exp {n}} → Val e → Val (↑ (ℤ.pos 1) , 0 [ e ])
↑ⱽ¹[_] {n} {e} v = shift-val v

↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

------------------------------------------------------------------------
-- Substitution

[_↦_]_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Exp {n} → Exp {n}
[_↦_]ᵀ_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Ty {n} → Ty {n}

sub-val : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → Val e → Val ([ k ↦ v ] e)
sub-valu : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → ValU e → ValU ([ k ↦ v ] e)
sub-tyg : ∀ {n k} {A : Ty {n}} {e : Exp {n}} {v : Val e} → TyG A → TyG ([ k ↦ v ]ᵀ A)

[_↦_]_ {n} {e} k v (Var x)
  with (_≟ᴺ_ x k)
...  | yes p = e
...  | no ¬p = Var x
[ k ↦ v ] UnitE = UnitE
[ k ↦ v ] Blame = Blame
[ k ↦ v ] Cast e A B = Cast ([ k ↦ v ] e) ([ k ↦ v ]ᵀ A) ([ k ↦ v ]ᵀ B)
[ k ↦ v ] Abs e = Abs (([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e))
[_↦_]_ {n} {e'} k v (App e e₁) = App ([ k ↦ v ] e) ([ k ↦ v ] e₁)
[ k ↦ v ] LabI x = LabI x
[_↦_]_ {n} {e} k v (CaseE v' f) = CaseE (sub-valu{n}{k}{e' = e}{v = v} v') (λ l x₁ → [ k ↦ v ] (f l x₁))
[ k ↦ v ] Prod e e₁ = Prod ([ k ↦ v ] e) ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)
[_↦_]_ {n} {e} k v (ProdV v' e') = ProdV (sub-val{n}{k}{e' = e}{v = v} v') ([ k ↦ v ] e')
[ k ↦ v ] LetP e e₁ = LetP ([ k ↦ v ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ shift-val{d = ℤ.pos 2}{c = 0} v ] e₁)
[ k ↦ v ] LetE e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc k) ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)

[ k ↦ s ]ᵀ UnitT = UnitT
[ k ↦ s ]ᵀ Dyn = Dyn
[ k ↦ s ]ᵀ Bot = Bot
[_↦_]ᵀ_ {n} {e} k v (Single x) = Single (sub-val{n}{k}{e' = e}{v = v} x)
[ k ↦ s ]ᵀ Label x = Label x
[ k ↦ s ]ᵀ Pi T T₁ = Pi ([ k ↦ s ]ᵀ T) ([ ℕ.suc k ↦ (shift-val{d = ℤ.pos 1}{c = 0} s) ]ᵀ T₁)
[ k ↦ s ]ᵀ Sigma T T₁ = Sigma ([ k ↦ s ]ᵀ T) ([ ℕ.suc k ↦ (shift-val{d = ℤ.pos 1}{c = 0} s) ]ᵀ T₁)
[_↦_]ᵀ_ {n} {e} k v (CaseT x f) = CaseT (sub-valu{n}{k}{e' = e}{v = v} x) λ l x₁ → [ k ↦ v ]ᵀ (f l x₁)

sub-val {n} {k} {.UnitE} {e'} {v} VUnit = VUnit
sub-val {n} {k} {Cast e A B} {e'} {v} (VCast v' g) = VCast (sub-val v') (sub-tyg g)
sub-val {n} {k} {Cast e A B} {e'} {v} (VCastFun v') = VCastFun (sub-val v')
sub-val {n} {k} {.(LabI _)} {e'} {v} VLab = VLab
sub-val {n} {k} {.(Abs _)} {e'} {v} VFun = VFun
sub-val {n} {k} {.(ProdV v' _)} {e'} {v} (VProd v' v'') = VProd (sub-val v') (sub-val v'')

sub-valu {n} {k} {(Var x)} {e'} {v} UVar
  with (_≟ᴺ_ x k)
...  | yes p = val⊂valu v
...  | no ¬p = UVar
sub-valu {n} {k} {.UnitE} {e'} {v} UValUnit = UValUnit
sub-valu {n} {k} {.(LabI _)} {e'} {v} UValLab = UValLab
sub-valu {n} {k} {.(Abs _)} {e'} {v} UValFun = UValFun
sub-valu {n} {k} {.(ProdV v₁ _)} {e'} {v} (UValProd v₁ x) = UValProd (sub-val v₁) (sub-val x)
sub-valu {n} {k} {(Cast (Var x) _ _)} {e'} {v} UVarCast
  with (_≟ᴺ_ x k)
...  | yes p = UValCast v
...  | no ¬p = UVarCast
sub-valu {n} {k} {.(Cast _ _ _)} {e'} {v} (UValCast x) = UValCast (sub-val x)
sub-valu {n} {k} {.Blame} {e'} {v} UBlame = UBlame

sub-tyg {n} {k} {.UnitT} {e} {v} GUnit = GUnit
sub-tyg {n} {k} {.(Label _)} {e} {v} GLabel = GLabel
sub-tyg {n} {k} {.(Pi Dyn Dyn)} {e} {v} GPi = GPi
sub-tyg {n} {k} {.(Sigma Dyn Dyn)} {e} {v} GSigma = GSigma
sub-tyg {n} {k} {Single V} {e} {V'} GSingle = GSingle

