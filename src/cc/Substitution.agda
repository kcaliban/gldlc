------------------------------------------------------------------------
-- Shifting and Substitution
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
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

↑ d , c [ UnitE ] = UnitE
↑ d , c [ Blame ] = Blame
↑ d , c [ Cast e A B ] = Cast ↑ d , c [ e ] ↑ᵀ d , c [ A ] ↑ᵀ d , c [ B ] 
↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
↑ d , c [ App t v ] = App (↑ d , c [ t ]) (↑ d , c [ v ])
↑ d , c [ LabI x ] = LabI x
↑ d , c [ CaseE e f ] = CaseE ↑ d , c [ e ] (λ l x → ↑ d , c [ f l x ])
↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
↑ d , c [ ProdV e e' ] = ProdV ↑ d , c [ e ] ↑ d , c [ e' ]
↑ d , c [ LetP e e' ] = LetP (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])
↑ d , c [ LetE e e' ] = LetE (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

↑ᵀ d , c [ UnitT ] = UnitT
↑ᵀ d , c [ Bot ] = Bot
↑ᵀ d , c [ Top ] = Top
↑ᵀ d , c [ Dyn ] = Dyn
↑ᵀ d , c [ Single x A ] = Single ↑ d , c [ x ] ↑ᵀ d , c [ A ]
↑ᵀ d , c [ Label x ] = Label x
↑ᵀ d , c [ Pi A A₁ ] = Pi ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
↑ᵀ d , c [ Sigma A A₁ ] = Sigma ↑ᵀ d , c [ A ] ↑ᵀ d , (ℕ.suc c) [ A₁ ]
↑ᵀ d , c [ CaseT x f ] = CaseT ↑ d , c [ x ] (λ l y → ↑ᵀ d , c [ f l y ])

-- shorthands
↑¹[_] : ∀ {n} → Exp {n} → Exp
↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

------------------------------------------------------------------------
-- Substitution

[_↦_]_ : ∀ {n} → ℕ → Exp {n} → Exp {n} → Exp {n}
[_↦_]ᵀ_ : ∀ {n} → ℕ → Exp {n} → Ty {n} → Ty {n}

[_↦_]_ {n} k e (Var x)
  with (_≟ᴺ_ x k)
...  | yes p = e
...  | no ¬p = Var x
[_↦_]_ {n} k e UnitE = UnitE
[_↦_]_ {n} k e (Abs e') = Abs ([ ℕ.suc k ↦ ↑ ℤ.pos 1 , 0 [ e ] ] e')
[_↦_]_ {n} k e (App e' e'') = App ([ k ↦ e ] e') ([ k ↦ e ] e'')
[_↦_]_ {n} k e (LabI x) = LabI x
[_↦_]_ {n} k e (CaseE e' f) = CaseE ([ k ↦ e ] e') (λ l x₁ → [ k ↦ e ] (f l x₁))
[_↦_]_ {n} k e (Prod e' e'') = Prod ([ k ↦ e ] e') ([ ℕ.suc k ↦ ↑ ℤ.pos 1 , 0 [ e ] ] e'')
[_↦_]_ {n} k e (ProdV e' e'') = ProdV ([ k ↦ e ] e') ([ k ↦ e ] e'')
[_↦_]_ {n} k e (LetP e' e'') = LetP ([ k ↦ e ] e') ([ ℕ.suc (ℕ.suc k) ↦ ↑ ℤ.pos 2 , 0 [ e ] ] e'')
[_↦_]_ {n} k e (LetE e' e'') = LetE ([ k ↦ e ] e') ([ (ℕ.suc k) ↦ ↑ ℤ.pos 1 , 0 [ e ] ] e'')
[_↦_]_ {n} k e Blame = Blame
[_↦_]_ {n} k e (Cast e' x x₁) = Cast ([ k ↦ e ] e') ([ k ↦ e ]ᵀ x) ([ k ↦ e ]ᵀ x₁)

[_↦_]ᵀ_ {n} k e UnitT = UnitT
[_↦_]ᵀ_ {n} k e (Single x T) = Single ([ k ↦ e ] x) ([ k ↦ e ]ᵀ T)
[_↦_]ᵀ_ {n} k e (Label x) = Label x
[_↦_]ᵀ_ {n} k e (Pi T T₁) = Pi ([ k ↦ e ]ᵀ T) ([ ℕ.suc k ↦ ↑ ℤ.pos 1 , 0 [ e ] ]ᵀ T₁)
[_↦_]ᵀ_ {n} k e (Sigma T T₁) = Sigma ([ k ↦ e ]ᵀ T) ([ ℕ.suc k ↦ ↑ ℤ.pos 1 , 0 [ e ] ]ᵀ T₁)
[_↦_]ᵀ_ {n} k e (CaseT x f) = CaseT ([ k ↦ e ] x) (λ l ins → [ k ↦ e ]ᵀ (f l ins))
[_↦_]ᵀ_ {n} k e Bot = Bot
[_↦_]ᵀ_ {n} k e Top = Top
[_↦_]ᵀ_ {n} k e Dyn = Dyn


