open import Agda.Builtin.Size

open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.List hiding (concat; [_]; map)
open import Category.Applicative

open import Codata.Colist
open import Codata.Thunk hiding (map)

open import src.Enumerable
open import src.Data 
open import src.Nonempty 
open import src.Product
open import src.Indexed

module src.Lambda where 

  data Foo : Set where
    bar : Foo
    baz : Foo → Foo → Foo

  -- We need this ...
  cp : ∀ {a b : Set} {i : Size} → Colist a i → Colist b i → Colist (a ⊗ b) i

  enumFoo : ∀ {i : Size} → Colist Foo i
  enumFoo = bar ∷ λ where .force → map (λ t → baz (fst t) (snd t)) (cp enumFoo enumFoo)

  prop : prefix 10 enumFoo ≡ {!!}
  prop = refl

{-
  merge' : ∀ {a : Set} {i : Size} → Colist a ∞ → Thunk (Colist a) ∞ → Colist a i
  merge' [] ys = ys .force
  merge' (x ∷ xs) ys = x ∷ (λ where .force → merge' (ys .force) xs)

  concat₊ : ∀ {a : Set} → List₊ a → List₊ a → List₊ a
  concat₊ [ x ] ys = x ∷ ys
  concat₊ (x ∷ xs) ys = x ∷ concat₊ xs ys

  concatMap₊ : ∀ {a b : Set} → (a → List₊ b) → List₊ a → List₊ b
  concatMap₊ f [ x ] = f x
  concatMap₊ f (x ∷ xs) = concat₊ (f x) (concatMap₊ f xs)

  apl : ∀ {a b : Set} → List₊ (a → b) → List₊ a → List₊ b
  apl = λ fs as → concatMap₊ (λ f → mapl₊ f as) fs

  prepend : ∀ {a : Set} {i : Size} → List₊ a → Thunk (Colist₊ a) i → Colist₊ a i
  prepend [ x ] ys = x ∷ ys
  prepend (x ∷ xs) ys = x ∷ λ where .force → prepend xs ys

  combine : ∀ {a : Set} → (a → a → a) → List₊ a → List₊ a → List₊ a
  combine f xs ys = apl (mapl₊ f xs) ys

  iterate2 : ∀ {a : Set} {i : Size} → (a → a → a) → (a → a) → List₊ a → Colist₊ a i
  iterate2 f g xs =
    let res₀  = combine f xs  xs in
    let res₁  = combine f res₀ xs in
    let res₂  = combine f xs res₀ in
    let res   = concat₊ res₀ (concat₊ res₁ res₂) in
    let res'  = merge₊ res (mapl₊ g res) in
    prepend (concat₊ (mapl₊ g xs) res')
      (λ where .force → iterate2 f g (concat₊ xs res'))

  enumFoo : ∀ {i : Size} → Colist Foo' i
  enumFoo = bar ∷ λ where .force → toColist (baz bar ∷ λ where .force → iterate2 qux baz [ bar ])
  
  -- Untyped, ill-scoped lambda terms
  module Lambda1 where 

    data L₁ : Set where
      Var : ℕ → L₁
      Abs : L₁ → L₁
      App : L₁ → L₁ → L₁

    mutual
      {-# TERMINATING #-}
      enumL₁' : ∀ {i : Size} → ℕ → Colist₊ L₁ i
      enumL₁' (zero) = enumVar
      enumL₁' (suc n) = interleaveN₊ (enumAbs (suc n) ∷ [ enumApp (suc n) ])

      enumVar : Colist₊ L₁ ∞
      enumVar = map₊ Var (iterate₊ zero suc)

      enumAbs : ∀ {j : Size} → ℕ → Colist₊ L₁ j
      enumAbs zero = enumL₁' 0
      enumAbs (suc n) = map₊ Abs (enumL₁' n)

      enumApp : ∀ {j : Size} → ℕ → Colist₊ L₁ ∞
      enumApp zero = enumL₁' 0 -- []
      enumApp (suc n) = interleaveN₊ (mapl₊ (λ p → toColist₊ (Abs (Var 0)) (Codata.Colist.map (λ ts → App (fst ts) (snd ts)) (toColist (enumL₁' (fst p)) × toColist (enumL₁' (snd p))))) (splits (suc 0) n))
        where splits : ℕ → ℕ → List₊ (ℕ ⊗ ℕ)
              splits n zero = [ n , zero ]
              splits n (suc m) = n , suc m ∷ splits (suc n) m
    
    instance
      enumL₁ : Enumerable L₁
      enumL₁ = record { enum = diagonal (map enumL₁' (inhabitants ℕ)) }


  -- Untyped, well-scoped lambda terms
  module Lambda2 where

    data L₂ : ℕ → Set where
      Var : ∀ {n : ℕ} → Fin n → L₂ n
      Abs : ∀ {n : ℕ} → L₂ (suc n) → L₂ n
      App : ∀ {n : ℕ} → L₂ n → L₂ n → L₂ n

    mutual
      {-# TERMINATING #-}
      enumL₂ : ∀ {i : Size} → (n : ℕ) → Colist (L₂ n) i
      enumL₂ n = interleave (enumVar n) (interleave (enumApp n) (λ where .force → enumAbs n)) .force

      enumVar : ∀ {i : Size} → (n : ℕ) → Colist (L₂ n) i
      enumVar n = map Var (inhabitants' Fin n)

      enumAbs : ∀ {i : Size} → (n : ℕ) → Colist (L₂ n) i
      enumAbs n = map Abs (enumL₂ (suc n))

      enumApp : ∀ {i : Size} → (n : ℕ) → Colist (L₂ n) i
      enumApp n = {!!}

      prop : prefix 10 (enumL₂ 0) ≡ {!!}
      prop = {!!}

  open Lambda1 public
-}
