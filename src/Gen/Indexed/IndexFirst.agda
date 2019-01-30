open import Data.Vec
open import Data.Nat

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin
open import Data.List

open import Function

open import Relation.Binary.PropositionalEquality

module src.Gen.Indexed.IndexFirst where

  Vec' : (a : Set) → ℕ → Set
  Vec' a zero = ⊤
  Vec' a (suc n) = a × Vec' a n

  data Term : ℕ → Set where
    Var : ∀ {n : ℕ} → Fin n → Term n
    Abs : ∀ {n : ℕ} → Term n → Term (suc n)
    App : ∀ {n : ℕ} → Term n → Term n → Term n

  VecF : Set → (ℕ → Set) → ℕ → Set
  VecF a f zero = ⊤
  VecF a f (suc n) = a × f n

  VecF' : Set → ℕ → (ℕ → Set) → Set
  VecF' a zero = λ f → ⊤
  VecF' a (suc n) = λ f → a × f n

  data RDesc (i : Set) : Set₁ where
    ν : (is : List i) → RDesc i
    σ : (s : Set) → (D : s → RDesc i) → RDesc i

  ℙ : ∀ {i : Set} → List i → (i → Set) → Set
  ℙ [] f = ⊤
  ℙ (x ∷ xs) f = f x × ℙ xs f

  ⟦_⟧ : ∀ {i : Set} → RDesc i → (i → Set) → Set
  ⟦ ν is ⟧ f = ℙ is f
  ⟦ σ S D ⟧ f = Σ[ s ∈ S ] ⟦ D s ⟧ f

  syntax σ S (λ s → D) = σ[ s ∈ S ] D

  Desc : Set → Set₁
  Desc i = i → RDesc i

  𝔽 : ∀ {i : Set} → Desc i → (i → Set) → (i → Set)
  𝔽 D f i = ⟦ D i ⟧ f

  _⇉_ : ∀ {i : Set} → (i → Set) → (i → Set) → Set
  (_⇉_) {i} x y = {v : i} → x v → y v 

  {-# NO_POSITIVITY_CHECK #-}
  data μ {i : Set} (D : Desc i) : i → Set where
    In : 𝔽 D (μ D) ⇉ μ D

  data ListTag : Set where
    nil  : ListTag
    cons : ListTag

  NatD : Desc ⊤
  NatD tt = σ ListTag λ { nil → ν [] ; cons → ν (tt ∷ []) }

  ListD : Set → Desc ⊤
  ListD a tt = σ ListTag λ { nil → ν [] ; cons → σ a λ _ → ν (tt ∷ []) }

  VecD : Set → Desc ℕ
  VecD a zero = ν []
  VecD a (suc n) = σ a λ _ → ν (n ∷ [])

  data ConMenu : Set where
    always  : ConMenu
    indexed : ConMenu

  FinD : Desc ℕ
  FinD = λ n → σ ConMenu λ { always → ν []
                           ; indexed → case n of λ { zero      → σ ⊥ λ ()
                                                   ; (suc m) → ν (m ∷ [])
                                                   }
                           }
  
  data Inv {a b : Set} (f : a → b) : b → Set where
    ok : (x : a) → Inv f (f x)

  und : ∀ {a b : Set} {f : a → b} {y : b} → Inv f y → a
  und (ok x) = x

  data 𝔼 {i j : Set} (e : j → i) : List j → List i → Set where
    []  : 𝔼 e [] []
    _∷_ : ∀ {y : j} {x : i} {js : List j} {is : List i} → (eq : e y ≡ x) → (eqs : 𝔼 e js is) → 𝔼 e (y ∷ js) (x ∷ is)

  data ROrn {i j : Set} (e : j → i) : RDesc i → RDesc j → Set₁ where
    ν : ∀ {js : List j} {is : List i} → (eqs : 𝔼 e js is) → ROrn e (ν is) (ν js)
    σ : (s : Set) → {D : s → RDesc i} {E : s → RDesc j} → ((s' : s) → ROrn e (D s') (E s')) → ROrn e (σ s D) (σ s E)
    Δ : (t : Set) → {D : RDesc i} {E : t → RDesc j} → ((t' : t) → ROrn e D (E t')) → ROrn e D (σ t E)
    ∇ : ∀ {s : Set} → (s' : s) → {D : s → RDesc i} {E : RDesc j} → ROrn e (D s') E → ROrn e (σ s D) E
    

  Orn : ∀ {i j : Set} → (e : j → i) (D : Desc i) (E : Desc j) → Set₁
  Orn {i} e D E = {x : i} → (j : Inv e x) → ROrn e (D x) (E (und j))

  NatD→ListD : (a : Set) → Orn (λ _ → tt) NatD (ListD a)
  NatD→ListD a (ok tt) = σ ListTag λ { nil → ν [] ; cons → Δ a λ { _ → ν (refl ∷ []) } }
  
  ListD→VecD : (a : Set) → Orn (λ _ → tt) (ListD a) (VecD a)
  ListD→VecD a (ok zero)    = ∇ nil (ν [])
  ListD→VecD a (ok (suc x)) = ∇ cons (σ a (const (ν (refl ∷ []))))

  
