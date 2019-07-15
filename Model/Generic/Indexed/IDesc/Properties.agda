open import Model.Data using (here ; there ; _∈_)
open import Model.Base hiding (μ)
open import Model.Combinators
open import Model.Properties.General
open import Model.Properties.Completeness
open import Model.Properties.Monotonicity

open import Model.Generic.Regular.Properties 
open import Model.Generic.Indexed.IDesc.Generator
open import Model.Generic.Indexed.IDesc.Universe

open import Model.Enumerate hiding (⟨_⟩)

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Unit

open import Function
open import Level renaming (zero to zeroL; suc to sucL)

open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.HeterogeneousEquality

module Model.Generic.Indexed.IDesc.Properties where

  open GApplicative ⦃...⦄
  open GMonad ⦃...⦄

  postulate
    Σ-bind-Complete :
      ∀ {I : Set} {a : Set} {b : a → Set} {t : I → Set} {x y : I}
        {g : Gen a t x} {g' : (v : a) → Gen (b v) t y}
        {x : Σ a b} {tg : (i : I) → 𝔾 t i}
      → g ∣ᵢ tg ↝ proj₁ x
      → g' (proj₁ x) ∣ᵢ tg ↝ proj₂ x
      → _∣ᵢ_↝_ {i = y} (g >>= λ y → ⦇ (λ v → y , v) (g' y) ⦈) tg x

  postulate
    Σ-bind-Monotone :
      ∀ {I : Set} {a : Set} {b : a → Set} {t : I → Set} {x y : I}
        {g : Gen a t x} {g' : (v : a) → Gen (b v) t y}
        {x : Σ a b} {tg : (i : I) → 𝔾 t i}
      → Depth-Monotoneᵢ g tg (proj₁ x)
      → Depth-Monotoneᵢ (g' (proj₁ x)) tg (proj₂ x)
      → Depth-Monotoneᵢ {i = y} ((g >>= λ y → ⦇ (λ v → y , v) (g' y) ⦈)) tg x

  postulate
    Sl-gen-Monotone :
      ∀ {n : ℕ} {fn : Sl (lift n)} → Depth-Monotoneᵢ (Sl-gen (lift n)) Sl-gen fn

  -- The selector's generator is complete
  sl-gen-Complete : ∀ {n : ℕ} → Completeᵢ {a = Sl (lift n) } (Sl-gen (lift n)) Sl-gen
  sl-gen-Complete {zero} {()}
  sl-gen-Complete {suc n} {∙} = 1 , here
  sl-gen-Complete {suc n} {▻ x} with sl-gen-Complete {n} {x}
  sl-gen-Complete {suc n} {▻ x} | n' , elem =
    ∥ᵢ-complete-left {a = Sl} (constrᵢ-preserves-elem {a = Sl} {b = Sl} (suc n' , elem))

  callᵢ-Complete :
    ∀ {I J : Set} {a : J → Set} {t : I → Set}
      {g : (j : J) → Gen (a j) a j} {i : I}
      {tg : (i : I) → Gen (t i) t i} {j : J}
    → Completeᵢ (g j) g
    → Completeᵢ {a = a j} {i = i} (Call j g) tg
  callᵢ-Complete p {x} with p {x}
  callᵢ-Complete p {x} | suc n , elem = suc n , elem

  call-Complete :
    ∀ {a : Set} {I : Set} {t : I → Set} {g : Gen a (λ _ → a) tt}
      {tg : (i : I) → Gen (t i) t i} {i : I}
    → Completeᵢ g (λ _ → g)
    → Completeᵢ {a = a} {i = i} (Call tt (λ _ → g)) tg
  call-Complete p {x} with p {x}
  call-Complete p {x} | suc n , elem = suc n , elem

  `×-gen-Complete :
    ∀ {A B I x y} {T : I → Set} {i} {g₁ : Gen A T i} {g₂ : Gen B T i}
      {tg : (i : I) → Gen (T i) T i}
    → g₁ ∣ᵢ tg ↝ x
    → g₂ ∣ᵢ tg ↝ y
    → Depth-Monotoneᵢ g₁ tg x
    → Depth-Monotoneᵢ g₂ tg y
    → _∣ᵢ_↝_ {i = i} ⦇ g₁ , g₂ ⦈ tg (x , y)
  `×-gen-Complete pₗ pᵣ mt₁ mt₂ = ⊛-completeᵢ pₗ pᵣ mt₁ mt₂

  ⟨⟩-elem :
    ∀ {I : Set} {i : I} {φ : func 0ℓ I I} {x : ⟦ func.out φ i ⟧ (μ φ)} {xs : List (⟦ func.out φ i ⟧ (μ φ))}
    → (⟨_⟩ {φ = φ} x) ∈ Data.List.map (⟨_⟩) xs → x ∈ xs
  ⟨⟩-elem {xs = []} ()
  ⟨⟩-elem {xs = x ∷ xs} here = here
  ⟨⟩-elem {xs = x ∷ xs} (there elem) = there (⟨⟩-elem elem)

  call-Monotone : 
    ∀ {a : Set} {I : Set} {t : I → Set} {g : Gen a (λ _ → a) tt}
      {tg : (i : I) → Gen (t i) t i} {i : I} {x}
    → Depth-Monotoneᵢ g (λ _ → g) x
    → Depth-Monotoneᵢ {a = a} {i = i} (Call tt (λ _ → g)) tg x
  call-Monotone mt z≤n ()
  call-Monotone mt (s≤s leq) elem = mt (s≤s leq) elem

  callᵢ-Monotone :
    ∀ {I J : Set} {i : I} {j : J} {a : I → Set} {t : J → Set} {g : (i : I) → Gen (a i) a i}
      {tg : (j : J) → Gen (t j) t j} {i : I} {x}
    → Depth-Monotoneᵢ (g i) g x
    → Depth-Monotoneᵢ {i = j} (Call i g) tg x
  callᵢ-Monotone mt z≤n ()
  callᵢ-Monotone mt (s≤s leq) elem = mt (s≤s leq) elem

  `1-gen-Monotone :
    ∀ {I} {i : I} {φ : func 0ℓ I I} {x} {m : (i : I)  → IDescM (λ S → 𝔾 (λ _ → S) tt) (func.out φ i)}
    → Depth-Monotoneᵢ (IDesc-gen {φ = φ} i `1~) (λ i → IDesc-gen {δ = func.out φ i} {φ = φ} i (m i)) x
  `1-gen-Monotone z≤n ()
  `1-gen-Monotone (s≤s leq) elem = elem

  `×-gen-monotone :
    ∀ {I : Set} {i = i} {δ₁ δ₂ : IDesc 0ℓ I} {φ : func 0ℓ I I} {x  : ⟦ δ₁ ⟧ (μ φ)}
      {y : ⟦ δ₂ ⟧ (μ φ)} {tg : (i : I) → Gen (⟦ func.out φ i ⟧ (μ φ) ) (λ i → ⟦ func.out φ i ⟧ (μ φ)) i} {g₁} {g₂}
    → Depth-Monotoneᵢ {i = i} g₁ tg x → Depth-Monotoneᵢ {i = i} g₂ tg y
    → Depth-Monotoneᵢ {i = i} ⦇ g₁ , g₂ ⦈ tg (x , y)
  `×-gen-monotone {g₁ = g₁} {g₂} mt₁ mt₂ = 
    ⊛-monotoneᵢ {g₁ = g₁} {g₂ = g₂} ,-inv mt₁ mt₂

  IDesc-gen-Monotone :
    ∀ {I : Set} {ix : I} {δ : IDesc 0ℓ I} {φ : func 0ℓ I I}
      {x : ⟦ δ ⟧ (μ φ)}
    → (m₁ : IDescM ((λ S →
             Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
      (Completeᵢ gen (λ _ → gen) ×
        (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s)))) δ)
    → (m₂ : (i : I) → IDescM ((λ S →
             Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
      (Completeᵢ gen (λ _ → gen) ×
        (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s)))) (func.out φ i))
    → Depth-Monotoneᵢ (IDesc-gen ix (mapm proj₁ m₁)) (λ i → IDesc-gen i (mapm proj₁ (m₂ i))) x
  IDesc-gen-Monotone {δ = `var i} {φ} {⟨ x ⟩} (`var~) m₂ (s≤s leq) elem
    with IDesc-gen-Monotone {ix = i} {δ = func.out φ i} {x = x} (m₂ i) m₂
  ... | prf = ++-elem-left (map-preserves-elem (prf leq (⟨⟩-elem {φ = φ} (map-++-ident {f = ⟨_⟩} elem))))
  IDesc-gen-Monotone {ix = ix} {δ = `1} {φ} {x} `1~ m₂ (s≤s leq) elem =
    `1-gen-Monotone {i = ix} {φ = φ} {m = λ i → mapm proj₁ (m₂ i)} (s≤s leq) elem
  IDesc-gen-Monotone {δ = δₗ `× δᵣ} {φ} {x} (mₗ `×~ mᵣ) m₂ (s≤s leq) elem =
    `×-gen-monotone {δ₁ = δₗ} {δ₂ = δᵣ} (IDesc-gen-Monotone {δ = δₗ} mₗ m₂)
                                        (IDesc-gen-Monotone {δ = δᵣ} mᵣ m₂) (s≤s leq) elem
  IDesc-gen-Monotone {ix = ix} {δ = `σ n T} {φ} {sl , x} (`σ~ mT) m₂ (s≤s leq) elem =
    Σ-bind-Monotone {x = ix} {g = Call (lift n) Sl-gen} {g' = λ sl → IDesc-gen ix (mapm proj₁ (mT sl))}
      (callᵢ-Monotone {i = lift n} Sl-gen-Monotone) (IDesc-gen-Monotone (mT sl) m₂ ) (s≤s leq) elem
  IDesc-gen-Monotone {ix = ix} {δ = `Σ S T} {φ} {s , x} (`Σ~ (gen , (cmp , mt)) mT) m₂ (s≤s leq) elem =
    Σ-bind-Monotone {x = ix} {y = ix} {g' = λ s → IDesc-gen {δ = T s} ix (mapm proj₁ (mT s))}
      (call-Monotone mt) (IDesc-gen-Monotone {δ = T s} {φ = φ} (mT s) m₂) (s≤s leq) elem

  IDesc-gen-Complete :
    ∀ {I : Set} {ix : I} {δ : IDesc 0ℓ I} {φ : func 0ℓ I I}
      {x : ⟦ δ ⟧ (μ φ)}
    → (m₁ : IDescM (λ S →
      Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
         (Completeᵢ gen (λ _ → gen) ×
           (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s))) δ) 
    → (m₂ : (i : I) →
      IDescM (λ S →
             Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
      (Completeᵢ gen (λ _ → gen) ×
        (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s)))
        (func.out φ i))
    → Σ ℕ (λ n → x ∈ enumerate (λ y → IDesc-gen y (mapm proj₁ (m₂ y))) ix (IDesc-gen ix (mapm proj₁ m₁)) n)
  IDesc-gen-Complete {δ = `var i} {φ} {⟨ x ⟩} m₁ m₂
    with IDesc-gen-Complete {ix = i} {δ = func.out φ i} {φ = φ} {x = x} (m₂ i) m₂
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} m₁ m₂ | zero , ()
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} `var~ m₂ | suc fst , snd =
    constrᵢ-preserves-elem {a = λ y → ⟦ func.out φ y ⟧ (μ φ)} ((suc (suc fst)) , snd) 
  IDesc-gen-Complete {δ = `1} {φ} {lift tt} `1~ m₂ = 1 , here
  IDesc-gen-Complete {ix = ix} {δ = δₗ `× δᵣ} {φ} {fst , snd} (mₗ `×~ mᵣ) m₂ =
    `×-gen-Complete (IDesc-gen-Complete {x = fst} mₗ m₂) (IDesc-gen-Complete {x = snd} mᵣ m₂)
                    (IDesc-gen-Monotone mₗ m₂) (IDesc-gen-Monotone mᵣ m₂)
  IDesc-gen-Complete {δ = `σ n T} {φ} {sl , x} (`σ~ mT) m₂ =
    Σ-bind-Complete (callᵢ-Complete sl-gen-Complete) (IDesc-gen-Complete {δ = T sl} (mT sl) m₂)
  IDesc-gen-Complete {δ = `Σ S T} {φ} {s , x} (`Σ~ (g , (cmp , mt)) x₂) m₂ =
    Σ-bind-Complete (call-Complete cmp) (IDesc-gen-Complete (x₂ s) m₂)


