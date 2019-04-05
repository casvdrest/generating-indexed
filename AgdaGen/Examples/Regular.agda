open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Data
  using (here; there; _∈_; merge)
  
open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Regular.Universe
open import AgdaGen.Generic.Regular.Properties
open import AgdaGen.Generic.Regular.Generator
open import AgdaGen.Generic.Regular.Instances

open import AgdaGen.Properties.Completeness
open import AgdaGen.Properties.General
open import AgdaGen.Properties.Equivalence
open import AgdaGen.Properties.Monotonicity

open import Data.Bool
open import Data.Maybe
  using (just; nothing; Maybe)
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Empty

open import Relation.Binary.PropositionalEquality

open import Level hiding (suc; zero)

module AgdaGen.Examples.Regular where
  
  ------ Bool -----

  bool : 𝔾 Bool
  bool = ⦇ true  ⦈
       ∥ ⦇ false ⦈

  bool-Complete : Complete bool bool
  bool-Complete {false} = 1 , there here
  bool-Complete {true} = 1 , here
  
  bool' : 𝔾 Bool
  bool' = isoGen Bool (U~ ⊕~ U~)

  bool∼bool' : bool ∼ bool'
  bool∼bool' =
    Complete→eq {g₁ = bool} {g₂ = bool'}
      bool-Complete (isoGen-Complete (U~ ⊕~ U~))


  ------ Maybe ------

  maybe : ∀ {a : Set} → 𝔾 a → 𝔾 (Maybe a)
  maybe a = ⦇ nothing    ⦈
          ∥ ⦇ just (` a) ⦈
  
  maybe' : ∀ {a : Set} → 𝔾 a → 𝔾 (Maybe a)
  maybe' {a = a} gen =
    isoGen (Maybe a) (K~ gen ⊕~ U~)

  maybe-Complete :
    ∀ {a : Set}
    → (sig :
        Σ[ gen ∈ 𝔾 a ] (
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen))
      ) → Complete (maybe (proj₁ sig)) (maybe (proj₁ sig))
  maybe-Complete (gen , fst , snd) {just x} =
    ∥-complete-right (constr-preserves-elem (`-complete fst))
  maybe-Complete (gen , prf) {nothing} =
    ∥-complete-left pure-complete

  
  maybe∼maybe' :
    ∀ {a : Set}
    → (sig :
        Σ[ gen ∈ 𝔾 a ] (
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen))
        ) → maybe (proj₁ sig) ∼ maybe' (proj₁ sig)
  maybe∼maybe' {a} sig =
    Complete→eq {g₁ = maybe (proj₁ sig)} {g₂ = maybe' (proj₁ sig)}
      (maybe-Complete sig) (isoGen-Complete (K~ sig ⊕~ U~))

  
  ------ Naturals ------

  nat : 𝔾 ℕ
  nat = ⦇ zero  ⦈
      ∥ ⦇ suc μ ⦈

  nat' : 𝔾 ℕ
  nat' = isoGen ℕ (U~ ⊕~ I~)

  nat-Complete : Complete nat nat
  nat-Complete {zero} = 1 , here
  nat-Complete {suc n} with nat-Complete {n}
  nat-Complete {suc n} | m , elem =
    suc m , merge-cong {xs = []}
     (++-elem-left (map-preserves-elem elem))
  
  nat∼nat' : nat ∼ nat'
  nat∼nat' = Complete→eq {g₁ = nat} {g₂ = nat'}
    nat-Complete (isoGen-Complete (U~ ⊕~ I~))
  
  ------ Lists ------

  list : ∀ {a : Set} → 𝔾 a → 𝔾 (List a)
  list a = ⦇ [] ⦈
         ∥ ⦇ ` a ∷ μ ⦈

  list' : ∀ (a : Set) → 𝔾 a → 𝔾 (List a)
  list' a gen = isoGen (List a) (U~ ⊕~ (K~ gen ⊗~ I~))

  ∷-bijective :
    ∀ {a : Set} {x₁ x₂ : a} {xs₁ xs₂ : List a}
    → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂ → x₁ ≡ x₂ × xs₁ ≡ xs₂
  ∷-bijective refl = refl , refl

  interpret-pure :
    ∀ {a t : Set} {tg : 𝔾 t} {x : a} {n : ℕ}
    → interpret (⦇ x ⦈) tg (suc n) ≡ x ∷ []
  interpret-pure = refl

  interpret-ap :
    ∀ {a : Set} {tg : 𝔾 (List a)} {gen : 𝔾 a} {xs : List a} {n : ℕ}
    → xs ∈ interpret (⦇ (` gen) ∷ μ ⦈) tg (suc n)
    → Σ[ t ∈ a × List a ] xs ≡ proj₁ t ∷ proj₂ t
  interpret-ap {tg = tg} {gen} {xs} {n} elem
    with ap-inv
      {fs = interpret (⦇ _∷_ (` gen) ⦈) tg (suc n)}
      {xs = interpret μ tg (suc n)} elem
  interpret-ap {tg = tg} {gen} {xs} {n} elem
   | (f , x) , (elemf , elemx) , refl with ap-singleton elemf
  interpret-ap {tg = tg} {gen} {.(f x)} {n} elem
   | (f , x) , (elemf , elemx) , refl | fst , (_ , refl) =
     (fst , x) , refl
  
  []-elem-⊥ :
    ∀ {n : ℕ} {a : Set} {tg : 𝔾 (List a)} {gen : 𝔾 a}
    → [] ∈ interpret (⦇ (` gen) ∷ μ ⦈) tg n → ⊥
  []-elem-⊥ {zero} ()
  []-elem-⊥ {suc n} {tg = tg} {gen = gen} elem with
    interpret-ap {tg = tg} {gen = gen} {n = n} elem
  ... | t , () 

  ∷-elem-⊥ :
    ∀ {n : ℕ} {a : Set} {x : a} {xs : List a} {tg : 𝔾 (List a)}
    → (x ∷ xs) ∈ interpret (⦇ [] ⦈) tg n → ⊥
  ∷-elem-⊥ {zero} ()
  ∷-elem-⊥ {suc n} {a} {tg = tg} elem
    with interpret-pure {List a} {tg = tg} {x = []} {n = n}
  ∷-elem-⊥ {suc n} {a} {tg = tg} (there ()) | refl

  list-Monotone :
    ∀ {a : Set} → (sig : Σ[ gen ∈ 𝔾 a ] (Complete gen gen × (∀ {x : a}
    → Depth-Monotone gen x gen))) → ∀ {xs : List a}
    → Depth-Monotone (list (proj₁ sig)) xs (list (proj₁ sig))
  list-Monotone sig {[]} =
    ∥-monotone-left pure-monotone (λ {n} → []-elem-⊥ {n = n})
  list-Monotone (gen , (cp , mt)) {x ∷ xs} =
    ∥-monotone-right (λ {n} → ∷-elem-⊥ {n = n})
      (⊛-monotone ∷-bijective (`-monotone mt)
        (μ-monotone (list-Monotone (gen , cp , mt))))

  list-Complete :
    ∀ {a : Set}
    → (sig :
         Σ[ gen ∈ 𝔾 a ]
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
      ) → Complete (list (proj₁ sig)) (list (proj₁ sig))
  list-Complete sig {[]} = ∥-complete-left pure-complete
  list-Complete sig {x ∷ xs} =
    ∥-complete-right (⊛-complete
      (`-complete (proj₁ (proj₂ sig)))
      (μ-complete (list-Complete sig))
      (`-monotone (proj₂ (proj₂ sig)))
      (μ-monotone (list-Monotone sig))
    )

  list∼list' :
    ∀ {a : Set}
    → (sig :
        Σ[ gen ∈ 𝔾 a ]
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
      ) → (list (proj₁ sig)) ∼ (list' a (proj₁ sig))
  list∼list' {a} sig =
    Complete→eq
     {g₁ = list (proj₁ sig)}
     {g₂ = list' a (proj₁ sig)}
     (list-Complete sig)
     (isoGen-Complete (U~ ⊕~ ((K~ sig) ⊗~ I~)))
  
  ------ Pairs ------

  pair : ∀ {a b} → 𝔾 {0ℓ} a → 𝔾 b → 𝔾 (a × b)
  pair a b = ⦇ ` a , ` b ⦈

  pair' : ∀ {a b : Set} → 𝔾 a → 𝔾 b → 𝔾 (a × b)
  pair' {a} {b} gen₁ gen₂ =
   isoGen (a × b) ((K~ gen₁) ⊗~ (K~ gen₂))
  
  pair-Complete :
   ∀ {a b : Set}
   → (sig₁ :
       Σ[ gen ∈ 𝔾 a ]
         Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
     ) → (sig₂ :
       Σ[ gen ∈ 𝔾 b ]
         Complete gen gen × (∀ {y : b} → Depth-Monotone gen y gen)
     ) → Complete (pair (proj₁ sig₁) (proj₁ sig₂)) (pair (proj₁ sig₁) (proj₁ sig₂))
  pair-Complete sig₁ sig₂ = ⊛-complete
    (`-complete (proj₁ (proj₂ sig₁)))
    (`-complete (proj₁ (proj₂ sig₂)))
    (`-monotone (proj₂ (proj₂ sig₁)))
    (`-monotone (proj₂ (proj₂ sig₂)))

  
  pair∼pair' :
   ∀ {a b : Set}
   → (sig₁ :
       Σ[ gen ∈ 𝔾 a ]
         Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
     ) → (sig₂ :
       Σ[ gen ∈ 𝔾 b ]
         Complete gen gen × (∀ {y : b} → Depth-Monotone gen y gen)
     ) → (pair (proj₁ sig₁) (proj₁ sig₂)) ∼ pair' (proj₁ sig₁) (proj₁ sig₂)
  pair∼pair' {a} {b} sig₁ sig₂ =
    Complete→eq
     (pair-Complete sig₁ sig₂)
     (isoGen-Complete ((K~ sig₁) ⊗~ K~ sig₂))

  ------ Either ------

  either : ∀ {a b} → 𝔾 {0ℓ} a → 𝔾 b → 𝔾 (a ⊎ b)
  either a b = ⦇ inj₁ (` a) ⦈
             ∥ ⦇ inj₂ (` b) ⦈  

  either' : ∀ {a b : Set} → 𝔾 a → 𝔾 b → 𝔾 (a ⊎ b)
  either' {a} {b} gen₁ gen₂ =
   isoGen (a ⊎ b) ((K~ gen₁) ⊕~ (K~ gen₂))

  either-Complete :
    ∀ {a b : Set}
    → (sig₁ :
        Σ[ gen ∈ 𝔾 a ]
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
      ) → (sig₂ :
        Σ[ gen ∈ 𝔾 b ]
          Complete gen gen × (∀ {y : b} → Depth-Monotone gen y gen)
      ) → Complete (either (proj₁ sig₁) (proj₁ sig₂)) (either (proj₁ sig₁) (proj₁ sig₂))
  either-Complete sig₁ sig₂ =
    ∥-Complete
      (`-complete (proj₁ (proj₂ sig₁)))
      (`-complete (proj₁ (proj₂ sig₂)))
 
  either∼either' :
    ∀ {a b : Set}
    → (sig₁ :
        Σ[ gen ∈ 𝔾 a ]
          Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)
    ) → (sig₂ :
        Σ[ gen ∈ 𝔾 b ] Complete gen gen × (∀ {y : b} → Depth-Monotone gen y gen)
    ) → either (proj₁ sig₁) (proj₁ sig₂) ∼ either' (proj₁ sig₁) (proj₁ sig₂)
  either∼either' {a} {b} sig₁ sig₂ =
    Complete→eq
     (either-Complete sig₁ sig₂)
     (isoGen-Complete ((K~ sig₁) ⊕~ (K~ sig₂))) 
