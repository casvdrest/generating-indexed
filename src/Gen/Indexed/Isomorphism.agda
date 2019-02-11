{-# OPTIONS --type-in-type #-}

open import src.Gen.Indexed.Signature
open import src.Gen.Regular.Isomorphism using (_≅_)

open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module src.Gen.Indexed.Isomorphism where

   -- Function exensionality
  postulate funext : ∀ {ℓ} {a b : Set ℓ} {f g : a → b} → (∀ {x} → f x ≡ g x) → f ≡ g

  -- Variation on function extensionality for dependent functions (Π-types). 
  postulate funext' : ∀ {ℓ} {a : Set ℓ} {b : a → Set ℓ} {f g : Π a b} → (∀ {x} → f x ≡ g x) → f ≡ g 

  -- Functions with an empty domain are, by function extensionality,
  -- allways equal (provided that they have the same codomain)
  ⊥-funeq : ∀ {ℓ} {b : Set ℓ} {f g : ⊥ → b} → f ≡ g
  ⊥-funeq = funext λ {x} → ⊥-elim x


  ------ Naturals ------

  fromℕ : ℕ → μ Σ-nat tt
  fromℕ zero =
    `μ (inj₁ tt , λ())
  fromℕ (suc n) =
    `μ ((inj₂ tt) , (λ { tt → fromℕ n }))

  toℕ : μ Σ-nat tt → ℕ
  toℕ (`μ (inj₁ tt , _)) = zero
  toℕ (`μ (inj₂ tt , snd)) =
    suc (toℕ (snd tt))

  ℕ-iso₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  ℕ-iso₁ {zero} = refl
  ℕ-iso₁ {suc n} =
    cong suc ℕ-iso₁

  ℕ-iso₂ : ∀ {nf : μ Σ-nat tt} → fromℕ (toℕ nf) ≡ nf
  ℕ-iso₂ {`μ (inj₁ tt , snd)} rewrite
    ⊥-funeq {b = μ Σ-nat tt}
            {f = snd} {g = λ()}
    = refl 
  ℕ-iso₂ {`μ (inj₂ tt , snd)} =
    cong (λ x → `μ (inj₂ tt , λ {tt → x})) ℕ-iso₂

  ℕ≅Σ-nat : ℕ ≅ μ Σ-nat tt
  ℕ≅Σ-nat = record { from = fromℕ
                   ; to = toℕ
                   ; iso₁ = ℕ-iso₁
                   ; iso₂ = ℕ-iso₂
                   }

  ------ Finite Sets ------

  fromFin : ∀ {n : ℕ} → Fin n → μ Σ-fin n
  fromFin zero =
    `μ (inj₁ tt , λ())
  fromFin (suc f) =
    `μ (inj₂ tt , λ {tt → fromFin f})

  toFin : ∀ {n : ℕ} → μ Σ-fin n → Fin n
  toFin {zero} (`μ (() , snd))
  toFin {suc n} (`μ (inj₁ tt , snd)) = zero
  toFin {suc n} (`μ (inj₂ tt , snd)) =
    suc (toFin (snd tt))

  Fin-iso₁ : ∀ {n : ℕ} {f : Fin n} → toFin (fromFin f) ≡ f
  Fin-iso₁ {zero} {()}
  Fin-iso₁ {suc n} {zero} = refl
  Fin-iso₁ {suc n} {suc f} =
    cong suc Fin-iso₁

  Fin-iso₂ : ∀ {n : ℕ} {f : μ Σ-fin n} → fromFin (toFin f) ≡ f
  Fin-iso₂ {zero} {`μ (() , snd)}
  Fin-iso₂ {suc n} {`μ (inj₁ tt , snd)} rewrite
    funext' {a = ⊥} {f = snd} {g = λ()}
            (λ {x} → ⊥-elim x)
    = refl
  Fin-iso₂ {suc n} {`μ (inj₂ tt , snd)} =
    cong (λ x → `μ ((inj₂ tt) , λ {tt → x})) Fin-iso₂

  Fin≅Σ-fin : ∀ {n : ℕ} → Fin n ≅ μ Σ-fin n
  Fin≅Σ-fin = record { from = fromFin
                     ; to = toFin
                     ; iso₁ = Fin-iso₁
                     ; iso₂ = Fin-iso₂ 
                     }


  ------ Lists ------

  fromList : ∀ {a : Set} → List a → μ (Σ-list a) tt
  fromList [] =
    `μ (inj₁ tt , λ ())
  fromList (x ∷ xs) =
    `μ (inj₂ x , λ {tt → fromList xs})

  toList : ∀ {a : Set} → μ ((Σ-list a)) tt → List a
  toList (`μ (inj₁ tt , snd)) = []
  toList (`μ (inj₂ y , snd)) =
    y ∷ toList (snd tt)
  
  List-iso₁ : ∀ {a : Set} {xs : List a} → toList (fromList xs) ≡ xs
  List-iso₁ {xs = []} = refl
  List-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) List-iso₁

  List-iso₂ : ∀ {a : Set} {xs : μ (Σ-list a) tt } → fromList (toList xs) ≡ xs
  List-iso₂ {a} {xs = `μ (inj₁ tt , snd)} rewrite
    ⊥-funeq {b = μ (Σ-list a) tt}
            {f = snd} {g = λ()}
    = refl
  List-iso₂ {xs = `μ (inj₂ y , snd)} =
    cong (λ x → `μ (inj₂ y , x))
         (funext List-iso₂)

  List≅Σ-list : ∀ {a : Set} → List a ≅ μ (Σ-list a) tt
  List≅Σ-list = record { from = fromList
                       ; to   = toList
                       ; iso₁ = List-iso₁
                       ; iso₂ = List-iso₂
                       }

  ------ Vectors ------

  fromVec : ∀ {a : Set} {n : ℕ} → Vec a n → μ (Σ-vec a) n
  fromVec {n = 0}     []       =
    `μ (tt , λ())
  fromVec {n = suc n} (x ∷ xs) =
    `μ (x , λ { tt → fromVec xs })

  toVec : ∀ {a : Set} {n : ℕ} → μ (Σ-vec a) n → Vec a n
  toVec {n = zero} (`μ (tt , snd)) = []
  toVec {n = suc n} (`μ (x , snd)) =
    x ∷ toVec (snd tt)

  Vec-iso₁ : ∀ {a : Set} {n : ℕ} {xs : Vec a n} → toVec (fromVec xs) ≡ xs
  Vec-iso₁ {xs = []} = refl
  Vec-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) Vec-iso₁

  Vec-iso₂ : ∀ {a : Set} {n : ℕ} {xs : μ (Σ-vec a) n} → fromVec (toVec xs) ≡ xs
  Vec-iso₂ {n = zero}  {`μ (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd} {g = λ()}
            (λ {x} → ⊥-elim x)
    = refl
  Vec-iso₂ {n = suc n} {`μ (fst , snd)} = cong (λ x → `μ (fst , x)) (funext Vec-iso₂)

  Vec≅Σ-vec : ∀ {a : Set} {n : ℕ} → Vec a n ≅ μ (Σ-vec a) n
  Vec≅Σ-vec = record { from = fromVec
                     ; to   = toVec
                     ; iso₁ = Vec-iso₁
                     ; iso₂ = Vec-iso₂
                     }



  ------ LEQ ------
  
  from≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx) ≤ (proj₂ idx) → μ Σ-≤ idx 
  from≤ z≤n = `μ (tt , λ())
  from≤ (s≤s p) =
    `μ (tt , λ { tt → from≤ p })
  
  to≤ : ∀ {idx : ℕ × ℕ} → μ Σ-≤ idx → proj₁ idx ≤ proj₂ idx
  to≤ {zero , snd₁} (`μ (tt , snd)) = z≤n
  to≤ {suc fst₁ , zero} (`μ (() , snd))
  to≤ {suc fst₁ , suc snd₁} (`μ (tt , snd)) =
    s≤s (to≤ (snd tt))

  ≤-iso₁ : ∀ {idx : ℕ × ℕ} {p : proj₁ idx ≤ proj₂ idx} → to≤ (from≤ p) ≡ p
  ≤-iso₁ {.0 , snd} {z≤n} = refl
  ≤-iso₁ {.(suc _) , .(suc _)} {s≤s p} = cong s≤s ≤-iso₁

  ≤-iso₂ : ∀ {idx : ℕ × ℕ} {p : μ Σ-≤ idx} → from≤ (to≤ p) ≡ p
  ≤-iso₂ {zero , snd₁} {`μ (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ {x} → ⊥-elim x)
    = refl
  ≤-iso₂ {suc fst₁ , zero} {`μ (() , snd)}
  ≤-iso₂ {suc fst₁ , suc snd₁} {`μ (fst , snd)} =
    cong (λ x → `μ (fst , x)) (funext ≤-iso₂)

  ≤≅Σ-≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx ≤ proj₂ idx) ≅ μ Σ-≤ idx
  ≤≅Σ-≤ = record { from = from≤
                 ; to   = to≤
                 ; iso₁ = ≤-iso₁
                 ; iso₂ = ≤-iso₂
                 }


  ------ Sorted ------

  fromSorted : ∀ {xs : List ℕ} → Sorted xs → μ Σ-Sorted xs
  fromSorted nil = `μ (tt , λ())
  fromSorted single =
    `μ (tt , λ())
  fromSorted (step' x₁ p) =
    `μ (x₁ , λ { tt → fromSorted p } )

  toSorted : ∀ {xs : List ℕ} → μ Σ-Sorted xs → Sorted xs
  toSorted {[]} (`μ (tt , snd)) = nil
  toSorted {x ∷ []} (`μ (tt , snd)) = single
  toSorted {x ∷ x₁ ∷ xs} (`μ (fst , snd)) =
    step' fst (toSorted (snd tt))

  Sorted-iso₁ : ∀ {xs : List ℕ} {p : Sorted xs} → toSorted (fromSorted p) ≡ p
  Sorted-iso₁ {[]} {nil} = refl
  Sorted-iso₁ {x ∷ []} {single} = refl
  Sorted-iso₁ {x ∷ x₁ ∷ xs} {step' x₂ p} =
    cong (step' x₂) Sorted-iso₁

  Sorted-iso₂ : ∀ {xs : List ℕ} {p : μ Σ-Sorted xs} → fromSorted (toSorted p) ≡ p
  Sorted-iso₂ {[]} {`μ (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ {x} → ⊥-elim x)
    = refl
  Sorted-iso₂ {x ∷ []} {`μ (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ{x} → ⊥-elim x)
    = refl
  Sorted-iso₂ {x ∷ x₁ ∷ xs} {`μ (fst , snd)} =
    cong (λ x → `μ (fst , x)) (funext Sorted-iso₂)

  Sorted≅Σ-Sorted : ∀ {xs : List ℕ} → Sorted xs ≅ μ Σ-Sorted xs
  Sorted≅Σ-Sorted = record { from = fromSorted
                           ; to   = toSorted
                           ; iso₁ = Sorted-iso₁
                           ; iso₂ = Sorted-iso₂
                           }


  
  
