{-# OPTIONS --type-in-type #-}

open import src.Gen.Indexed.Signature
open import src.Gen.Base
open import src.Gen.Regular.Isomorphism using (_≅_)

open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)

open import Category.Applicative

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

module src.Gen.Indexed.Isomorphism where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)

   -- Function exensionality
  postulate funext : ∀ {ℓ} {a b : Set ℓ} {f g : a → b} → (∀ {x} → f x ≡ g x) → f ≡ g

  -- Variation on function extensionality for dependent functions (Π-types). 
  postulate funext' : ∀ {ℓ} {a : Set ℓ} {b : a → Set ℓ} {f g : Π a b} → (∀ {x} → f x ≡ g x) → f ≡ g 

  -- Functions with an empty domain are, by function extensionality,
  -- allways equal (provided that they have the same codomain)
  ⊥-funeq : ∀ {ℓ} {b : Set ℓ} {f g : ⊥ → b} → f ≡ g
  ⊥-funeq = funext λ {x} → ⊥-elim x


  ------ Naturals ------

  fromℕ : ℕ → Fix Σ-nat tt
  fromℕ zero =
    In (inj₁ tt , λ())
  fromℕ (suc n) =
    In ((inj₂ tt) , (λ { tt → fromℕ n }))

  toℕ : Fix Σ-nat tt → ℕ
  toℕ (In (inj₁ tt , _)) = zero
  toℕ (In (inj₂ tt , snd)) =
    suc (toℕ (snd tt))

  ℕ-iso₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  ℕ-iso₁ {zero} = refl
  ℕ-iso₁ {suc n} =
    cong suc ℕ-iso₁

  ℕ-iso₂ : ∀ {nf : Fix Σ-nat tt} → fromℕ (toℕ nf) ≡ nf
  ℕ-iso₂ {In (inj₁ tt , snd)} rewrite
    ⊥-funeq {b = Fix Σ-nat tt}
            {f = snd} {g = λ()}
    = refl 
  ℕ-iso₂ {In (inj₂ tt , snd)} =
    cong (λ x → In (inj₂ tt , λ {tt → x})) ℕ-iso₂

  ℕ≅Σ-nat : ℕ ≅ Fix Σ-nat tt
  ℕ≅Σ-nat = record { from = fromℕ
                   ; to = toℕ
                   ; iso₁ = ℕ-iso₁
                   ; iso₂ = ℕ-iso₂
                   }

  ------ Finite Sets ------

  fromFin : ∀ {n : ℕ} → Fin n → Fix Σ-fin n
  fromFin zero =
    In (inj₁ tt , λ())
  fromFin (suc f) =
    In (inj₂ tt , λ {tt → fromFin f})

  toFin : ∀ {n : ℕ} → Fix Σ-fin n → Fin n
  toFin {zero} (In (() , snd))
  toFin {suc n} (In (inj₁ tt , snd)) = zero
  toFin {suc n} (In (inj₂ tt , snd)) =
    suc (toFin (snd tt))

  Fin-iso₁ : ∀ {n : ℕ} {f : Fin n} → toFin (fromFin f) ≡ f
  Fin-iso₁ {zero} {()}
  Fin-iso₁ {suc n} {zero} = refl
  Fin-iso₁ {suc n} {suc f} =
    cong suc Fin-iso₁

  Fin-iso₂ : ∀ {n : ℕ} {f : Fix Σ-fin n} → fromFin (toFin f) ≡ f
  Fin-iso₂ {zero} {In (() , snd)}
  Fin-iso₂ {suc n} {In (inj₁ tt , snd)} rewrite
    funext' {a = ⊥} {f = snd} {g = λ()}
            (λ {x} → ⊥-elim x)
    = refl
  Fin-iso₂ {suc n} {In (inj₂ tt , snd)} =
    cong (λ x → In ((inj₂ tt) , λ {tt → x})) Fin-iso₂

  Fin≅Σ-fin : ∀ {n : ℕ} → Fin n ≅ Fix Σ-fin n
  Fin≅Σ-fin = record { from = fromFin
                     ; to   = toFin
                     ; iso₁ = Fin-iso₁
                     ; iso₂ = Fin-iso₂ 
                     }

  ------ Well-Scoped Lambda Terms ------

  fromTerm : ∀ {n : ℕ} → Term n → Fix Σ-Term n
  fromTerm {zero} (Abs t) =
    In (inj₁ tt , λ { tt → fromTerm t })
  fromTerm {zero} (App t t₁) =
    In (inj₂ tt , λ { (inj₁ tt) → fromTerm t ; (inj₂ tt) → fromTerm t₁ })
  fromTerm {zero} (Var ())
  fromTerm {suc n} (Abs t) =
    In ((inj₁ tt) , λ { tt → fromTerm t })
  fromTerm {suc n} (App t t₁) =
    In ((inj₂ (inj₁ tt)) , (λ { (inj₁ tt) → fromTerm t ; (inj₂ tt) → fromTerm t₁ }))
  fromTerm {suc n} (Var x) =
    In ((inj₂ (inj₂ x)) , λ())

  toTerm : ∀ {n : ℕ} → Fix Σ-Term n → Term n
  toTerm {zero} (In (inj₁ tt , snd)) =
    Abs (toTerm (snd tt))
  toTerm {zero} (In (inj₂ tt , snd)) =
    App (toTerm (snd (inj₁ tt))) (toTerm (snd (inj₂ tt)))
  toTerm {suc n} (In (inj₁ tt , snd)) =
    Abs (toTerm (snd tt))
  toTerm {suc n} (In (inj₂ (inj₁ tt) , snd)) =
    App (toTerm (snd (inj₁ tt))) (toTerm (snd (inj₂ tt)))
  toTerm {suc n} (In (inj₂ (inj₂ y) , snd)) =
    Var y

  ,-eq : ∀ {a b} {x₁ x₂ : a} {y₁ y₂ : b}
         → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
  ,-eq refl refl = refl

  Term-iso₁ : ∀ {n : ℕ} {t : Term n} → toTerm (fromTerm t) ≡ t
  Term-iso₁ {zero} {Abs t} =
    cong Abs Term-iso₁
  Term-iso₁ {zero} {App t₁ t₂} =
    cong (uncurry App) (,-eq Term-iso₁ Term-iso₁) 
  Term-iso₁ {zero} {Var ()}
  Term-iso₁ {suc n} {Abs t} =
    cong Abs Term-iso₁
  Term-iso₁ {suc n} {App t t₁} =
    cong (uncurry App) (,-eq Term-iso₁ Term-iso₁)
  Term-iso₁ {suc n} {Var x} = refl

  Term-iso₂ : ∀ {n : ℕ} {t : Fix Σ-Term n} → fromTerm (toTerm t) ≡ t
  Term-iso₂ {zero} {In (inj₁ tt , snd)} =
    cong (In ∘ λ x → inj₁ tt , x) (funext Term-iso₂)
  Term-iso₂ {zero} {In (inj₂ tt , snd)} =
    cong (In ∘ λ x → inj₂ tt , x) (
      funext' λ { {inj₁ x} → Term-iso₂ ; {inj₂ y} → Term-iso₂ })
  Term-iso₂ {suc n} {In (inj₁ tt , snd)} =
    cong (In ∘ λ x → (inj₁ tt) , x) (funext Term-iso₂)
  Term-iso₂ {suc n} {In (inj₂ (inj₁ tt) , snd)} =
    cong (In ∘ λ x → (inj₂ (inj₁ tt)) , x)
      (funext' λ { {inj₁ tt} → Term-iso₂ ; {inj₂ tt} → Term-iso₂ })
  Term-iso₂ {suc n} {In (inj₂ (inj₂ y) , snd)} =
    cong (In ∘ λ x → (inj₂ (inj₂ y)) , x) (funext' λ {x} → ⊥-elim x)

  Term≅Σ-Term : ∀ {n : ℕ} → Term n ≅ Fix Σ-Term n
  Term≅Σ-Term = record { from = fromTerm
                       ; to   = toTerm
                       ; iso₁ = Term-iso₁
                       ; iso₂ = Term-iso₂
                       }

  
  ------ Lists ------

  fromList : ∀ {a : Set} → List a → Fix (Σ-list a) tt
  fromList [] =
    In (inj₁ tt , λ ())
  fromList (x ∷ xs) =
    In (inj₂ x , λ {tt → fromList xs})

  toList : ∀ {a : Set} → Fix ((Σ-list a)) tt → List a
  toList (In (inj₁ tt , snd)) = []
  toList (In (inj₂ y , snd)) =
    y ∷ toList (snd tt)
  
  List-iso₁ : ∀ {a : Set} {xs : List a} → toList (fromList xs) ≡ xs
  List-iso₁ {xs = []} = refl
  List-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) List-iso₁

  List-iso₂ : ∀ {a : Set} {xs : Fix (Σ-list a) tt } → fromList (toList xs) ≡ xs
  List-iso₂ {a} {xs = In (inj₁ tt , snd)} rewrite
    ⊥-funeq {b = Fix (Σ-list a) tt}
            {f = snd} {g = λ()}
    = refl
  List-iso₂ {xs = In (inj₂ y , snd)} =
    cong (λ x → In (inj₂ y , x))
         (funext List-iso₂)

  List≅Σ-list : ∀ {a : Set} → List a ≅ Fix (Σ-list a) tt
  List≅Σ-list = record { from = fromList
                       ; to   = toList
                       ; iso₁ = List-iso₁
                       ; iso₂ = List-iso₂
                       }

  
  ------ Vectors ------

  fromVec : ∀ {a : Set} {n : ℕ} → Vec a n → Fix (Σ-vec a) n
  fromVec {n = 0}     []       =
    In (tt , λ())
  fromVec {n = suc n} (x ∷ xs) =
    In (x , λ { tt → fromVec xs })

  toVec : ∀ {a : Set} {n : ℕ} → Fix (Σ-vec a) n → Vec a n
  toVec {n = zero} (In (tt , snd)) = []
  toVec {n = suc n} (In (x , snd)) =
    x ∷ toVec (snd tt)

  Vec-iso₁ : ∀ {a : Set} {n : ℕ} {xs : Vec a n} → toVec (fromVec xs) ≡ xs
  Vec-iso₁ {xs = []} = refl
  Vec-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) Vec-iso₁

  Vec-iso₂ : ∀ {a : Set} {n : ℕ} {xs : Fix (Σ-vec a) n} → fromVec (toVec xs) ≡ xs
  Vec-iso₂ {n = zero}  {In (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd} {g = λ()}
            (λ {x} → ⊥-elim x)
    = refl
  Vec-iso₂ {n = suc n} {In (fst , snd)} = cong (λ x → In (fst , x)) (funext Vec-iso₂)

  Vec≅Σ-vec : ∀ {a : Set} {n : ℕ} → Vec a n ≅ Fix (Σ-vec a) n
  Vec≅Σ-vec = record { from = fromVec
                     ; to   = toVec
                     ; iso₁ = Vec-iso₁
                     ; iso₂ = Vec-iso₂
                     }
  
  ------ LEQ ------
  
  from≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx) ≤ (proj₂ idx) → Fix Σ-≤ idx 
  from≤ z≤n = In (tt , λ())
  from≤ (s≤s p) =
    In (tt , λ { tt → from≤ p })
  
  to≤ : ∀ {idx : ℕ × ℕ} → Fix Σ-≤ idx → proj₁ idx ≤ proj₂ idx
  to≤ {zero , snd₁} (In (tt , snd)) = z≤n
  to≤ {suc fst₁ , zero} (In (() , snd))
  to≤ {suc fst₁ , suc snd₁} (In (tt , snd)) =
    s≤s (to≤ (snd tt))

  ≤-iso₁ : ∀ {idx : ℕ × ℕ} {p : proj₁ idx ≤ proj₂ idx} → to≤ (from≤ p) ≡ p
  ≤-iso₁ {.0 , snd} {z≤n} = refl
  ≤-iso₁ {.(suc _) , .(suc _)} {s≤s p} = cong s≤s ≤-iso₁

  ≤-iso₂ : ∀ {idx : ℕ × ℕ} {p : Fix Σ-≤ idx} → from≤ (to≤ p) ≡ p
  ≤-iso₂ {zero , snd₁} {In (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ {x} → ⊥-elim x)
    = refl
  ≤-iso₂ {suc fst₁ , zero} {In (() , snd)}
  ≤-iso₂ {suc fst₁ , suc snd₁} {In (fst , snd)} =
    cong (λ x → In (fst , x)) (funext ≤-iso₂)

  ≤≅Σ-≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx ≤ proj₂ idx) ≅ Fix Σ-≤ idx
  ≤≅Σ-≤ = record { from = from≤
                 ; to   = to≤
                 ; iso₁ = ≤-iso₁
                 ; iso₂ = ≤-iso₂
                 }


  ------ Sorted ------

  fromSorted : ∀ {xs : List ℕ} → Sorted xs → Fix Σ-Sorted xs
  fromSorted nil = In (tt , λ())
  fromSorted single =
    In (tt , λ())
  fromSorted (step' x₁ p) =
    In (x₁ , λ { tt → fromSorted p } )

  toSorted : ∀ {xs : List ℕ} → Fix Σ-Sorted xs → Sorted xs
  toSorted {[]} (In (tt , snd)) = nil
  toSorted {x ∷ []} (In (tt , snd)) = single
  toSorted {x ∷ x₁ ∷ xs} (In (fst , snd)) =
    step' fst (toSorted (snd tt))

  Sorted-iso₁ : ∀ {xs : List ℕ} {p : Sorted xs} → toSorted (fromSorted p) ≡ p
  Sorted-iso₁ {[]} {nil} = refl
  Sorted-iso₁ {x ∷ []} {single} = refl
  Sorted-iso₁ {x ∷ x₁ ∷ xs} {step' x₂ p} =
    cong (step' x₂) Sorted-iso₁

  Sorted-iso₂ : ∀ {xs : List ℕ} {p : Fix Σ-Sorted xs} → fromSorted (toSorted p) ≡ p
  Sorted-iso₂ {[]} {In (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ {x} → ⊥-elim x)
    = refl
  Sorted-iso₂ {x ∷ []} {In (tt , snd)} rewrite
    funext' {a = ⊥} {f = snd}
            {g = λ()} (λ{x} → ⊥-elim x)
    = refl
  Sorted-iso₂ {x ∷ x₁ ∷ xs} {In (fst , snd)} =
    cong (λ x → In (fst , x)) (funext Sorted-iso₂)

  Sorted≅Σ-Sorted : ∀ {xs : List ℕ} → Sorted xs ≅ Fix Σ-Sorted xs
  Sorted≅Σ-Sorted = record { from = fromSorted
                           ; to   = toSorted
                           ; iso₁ = Sorted-iso₁
                           ; iso₂ = Sorted-iso₂
                           }
                           
