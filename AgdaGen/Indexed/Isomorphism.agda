{-# OPTIONS --type-in-type #-}

open import AgdaGen.Indexed.Signature
open import AgdaGen.Base
open import AgdaGen.Regular.Isomorphism 
open import AgdaGen.Regular.Generic
open import AgdaGen.Indexed.Generic
open import AgdaGen.Regular.Cogen
open import AgdaGen.Indexed.PiGen

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

module AgdaGen.Indexed.Isomorphism where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)

  triv : (a : Set) → ⊤ → Set
  triv a tt = a

  record MultiSorted {i : Set} (a : i → Set) : Set where
    field
      Wᵢ : Σ[ Σ ∈ Sig i ] (∀ {x : i} → a x ≅ Fixₛ Σ x)

  getΣ : ∀ {i : Set} {a : i → Set} → MultiSorted a → Sig i
  getΣ (record { Wᵢ = Σ , _ }) = Σ

  isoGenᵢ : ∀ {i : Set} {a : i → Set} → ⦃ p : MultiSorted a ⦄
           → ((x : i) → RegInfo (λ op → 𝔾 op × Π𝔾 op) (Sig.Op (getΣ p) x))
           → ((x : i) → (op : Fix (Sig.Op (getΣ p) x))
                 → RegInfo (λ op → 𝔾 op × Π𝔾 op) (Sig.Ar (getΣ p) op)) → 𝔾ᵢ a
  isoGenᵢ ⦃ p = record { Wᵢ = Σ , iso } ⦄ sig₁ sig₂ x =
    ⦇ (_≅_.to iso ∘ Inₛ) (` deriveGenᵢ sig₁ sig₂ x) ⦈ 
      
   -- Function exensionality
  postulate funext : ∀ {a b : Set} {f g : a → b} → (∀ {x} → f x ≡ g x) → f ≡ g

  -- Variation on function extensionality for dependent functions (Π-types). 
  postulate funext' : ∀ {a : Set} {b : a → Set} {f g : Π a b} → (∀ {x} → f x ≡ g x) → f ≡ g 

  -- Functions with an empty domain are, by function extensionality,
  -- allways equal (provided that they have the same codomain)
  ⊥-funeq : ∀ {ℓ} {b : Set ℓ} {f g : ⊥ → b} → f ≡ g
  ⊥-funeq = funext λ { {()} }

  Fix-⊥-eq : ∀ {b : Fix Z → Set} {f g : Π (Fix Z) b} → f ≡ g
  Fix-⊥-eq = funext' λ { {In ()} }

  cong₂ : ∀ {a b c : Set} {x₁ x₂ : a} {y₁ y₂ : b} → (f : a → b → c) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂ 
  cong₂ f refl refl = refl
  
   ------ Naturals ------

  fromℕ : ℕ → Fixₛ Σ-nat tt
  fromℕ zero =
    Inₛ (In (inj₁ tt) , λ { (In ()) })
  fromℕ (suc n) =
    Inₛ (In (inj₂ tt) , (λ { (In tt) → fromℕ n }))

  toℕ : Fixₛ Σ-nat tt → ℕ
  toℕ (Inₛ (In (inj₁ tt) , _)) = zero
  toℕ (Inₛ (In (inj₂ tt) , snd)) =
    suc (toℕ (snd (In tt)))

  ℕ-iso₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  ℕ-iso₁ {zero} = refl
  ℕ-iso₁ {suc n} =
    cong suc ℕ-iso₁

  ℕ-iso₂ : ∀ {n : Fixₛ Σ-nat tt} → fromℕ (toℕ n) ≡ n
  ℕ-iso₂ {Inₛ (In (inj₁ tt) , snd)} =
    cong (λ x → Inₛ ((In (inj₁ tt)) , x)) (funext λ { {In ()} })
  ℕ-iso₂ {Inₛ (In (inj₂ tt) , snd)} =
    cong (λ x → Inₛ ((In (inj₂ tt)) , x)) (funext λ { {In tt} → ℕ-iso₂ })

  ℕ≅Σ-nat : ℕ ≅ Fixₛ Σ-nat tt
  ℕ≅Σ-nat =
    record { from = fromℕ
           ; to   = toℕ
           ; iso₁ = ℕ-iso₁
           ; iso₂ = ℕ-iso₂
           }

  instance
    ℕ-MultiSorted : MultiSorted (triv ℕ)
    ℕ-MultiSorted = record { Wᵢ = Σ-nat , ℕ≅Σ-nat }
  
  ------ Finite Sets ------

  fromFin : ∀ {n : ℕ} → Fin n → Fixₛ Σ-fin n
  fromFin zero =
    Inₛ (In (inj₁ tt) , λ { (In ()) })
  fromFin (suc f) =
    Inₛ (In (inj₂ tt) , λ { (In tt) → fromFin f})
  
  toFin : ∀ {n : ℕ} → Fixₛ Σ-fin n → Fin n
  toFin {zero} (Inₛ (In () , snd))
  toFin {suc n} (Inₛ (In (inj₁ tt) , snd)) = zero
  toFin {suc n} (Inₛ (In (inj₂ tt) , snd)) = suc (toFin (snd (In tt)))

  
  Fin-iso₁ : ∀ {n : ℕ} {f : Fin n} → toFin (fromFin f) ≡ f
  Fin-iso₁ {zero} {()}
  Fin-iso₁ {suc n} {zero} = refl
  Fin-iso₁ {suc n} {suc f} =
    cong suc Fin-iso₁
  
  Fin-iso₂ : ∀ {n : ℕ} {f : Fixₛ Σ-fin n} → fromFin (toFin f) ≡ f
  Fin-iso₂ {zero} {Inₛ (In () , snd)}
  Fin-iso₂ {suc n} {Inₛ (In (inj₁ tt) , snd)} =
    cong (λ x → Inₛ (In (inj₁ tt) , x)) (funext' λ { {In ()} })
  Fin-iso₂ {suc n} {Inₛ (In (inj₂ tt) , snd)} =
    cong (λ x → Inₛ (In (inj₂ tt) , x)) (funext' λ { {In tt} → Fin-iso₂ })

  
  Fin≅Σ-fin : ∀ {n : ℕ} → Fin n ≅ Fixₛ Σ-fin n
  Fin≅Σ-fin =
    record { from = fromFin
           ; to   = toFin
           ; iso₁ = Fin-iso₁
           ; iso₂ = Fin-iso₂ 
           }

  instance
    Fin-MultiSorted : MultiSorted Fin
    Fin-MultiSorted = record { Wᵢ = Σ-fin , Fin≅Σ-fin }

  ------ Well-Scoped Lambda Terms ------
  
  fromTerm : ∀ {n : ℕ} → Term n → Fixₛ Σ-Term n
  fromTerm {zero} (Abs t) =
    Inₛ (In (inj₁ tt) , λ { (In tt) → fromTerm t })
  fromTerm {zero} (App t t₁) =
    Inₛ (In (inj₂ tt) , λ { (In (inj₁ tt))
      → fromTerm t ; (In (inj₂ tt)) → fromTerm t₁ })
  fromTerm {zero} (Var ())
  fromTerm {suc n} (Abs t) =
    Inₛ ((In (inj₁ tt)) , λ { (In tt) → fromTerm t })
  fromTerm {suc n} (App t t₁) =
    Inₛ (In (inj₂ (inj₁ tt)) , (λ { (In (inj₁ tt))
      → fromTerm t ; (In (inj₂ tt)) → fromTerm t₁ }))
  fromTerm {suc n} (Var x) =
    Inₛ (In (inj₂ (inj₂ x)) , λ { (In ()) })

  
  toTerm : ∀ {n : ℕ} → Fixₛ Σ-Term n → Term n
  toTerm {zero} (Inₛ (In (inj₁ tt) , snd)) =
    Abs (toTerm (snd (In tt)))
  toTerm {zero} (Inₛ (In (inj₂ tt) , snd)) =
    App (toTerm (snd (In (inj₁ tt)))) (toTerm (snd (In (inj₂ tt))))
  toTerm {suc n} (Inₛ (In (inj₁ tt) , snd)) =
    Abs (toTerm (snd (In tt)))
  toTerm {suc n} (Inₛ (In (inj₂ (inj₁ tt)) , snd)) =
    App (toTerm (snd (In (inj₁ tt)))) (toTerm (snd (In (inj₂ tt))))
  toTerm {suc n} (Inₛ (In (inj₂ (inj₂ y)) , snd)) =
    Var y 
  
  Term-iso₁ : ∀ {n : ℕ} {t : Term n} → toTerm (fromTerm t) ≡ t
  Term-iso₁ {zero} {Abs t} =
    cong Abs Term-iso₁
  Term-iso₁ {zero} {App t₁ t₂} =
    cong (uncurry App) (cong₂ _,_ Term-iso₁ Term-iso₁) 
  Term-iso₁ {zero} {Var ()}
  Term-iso₁ {suc n} {Abs t} =
    cong Abs Term-iso₁
  Term-iso₁ {suc n} {App t t₁} =
    cong (uncurry App) (cong₂ _,_ Term-iso₁ Term-iso₁)
  Term-iso₁ {suc n} {Var x} = refl
  
  Term-iso₂ : ∀ {n : ℕ} {t : Fixₛ Σ-Term n} → fromTerm (toTerm t) ≡ t
  Term-iso₂ {zero} {Inₛ (In (inj₁ tt) , snd)} =
    cong (λ x → Inₛ ((In (inj₁ tt)) , x)) (funext' λ { {In tt} → Term-iso₂})
  Term-iso₂ {zero} {Inₛ (In (inj₂ tt) , snd)} =
    cong (λ x → Inₛ (In (inj₂ tt) , x))
      (funext' λ {
        {In (inj₁ tt)} → Term-iso₂
      ; {In (inj₂ tt)} → Term-iso₂
      })
  Term-iso₂ {suc n} {Inₛ (In (inj₁ tt) , snd)} =
    cong (λ x → Inₛ ((In (inj₁ tt)) , x)) (funext' λ { {In tt} → Term-iso₂ })
  Term-iso₂ {suc n} {Inₛ (In (inj₂ (inj₁ tt)) , snd)} =
    cong (λ x → Inₛ ((In (inj₂ (inj₁ tt))) , x))
      (funext' λ {
        {In (inj₁ tt)} → Term-iso₂
      ; {In (inj₂ tt)} → Term-iso₂
      })
  Term-iso₂ {suc n} {Inₛ (In (inj₂ (inj₂ y)) , snd)} =
    cong (λ x → Inₛ (In (inj₂ (inj₂ y)) , x)) (funext' λ { {In ()} })

  
  Term≅Σ-Term : ∀ {n : ℕ} → Term n ≅ Fixₛ Σ-Term n
  Term≅Σ-Term =
    record { from = fromTerm
           ; to   = toTerm
           ; iso₁ = Term-iso₁
           ; iso₂ = Term-iso₂
           }

  instance
    Term-MultiSorted : MultiSorted Term
    Term-MultiSorted = record { Wᵢ = Σ-Term , Term≅Σ-Term }

  ------ Lists ------

  fromList : ∀ {a : Set} → List a → Fixₛ (Σ-list a) tt
  fromList [] =
    Inₛ (In (inj₁ tt) , λ { (In ()) })
  fromList (x ∷ xs) =
    Inₛ (In (inj₂ x) , λ { (In tt) → fromList xs})

  toList : ∀ {a : Set} → Fixₛ ((Σ-list a)) tt → List a
  toList (Inₛ (In (inj₁ tt) , snd)) = []
  toList (Inₛ (In (inj₂ y) , snd)) =
    y ∷ toList (snd (In tt))
  
  List-iso₁ : ∀ {a : Set} {xs : List a} → toList (fromList xs) ≡ xs
  List-iso₁ {xs = []} = refl
  List-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) List-iso₁
  
  List-iso₂ : ∀ {a : Set} {xs : Fixₛ (Σ-list a) tt } → fromList (toList xs) ≡ xs
  List-iso₂ {a} {Inₛ (In (inj₁ tt) , snd)} =
    cong (λ x → Inₛ ((In (inj₁ tt)) , x)) (funext λ { {In ()} })
  List-iso₂ {a} {Inₛ (In (inj₂ y) , snd)} =
    cong (λ x → Inₛ ((In (inj₂ y)) , x)) (funext λ { {In tt} → List-iso₂} )

  List≅Σ-list : ∀ {a : Set} → List a ≅ Fixₛ (Σ-list a) tt
  List≅Σ-list =
    record { from = fromList
           ; to   = toList
           ; iso₁ = List-iso₁
           ; iso₂ = List-iso₂
           }

  instance
    List-MultiSorted : ∀ {a : Set} → MultiSorted (triv (List a))
    List-MultiSorted {a} = record { Wᵢ = Σ-list a , List≅Σ-list }

  ------ Vectors ------

  fromVec : ∀ {a : Set} {n : ℕ} → Vec a n → Fixₛ (Σ-vec a) n
  fromVec {n = 0}     []       =
    Inₛ (In tt , λ { (In ()) })
  fromVec {n = suc n} (x ∷ xs) =
    Inₛ (In x , λ { (In tt) → fromVec xs })

  toVec : ∀ {a : Set} {n : ℕ} → Fixₛ (Σ-vec a) n → Vec a n
  toVec {n = zero} (Inₛ (In tt , snd)) = []
  toVec {n = suc n} (Inₛ (In x , snd)) =
    x ∷ toVec (snd (In tt))

  
  Vec-iso₁ : ∀ {a : Set} {n : ℕ} {xs : Vec a n} → toVec (fromVec xs) ≡ xs
  Vec-iso₁ {xs = []} = refl
  Vec-iso₁ {xs = x ∷ xs} =
    cong (_∷_ x) Vec-iso₁
  
  Vec-iso₂ : ∀ {a : Set} {n : ℕ} {xs : Fixₛ (Σ-vec a) n} → fromVec (toVec xs) ≡ xs
  Vec-iso₂ {n = zero} {Inₛ (In tt , snd)} =
    cong (λ x → Inₛ ((In tt) , x)) (funext' λ { {In ()} })
  Vec-iso₂ {n = suc n} {Inₛ (In y , snd)} =
    cong (λ x → Inₛ ((In y) , x)) (funext' λ { {In tt} → Vec-iso₂})

  Vec≅Σ-vec : ∀ {a : Set} {n : ℕ} → Vec a n ≅ Fixₛ (Σ-vec a) n
  Vec≅Σ-vec =
    record { from = fromVec
           ; to   = toVec
           ; iso₁ = Vec-iso₁
           ; iso₂ = Vec-iso₂
           }

  instance
    Vec-MultiSorted : ∀ {a : Set} → MultiSorted (Vec a)
    Vec-MultiSorted {a} = record { Wᵢ = Σ-vec a , Vec≅Σ-vec }

  ------ LEQ ------
  
  from≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx) ≤ (proj₂ idx) → Fixₛ Σ-≤ idx 
  from≤ z≤n = Inₛ (In tt , λ { (In ()) })
  from≤ (s≤s p) =
    Inₛ (In tt , λ { (In tt) → from≤ p })
  
  to≤ : ∀ {idx : ℕ × ℕ} → Fixₛ Σ-≤ idx → proj₁ idx ≤ proj₂ idx
  to≤ {zero , snd₁} (Inₛ (In tt , snd)) = z≤n
  to≤ {suc fst , zero} (Inₛ (In () , snd))
  to≤ {suc fst , suc snd₁} (Inₛ (In x , snd)) =
    s≤s (to≤ (snd (In x)))
  
  ≤-iso₁ : ∀ {idx : ℕ × ℕ} {p : proj₁ idx ≤ proj₂ idx} → to≤ (from≤ p) ≡ p
  ≤-iso₁ {.0 , snd} {z≤n} = refl
  ≤-iso₁ {.(suc _) , .(suc _)} {s≤s p} = cong s≤s ≤-iso₁


  ≤-iso₂ : ∀ {idx : ℕ × ℕ} {p : Fixₛ Σ-≤ idx} → from≤ (to≤ p) ≡ p
  ≤-iso₂ {zero , m} {Inₛ (In tt , snd₁)} = cong (λ x → Inₛ ((In tt) , x)) (funext' λ { {In ()} })
  ≤-iso₂ {suc n , zero} {Inₛ (In () , snd)}
  ≤-iso₂ {suc n , suc m} {Inₛ (In tt , snd)} = cong (λ x → Inₛ (In tt , x)) (funext' λ { {In tt} → ≤-iso₂ })

  ≤≅Σ-≤ : ∀ {idx : ℕ × ℕ} → (proj₁ idx ≤ proj₂ idx) ≅ Fixₛ Σ-≤ idx
  ≤≅Σ-≤ =
    record { from = from≤
           ; to   = to≤
           ; iso₁ = ≤-iso₁
           ; iso₂ = ≤-iso₂
           }

  instance
    ≤-MultiSorted : MultiSorted (uncurry _≤_)
    ≤-MultiSorted = record { Wᵢ = Σ-≤ , ≤≅Σ-≤ }

  ------ Sorted ------

  fromSorted : ∀ {xs : List ℕ} → Sorted xs → Fixₛ Σ-Sorted xs
  fromSorted nil = Inₛ (In tt , λ { (In ()) })
  fromSorted single =
    Inₛ (In tt , λ { (In ()) })
  fromSorted (step' x₁ p) =
    Inₛ (In x₁ , λ { (In tt) → fromSorted p } )

  toSorted : ∀ {xs : List ℕ} → Fixₛ Σ-Sorted xs → Sorted xs
  toSorted {[]} (Inₛ (In tt , snd)) = nil
  toSorted {x ∷ []} (Inₛ (In tt , snd)) = single
  toSorted {x ∷ x₁ ∷ xs} (Inₛ ((In fst) , snd)) =
    step' fst (toSorted (snd (In tt)))


  Sorted-iso₁ : ∀ {xs : List ℕ} {p : Sorted xs} → toSorted (fromSorted p) ≡ p
  Sorted-iso₁ {[]} {nil} = refl
  Sorted-iso₁ {x ∷ []} {single} = refl
  Sorted-iso₁ {x ∷ x₁ ∷ xs} {step' x₂ p} =
    cong (step' x₂) Sorted-iso₁


  Sorted-iso₂ : ∀ {xs : List ℕ} {p : Fixₛ Σ-Sorted xs} → fromSorted (toSorted p) ≡ p
  Sorted-iso₂ {[]} {Inₛ (In tt , snd)} =
    cong (λ x → Inₛ ((In tt) , x)) (funext' λ { {In ()} })
  Sorted-iso₂ {x ∷ []} {Inₛ (In tt , snd)} =
    cong (λ v → Inₛ ((In tt) , v)) (funext' λ { {In ()} })
  Sorted-iso₂ {x ∷ x₁ ∷ xs} {Inₛ (In prf , snd)} =
    cong (λ x → Inₛ ((In prf) , x)) (funext' λ { {In tt} → Sorted-iso₂ })

  Sorted≅Σ-Sorted : ∀ {xs : List ℕ} → Sorted xs ≅ Fixₛ Σ-Sorted xs
  Sorted≅Σ-Sorted =
    record { from = fromSorted
           ; to   = toSorted
           ; iso₁ = Sorted-iso₁
           ; iso₂ = Sorted-iso₂
           }

  instance
    Sorted-MultiSorted : MultiSorted Sorted
    Sorted-MultiSorted = record { Wᵢ = Σ-Sorted , Sorted≅Σ-Sorted }
                           
  ------ Perfect Trees -----

  fromPerfect : ∀ {a : Set} {n : ℕ} → Perfect a n → Fixₛ (Σ-Perfect {a}) n
  fromPerfect {a} {zero} p =
    Inₛ ((In tt) , λ { (In ()) })
  fromPerfect {a} {suc n} (Node x pₗ pᵣ) =
    Inₛ ((In x) , (λ { (In (inj₁ x))
      → fromPerfect pₗ ; (In (inj₂ y)) → fromPerfect pᵣ })
    )

  toPerfect : ∀ {a : Set} {n : ℕ} → Fixₛ (Σ-Perfect {a}) n → Perfect a n
  toPerfect {n = zero} (Inₛ (In tt , snd)) = Leaf
  toPerfect {n = suc n} (Inₛ (In x , snd)) =
    Node x (toPerfect (snd (In (inj₁ tt)))) (toPerfect (snd (In (inj₂ tt))))

  Perfect-iso₁ : ∀ {a : Set} {n : ℕ} {p : Perfect a n} → toPerfect (fromPerfect p) ≡ p
  Perfect-iso₁ {n = zero} {Leaf} = refl
  Perfect-iso₁ {n = suc n} {Node x pl pr} =
    cong₂ (Node x) Perfect-iso₁ Perfect-iso₁

  Perfect-iso₂ : ∀ {a : Set} {n : ℕ} {p : Fixₛ (Σ-Perfect {a}) n} → fromPerfect (toPerfect p) ≡ p
  Perfect-iso₂ {n = zero} {Inₛ (In tt , snd)} =
    cong (λ x → Inₛ ((In tt) , x)) (funext' λ { {In ()} })
  Perfect-iso₂ {n = suc n} {Inₛ (In v , snd)} =
    cong (λ x → Inₛ ((In v) , x)) ( funext' λ {
        {In (inj₁ tt)} → Perfect-iso₂
      ; {In (inj₂ tt)} → Perfect-iso₂
      })

  Perfect≅Σ-Perfect : ∀ {a : Set} {n : ℕ} → Perfect a n ≅ Fixₛ (Σ-Perfect {a}) n
  Perfect≅Σ-Perfect =
    record { from = fromPerfect
           ; to   = toPerfect
           ; iso₁ = Perfect-iso₁
           ; iso₂ = Perfect-iso₂
           }

  instance
    Perfect-MultiSorted : ∀ {a : Set} → MultiSorted (Perfect a)
    Perfect-MultiSorted {a} = record { Wᵢ = Σ-Perfect {a} , Perfect≅Σ-Perfect }
