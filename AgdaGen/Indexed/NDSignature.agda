import Level as L

open import Data.Nat hiding (_≤_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List hiding (lookup)
open import Data.Unit hiding (_≤_)
open import Data.Vec
open import Data.Fin using (Fin; suc; zero)

open import AgdaGen.Regular.Generic
open import AgdaGen.Data using (_∈_; here; there)
open import AgdaGen.Indexed.Isomorphism
open import AgdaGen.Regular.Isomorphism
open import AgdaGen.Indexed.Lambda

open import Relation.Binary.PropositionalEquality hiding (cong₂)
open import Relation.Nullary

open import Function

module AgdaGen.Indexed.NDSignature where

  data SizedTree : ℕ → Set where 
    Leaf : SizedTree 0
    Node : ∀ {n m : ℕ} → SizedTree n → SizedTree m → SizedTree (suc (n + m))

  data SizedTree' : ℕ → Set where
    Leaf' : SizedTree' 1
    Node' : ∀ {n m : ℕ} → SizedTree' (suc n) → SizedTree' (suc m) → SizedTree' (suc (suc (n + m)))

  Invertible : ∀ {ℓ} {a b : Set ℓ} {n : ℕ} (f : Vec a n → b) → Set ℓ
  Invertible {_} {a} {b} {n} f = (y : b) → List (Σ[ args ∈ Vec a n ] f args ≡ y)

  Inversion : ∀ {ℓ} {a b : Set ℓ} {n : ℕ} → (f : Vec a n → b) → b → Set ℓ
  Inversion {_} {a} {b} {n} f y = Σ[ args ∈ Vec a n ] f args ≡ y

  record NDSig {ℓ} (i : Set ℓ) : Set (L.suc ℓ) where
    constructor _◂_∣_
    field
      Opₙ : i → Reg
      Arₙ : ∀ {x} → Fix (Opₙ x) → ℕ
      Ivₙ : ∀ {x} {op : Fix (Opₙ x)} → Σ[ f ∈ (Vec i (Arₙ op) → i) ] Invertible f

  
  ⟦_⟧ₙ : ∀ {i : Set} → (Σ : NDSig i) → (x : i → Set) → i → Set
  ⟦_⟧ₙ {i} (Opₙ ◂ Arₙ ∣ Ivₙ) r =  λ ix → Σ[ op ∈ Fix (Opₙ ix) ]
    Σ[ inv ∈ Inversion (proj₁ (Ivₙ {ix} {op})) ix ] ((fn : Fin (Arₙ op)) → r (lookup fn (proj₁ inv)))
  
  data Fixₙ {i : Set} (Σ : NDSig i) (x : i) : Set where
    Inₙ : ⟦ Σ ⟧ₙ (Fixₙ Σ) x → Fixₙ Σ x  
  
  split+ : (n : ℕ) → List (Σ[ v ∈ Vec ℕ 2 ] lookup zero v + lookup (suc zero) v ≡ n)
  split+ zero = ((0 ∷ (0 ∷ [])) , refl) ∷ []
  split+ (suc n) = ((0 ∷ (suc n ∷ [])) , refl)
    ∷ Data.List.map (λ { ((n ∷ m ∷ []) , refl) → suc n ∷ m ∷ [] , refl }) (split+ n)

  index : ∀ {i : Set} {f : i → Set} {x : i} → f x → i
  index {x = x} _ = x

  Opₙ-Sized : ℕ → Reg
  Opₙ-Sized zero = U
  Opₙ-Sized (suc n) = U

  Arₙ-Sized : (n : ℕ) → Fix (Opₙ-Sized n) → ℕ
  Arₙ-Sized zero (In tt) = 0
  Arₙ-Sized (suc n) (In tt) = 2

  Ivₙ-Sized : (n : ℕ) → (op : Fix (Opₙ-Sized n))
            → Σ[ f ∈ (Vec ℕ (Arₙ-Sized n op) → ℕ) ] Invertible f
  Ivₙ-Sized zero (In tt) =
    const zero , λ { zero → ([] , refl) ∷ [] ; (suc x) → [] }
  Ivₙ-Sized (suc n) (In tt) =
     (λ { (l ∷ r ∷ []) → suc (l + r) })
    , λ { zero → []
        ; (suc y) → Data.List.map (λ { (l ∷ r ∷ [] , refl) → l ∷ r ∷ [] , refl
        }) (split+ y) }

  Σ-Sized : NDSig ℕ
  Σ-Sized =
    Opₙ-Sized ◂ (λ {n} → Arₙ-Sized n) ∣ λ {n} {op} → Ivₙ-Sized n op

  fromSized : ∀ {n : ℕ} → SizedTree n → Fixₙ Σ-Sized n
  fromSized {zero} Leaf = Inₙ (In tt , ([] , refl) , λ ())
  fromSized {suc n} (Node l r) =
    Inₙ ((In tt) , ( index {f = SizedTree} l ∷ index {f = SizedTree} r ∷ [] , refl)
      , λ { zero → fromSized l ; (suc zero) → fromSized r ; (suc (suc ())) }
    )
  
  toSized : ∀ {n : ℕ} → Fixₙ Σ-Sized n → SizedTree n
  toSized {zero} (Inₙ (In tt , ([] , refl) , snd)) = Leaf
  toSized {suc .(l + r)} (Inₙ (In tt , (l ∷ r ∷ [] , refl) , snd)) =
    Node (toSized (snd zero)) (toSized (snd (suc zero)))

  Sized-iso₁ : ∀ {n : ℕ} {t : SizedTree n} → toSized (fromSized t) ≡ t
  Sized-iso₁ {zero} {Leaf} = refl
  Sized-iso₁ {suc n} {Node l r} with Sized-iso₁ {t = l}
  ... | p₁ with Sized-iso₁ {t = r}
  ... | p₂ = cong₂ Node p₁ p₂

  Sized-iso₂ : ∀ {n : ℕ} {t : Fixₙ Σ-Sized n} → fromSized (toSized t) ≡ t
  Sized-iso₂ {zero} {Inₙ (In tt , ([] , refl) , snd)} =
    cong (λ x → Inₙ ((In tt) , ([] , refl) , λ fn → x fn)) (funext' λ { {()} })
  Sized-iso₂ {suc .(l + r)} {Inₙ (In tt , (l ∷ r ∷ [] , refl) , snd)} =
    cong (λ x → Inₙ ((In tt) , (((l ∷ r ∷ []) , refl) , x)))
      (funext' λ {
        {zero} → Sized-iso₂ {t = snd zero}
      ; {suc zero} → Sized-iso₂ {t = snd (suc zero)}
      ; {suc (suc ())} })

  Sized≅Σ-Sized : ∀ {n : ℕ} → SizedTree n ≅ Fixₙ Σ-Sized n
  Sized≅Σ-Sized =
    record { from = fromSized
           ; to   = toSized
           ; iso₁ = Sized-iso₁
           ; iso₂ = Sized-iso₂
           }

  data LEQ : (ℕ × ℕ) → Set where
    z≤s : ∀ {m : ℕ} → LEQ (0 , m)
    s≤s : ∀ {n m : ℕ} → LEQ (n , m) → LEQ (suc n , suc m)

  Opₙ-LEQ : ℕ × ℕ → Reg
  Opₙ-LEQ (zero  , m    ) = U
  Opₙ-LEQ (suc n , zero ) = Z
  Opₙ-LEQ (suc n , suc m) = U

  Arₙ-LEQ : (ix : ℕ × ℕ) → Fix (Opₙ-LEQ ix) → ℕ 
  Arₙ-LEQ (zero , m) (In tt) = 0
  Arₙ-LEQ (suc n , zero) (In ())
  Arₙ-LEQ (suc n , suc m) (In tt) = 1

  Ivₙ-LEQ : (ix : ℕ × ℕ) → (op : Fix (Opₙ-LEQ ix))
          → Σ[ f ∈ (Vec (ℕ × ℕ) (Arₙ-LEQ ix op) → ℕ × ℕ) ] Invertible f
  Ivₙ-LEQ (zero  , m    ) (In tt) =
    (λ { [] → zero , m }) , λ { (fst , snd) → [] }
  Ivₙ-LEQ (suc n , zero ) (In ())
  Ivₙ-LEQ (suc n , suc m) (In tt) =
     (λ { ((l , r) ∷ []) → suc l , suc r })
    , λ { (zero , m) → []
        ; (suc n , zero) → []
        ; (suc n , suc m) → ((n , m) ∷ [] , refl) ∷ []
        }
  
  Σ-LEQ : NDSig (ℕ × ℕ)
  Σ-LEQ = Opₙ-LEQ ◂ (λ {ix} → Arₙ-LEQ ix) ∣ λ {ix} {op} → Ivₙ-LEQ ix op

  fromLEQ : ∀ {ix : ℕ × ℕ} → LEQ ix → Fixₙ Σ-LEQ ix
  fromLEQ z≤s = Inₙ (In tt , ([] , refl) , λ ())
  fromLEQ (s≤s leq) =
      Inₙ ((In tt) , (((proj₁ (index {f = LEQ} leq)
    , proj₂ (index {f = LEQ} leq)) ∷ []) , refl)
    , λ { zero → fromLEQ leq ; (suc ()) })

  toLEQ : ∀ {ix : ℕ × ℕ} → Fixₙ Σ-LEQ ix → LEQ ix
  toLEQ {zero  , m    } (Inₙ (In tt , snd)) = z≤s
  toLEQ {suc n , zero } (Inₙ (In () , snd))
  toLEQ {suc n , suc m} (Inₙ (In tt , ((.n , .m) ∷ [] , refl) , snd)) =
    s≤s (toLEQ (snd zero))

  LEQ-iso₁ : ∀ {ix : ℕ × ℕ} {leq : LEQ ix} → toLEQ (fromLEQ leq) ≡ leq
  LEQ-iso₁ {zero  , m    } {z≤s}     = refl
  LEQ-iso₁ {suc n , zero } {()}
  LEQ-iso₁ {suc n , suc m} {s≤s leq} = cong s≤s LEQ-iso₁

  LEQ-iso₂ : ∀ {ix : ℕ × ℕ} {leq : Fixₙ Σ-LEQ ix} → fromLEQ (toLEQ leq) ≡ leq
  LEQ-iso₂ {zero , m} {Inₙ (In tt , ([] , refl) , snd)} =
    cong (λ x → Inₙ ((In tt) , ([] , refl) , x)) (funext' λ { {()} })
  LEQ-iso₂ {suc n , zero } {Inₙ (In () , snd)}
  LEQ-iso₂ {suc n , suc m} {Inₙ (In tt , ((.n , .m) ∷ [] , refl) , snd)} =
    cong (λ x → Inₙ ((In tt) , ((((n , m) ∷ []) , refl) , x)))
         (funext' λ { {zero} → LEQ-iso₂ ; {suc ()} })

  LEQ≅Σ-LEQ : ∀ {ix : ℕ × ℕ} → LEQ ix ≅ Fixₙ Σ-LEQ ix
  LEQ≅Σ-LEQ =
    record { from = fromLEQ
           ; to   = toLEQ
           ; iso₁ = LEQ-iso₁
           ; iso₂ = LEQ-iso₂
           }
