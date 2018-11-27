
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Bool

module Generic where 

  indexed : Set → Set₁
  indexed I = I → Set

  _▷_ : Set → Set → Set₁ 
  I ▷ O = indexed I → indexed O

  record _≃_ (A B : Set) : Set where
    field
      from : A → B
      to   : B → A
      iso₁ : ∀ {x : A} → to (from x) ≡ x
      iso₂ : ∀ {x : B} → from (to x) ≡ x

  data _+_ : Set → Set → Set where
    inl : ∀ {A B : Set} → A → A + B
    inr : ∀ {A B : Set} → B → A + B

  data _×_ : Set → Set → Set where
    _,_ : ∀ {A B : Set} → A → B → A × B

  _∘_ : ∀ {A B C : Set₁} → (B → C) → (A → B) → A → C
  g ∘ f = λ x → g (f x)

  _∣_ : ∀ {I J} → indexed I → indexed J → indexed (I + J)
  (l ∣ r) (inl x) = l x
  (l ∣ r) (inr x) = r x

  mutual
    data _▶_ : Set → Set → Set₁ where 
      Z : ∀ {I O : Set} → I ▶ O
      U : ∀ {I O : Set} → I ▶ O
      I : ∀ {I O : Set} → I → I ▶ O
      _⊗_ : ∀ {I O : Set} → I ▶ O → I ▶ O → I ▶ O
      _⊕_ : ∀ {I O : Set} → I ▶ O → I ▶ O → I ▶ O
      _⊚_ : ∀ {I M O : Set} → M ▶ O → I ▶ M → I ▶ O
      Iso : ∀ {I O} → (C : I ▶ O) → (D : I ▷ O) →
                      ((r : indexed I) → (o : O) → D r o ≃ ⟦ C ⟧ r o) → I ▶ O
      Fix : ∀ {I O} → (I + O) ▶ O → I ▶ O

    
    data μ {I O : Set} (F : (I + O) ▶ O) (r : indexed I) (o : O) : Set where
      ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

    ⟦_⟧ : ∀ {I O : Set} → I ▶ O → I ▷ O
    ⟦ Z ⟧ r o = ⊥
    ⟦ U ⟧ r o = ⊤
    ⟦ I i ⟧ r o = r i 
    ⟦ F ⊕ G ⟧ r o = ⟦ F ⟧ r o + ⟦ G ⟧ r o
    ⟦ F ⊗ G ⟧ r o = ⟦ F ⟧ r o × ⟦ G ⟧ r o
    ⟦ F ⊚ G ⟧ r o = (⟦ F ⟧ ∘ ⟦ G ⟧ ) r o
    ⟦ Iso C D e ⟧ r o = D r o
    ⟦ Fix F ⟧ r o = μ F r o

  infix 3 _≃_

  BoolF : ⊥ ▶ ⊤
  BoolF = U ⊕ U

  fromBool : ∀ {r o} → Bool → ⟦ BoolF ⟧ r o
  fromBool false = inr tt
  fromBool true = inl tt

  toBool : ∀ {r o} → ⟦ BoolF ⟧ r o → Bool
  toBool (inl x) = true
  toBool (inr x) = false

  isoBool₁ : ∀ {b r o} → toBool {r} {o} (fromBool {r} {o} b) ≡ b
  isoBool₁ {true}  = refl
  isoBool₁ {false} = refl

  isoBool₂ : ∀ {b r o} → fromBool {r} {o} (toBool {r} {o} b) ≡ b
  isoBool₂ {inl x} = refl
  isoBool₂ {inr x} = refl
  
  isoBool : (r : indexed ⊥) (o : ⊤) → Bool ≃ ⟦ BoolF ⟧ r o
  isoBool r o = record { from = fromBool {r} {o} 
                       ; to   = toBool {r} {o} 
                       ; iso₁ = isoBool₁
                       ; iso₂ = isoBool₂
                       }

  Bool' : ⊥ ▶ ⊤
  Bool' = Iso BoolF (λ _ _ → Bool) isoBool
  
  data Maybe (A : Set) : Set where
    Just : A → Maybe A
    Nothing : Maybe A

  MaybeF : ⊤ ▶ ⊤
  MaybeF = I tt ⊕ U

  fromMaybe : ∀ {r o} → Maybe (r o) → ⟦ MaybeF ⟧ r o
  fromMaybe (Just x) = inl x
  fromMaybe Nothing = inr tt

  toMaybe : ∀ {r o} → ⟦ MaybeF ⟧ r o → Maybe (r o)
  toMaybe (inl x) = Just x
  toMaybe (inr x) = Nothing

  isoMaybe₁ : ∀ {r o m} → toMaybe {r} {o} (fromMaybe m) ≡ m
  isoMaybe₁ {m = Just x} = refl
  isoMaybe₁ {m = Nothing} = refl

  isoMaybe₂ : ∀ {r o m} → fromMaybe {r} {o} (toMaybe m) ≡ m
  isoMaybe₂ {m = inl x} = refl
  isoMaybe₂ {m = inr x} = refl

  isoMaybe : (r : indexed ⊤) (o : ⊤) → Maybe (r o) ≃ ⟦ MaybeF ⟧ r o
  isoMaybe r o = record { from = fromMaybe
                        ; to   = toMaybe
                        ; iso₁ = isoMaybe₁
                        ; iso₂ = isoMaybe₂
                        }

  Maybe' : ⊤ ▶ ⊤
  Maybe' = Iso MaybeF (λ r o → Maybe (r o)) isoMaybe

  infixr 6 _∷_

  data [_] (A : Set) : Set where
    []  : [ A ]
    _∷_ : A → [ A ] → [ A ]

  listF : (⊤ + ⊤) ▶ ⊤
  listF = U ⊕ ((I (inl tt) ⊗ I (inr tt) ))

  fromList : ∀ {r o} → [ r o ] → ⟦ Fix listF ⟧ r o
  fromList [] = ⟨ inl tt ⟩
  fromList (x ∷ xs) = ⟨ inr (x , fromList xs) ⟩

  toList : ∀ {r o} → ⟦ Fix listF ⟧ r o → [ r o ]
  toList ⟨ inl x ⟩ = []
  toList ⟨ inr (x , xs) ⟩ = x ∷ (toList xs)

  isoList₁ : ∀ {r o l} → toList {r} {o} (fromList l) ≡ l
  isoList₁ {l = []} = refl
  isoList₁ {l = (x ∷ xs)} = cong (λ h → x ∷ h) isoList₁

  isoList₂ : ∀ {r o l} → fromList {r} {o} (toList l) ≡ l
  isoList₂ {l = ⟨ inl tt ⟩} = refl
  isoList₂ {l = ⟨ inr (x , xs) ⟩} = cong (λ h → ⟨ inr (x , h) ⟩) isoList₂

  isoList : (r : indexed ⊤) (o : ⊤) → [ r o ] ≃ ⟦ Fix listF ⟧ r o
  isoList r o = record { from = fromList
                       ; to   = toList
                       ; iso₁ = isoList₁
                       ; iso₂ = isoList₂
                       }

  List' : ⊤ ▶ ⊤
  List' = Iso (Fix listF) (λ r o → [ r o ]) isoList

  _⇉_ : ∀ {I} → indexed I → indexed I → Set
  r ⇉ s = ∀ i → r i → s i 
  
  
  
