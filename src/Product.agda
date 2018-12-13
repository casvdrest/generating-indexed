open import Size

open import Codata.Colist
open import Codata.Thunk hiding (map)

open import Data.List hiding (concat; [_]; zipWith; map)

open import src.Nonempty
open import src.Data

module src.Product where

  concat : ∀ {a : Set} {i : Size}
           → (xs : Colist (List₊ a) i)
           → Colist a i
  concat [] = []
  concat ([ x ] ∷ xss) =
    x ∷ λ where .force → concat (xss .force)
  concat ((x ∷ xs) ∷ xss) =
    x ∷ λ where .force → concat (xs ∷ xss)

  stripe₁ : ∀ {a : Set} {i j : Size}  
             → List₊ (Colist₊ a ∞)
             → List₊ a ⊗ List₊ (Colist a j)
  stripe₁ [ [ x ] ] = [ x ] , [ [] ]
  stripe₁ [ x ∷ xs ] = [ x ] , [ toColist (xs .force) ]
  stripe₁ (x ∷ xs) with stripe₁ xs 
  ... | ys , rs = (head₊ x ∷ ys) , (tail₊ x ∷ rs)

  filterEmpty : ∀ {a : Set} {i : Size} {j : Size< i}
                → List₊ (Colist a i)
                → List (Colist₊ a j)
  filterEmpty [ [] ] = []
  filterEmpty [ x ∷ xss ] = toColist₊ x (xss .force) ∷ []
  filterEmpty ([] ∷ xss) = filterEmpty xss
  filterEmpty ((x ∷ xs) ∷ xss) = toColist₊ x (xs .force) ∷ filterEmpty xss

  stripe : ∀ {a : Set} {i j : Size} 
            → List₊ (Colist₊ a ∞)
            → Colist (Colist₊ a ∞) ∞
            → Colist₊ (List₊ a) i
  stripe xs zs with stripe₁ xs 
  stripe xs zs | ys , rs with filterEmpty rs
  stripe xs [] | ys , rs | [] = [ ys ]
  stripe xs (z ∷ zs) | ys , rs | [] =
    ys ∷ λ where .force → stripe [ z ] (zs . force)
  stripe xs [] | ys , rs | x ∷ xss =
    ys ∷ λ where .force → stripe (toList₊ x xss) []
  stripe xs (z ∷ zs) | ys , rs | x ∷ xss =
    ys ∷ λ where .force → stripe (toList₊ z (x ∷ xss)) (zs .force)
  
  diagonal : ∀ {a : Set} → Colist (Colist₊ a ∞) ∞ → Colist a ∞
  diagonal [] = []
  diagonal (xs ∷ xss) = concat (toColist (stripe [ xs ] (xss .force)))

  multiply : ∀ {a b : Set} {i j : Size} 
             → Colist a i → Colist₊ b j
             → Colist (Colist₊ (a ⊗ b) j ) i
  multiply []       _  = []
  multiply (x ∷ xs) ys =
    zipWith₊ _,_ (repeat₊ x) ys ∷ λ where .force → multiply (xs .force) ys

  -- Cartesian product of colists
  _×_ : ∀ {a b : Set} → Colist a ∞ → Colist b ∞ → Colist (a ⊗ b) ∞
  xs × [] = []
  xs × (y ∷ ys) = diagonal (multiply xs (toColist₊ y (ys .force)))

  _⊛_ : ∀ {a b : Set} → Colist (a → b) ∞ → Colist a ∞ → Colist b ∞
  fs ⊛ xs = map (λ p → (fst p) (snd p)) (fs × xs)
