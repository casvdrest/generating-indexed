{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base renaming (μ to μB)
open import AgdaGen.Combinators
open import AgdaGen.Enumerate hiding (⟨_⟩)
open import AgdaGen.Examples.Regex

open import AgdaGen.Generic.Isomorphism
open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Generator

open import Data.Unit
open import Data.Product
open import Data.List

open import Relation.Binary.PropositionalEquality

open import Level renaming (suc to sucL ; zero to zeroL)

module AgdaGen.Generic.Indexed.IDesc.Regex where

  -- Descibes regular rexpressions as an
  -- indexed description
  rD : func zeroL Regex Regex
  rD = func.mk λ
    { (`c x) → `1
    ; zero → `σ 0 λ ()
    ; one → `1
    ; (r `+ r') →
        `σ 2 λ 
          { ∙     → `var r
          ; (▻ ∙) → `var r' 
          }
    ; (r `∙ r') → `var r `× `var r' 
    ; (r *) →
        `σ 2 λ
          { ∙     → `var r `× `var (r *)
          ; (▻ ∙) → `1
          }
    }

  -- From regular expression to description fixed point
  fromR : ∀ {r : Regex} → ∈ᵣ r → μ rD r
  fromR {.(`c _)} [Char] = ⟨ lift tt ⟩
  fromR {.one} [One] = ⟨ lift tt ⟩
  fromR {(r `+ r')} ([Left] ir) = ⟨ ∙ , fromR {r = r} ir ⟩
  fromR {(r `+ r')} ([Right] ir) = ⟨ (▻ ∙ , fromR {r = r'} ir) ⟩
  fromR {(r `∙ r')} ([Seq] ir ir') = ⟨ (fromR ir , fromR ir') ⟩
  fromR {(r *)} ([Step] ir ir') = ⟨ (∙ , (fromR ir) , (fromR ir')) ⟩
  fromR {(r *)} [Stop] = ⟨ ▻ ∙ , lift tt ⟩

  -- From description fixed point to regular expression
  toR : ∀ {r : Regex} → μ rD r → ∈ᵣ r
  toR {`c x₁} ⟨ lift tt ⟩ = [Char]
  toR {zero} ⟨ () , snd ⟩
  toR {one} ⟨ lift tt ⟩ = [One]
  toR {r `+ r'} ⟨ ∙ , snd ⟩ = [Left] (toR snd)
  toR {r `+ r'} ⟨ ▻ ∙ , snd ⟩ = [Right] (toR snd)
  toR {r `∙ r₁} ⟨ fst , snd ⟩ = [Seq] (toR fst) (toR snd)
  toR {r *} ⟨ ∙ , fst , snd ⟩ = [Step] (toR fst) (toR snd)
  toR {r *} ⟨ ▻ ∙ , snd ⟩ = [Stop]

  -- to ∘ from ≡ id
  r-iso₁ : ∀ {r : Regex} {p : ∈ᵣ r} → toR (fromR p) ≡ p
  r-iso₁ {p = [Char]} = refl
  r-iso₁ {p = [One]} = refl
  r-iso₁ {p = [Left] p} = cong [Left] r-iso₁
  r-iso₁ {p = [Right] p} = cong [Right] r-iso₁
  r-iso₁ {p = [Seq] p p₁} = cong₂ [Seq] r-iso₁ r-iso₁
  r-iso₁ {p = [Step] p p₁} = cong₂ [Step] r-iso₁ r-iso₁
  r-iso₁ {p = [Stop]} = refl

  -- from ∘ to ≡ id
  r-iso₂ : ∀ {r : Regex} {p : μ rD r} → fromR (toR p) ≡ p
  r-iso₂ {`c x} {⟨ lift tt ⟩} = refl
  r-iso₂ {zero} {⟨ () , snd ⟩}
  r-iso₂ {one} {⟨ lift tt ⟩} = refl
  r-iso₂ {r `+ r₁} {⟨ ∙ , snd ⟩} = cong (λ x → ⟨ (∙ , x) ⟩) r-iso₂
  r-iso₂ {r `+ r₁} {⟨ ▻ ∙ , snd ⟩} = cong (λ x → ⟨ (▻ ∙ , x) ⟩) r-iso₂
  r-iso₂ {r `∙ r₁} {⟨ fst , snd ⟩} = cong₂ (λ x x₁ → ⟨ (x , x₁) ⟩) r-iso₂ r-iso₂
  r-iso₂ {r *} {⟨ ∙ , (a , b) ⟩} = cong₂ (λ x x₁ → ⟨ (∙ , x , x₁) ⟩) r-iso₂ r-iso₂
  r-iso₂ {r *} {⟨ ▻ ∙ , lift tt ⟩} = refl

  -- Convert a regular expression proof to a string
  r→String : ∀ {r : Regex} → ∈ᵣ r → String
  r→String {r = `c c} [Char] = c ∷ []
  r→String [One] = []
  r→String ([Left] p) = r→String p
  r→String ([Right] p) = r→String p
  r→String ([Seq] p p₁) = r→String p ++ r→String p₁
  r→String ([Step] p p₁) = r→String p ++ r→String p₁
  r→String [Stop] = []

  -- regular expressions can be described using an indexed description
  instance
    r≅IDesc : ≅IDesc ∈ᵣ
    r≅IDesc = record { W = rD , ≅-transitive (≅-symmetric ≅lift) record { from = fromR ; to = toR ; iso₁ = r-iso₁ ; iso₂ = r-iso₂ } }

  -- Example regular expression: '(a+b)*'
  r1 : Regex
  r1 = (`c 'a' `+ `c 'b') *

  -- Metadata description for regular expressions (there are no sigmas,
  -- so we don't need to supply any actual generators). 
  rDM : (r : Regex) → IDescM 𝔾 (func.out rD r)
  rDM (`c x) = `1~
  rDM zero = `σ~ (λ ())
  rDM one = `1~
  rDM (r `+ r₁) = `σ~ (λ { ∙ → `var~ ; (▻ ∙) → `var~ })
  rDM (r `∙ r₁) = `var~ `×~ `var~
  rDM (r *) = `σ~ (λ { ∙ → `var~ `×~ `var~ ; (▻ ∙) → `1~ })

  -- Enumeration of '(a+b)*'
  test : Data.List.map (λ { (lift x) → r→String x }) (⟨ (λ x → IDesc-isoGen x rDM) ⟩ᵢ r1 5) ≡
    [] ∷ ('b' ∷ []) ∷ ('b' ∷ 'b' ∷ []) ∷ ('b' ∷ ('b' ∷ 'b' ∷ [])) ∷ ('b' ∷ 'b' ∷ 'a' ∷ []) ∷
    ('b' ∷ 'a' ∷ []) ∷ ('b' ∷ 'a' ∷ 'b' ∷ []) ∷ ('b' ∷ 'a' ∷ 'a' ∷ []) ∷ ('a' ∷ []) ∷
    ('a' ∷ 'b' ∷ []) ∷ ('a' ∷ 'b' ∷ 'b' ∷ []) ∷ ('a' ∷ 'b' ∷ 'a' ∷ []) ∷ ('a' ∷ 'a' ∷ []) ∷
    ('a' ∷ 'a' ∷ 'b' ∷ []) ∷ ('a' ∷ 'a' ∷ 'a' ∷ []) ∷ []
  test = refl
  
