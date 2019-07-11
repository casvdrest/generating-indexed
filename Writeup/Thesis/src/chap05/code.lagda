\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
  
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Data.Sum

open import AgdaGen.Base hiding (Call) renaming (Gen to GenBase ; μ to μBase) 
open import AgdaGen.Combinators

open import Function

open import Relation.Binary.PropositionalEquality

record _≃_ (a : Set) (b : Set) : Set where
  field
    from  : a → b
    to    : b → a
    iso₁  : ∀ {x} → to (from x) ≡ x
    iso₂  : ∀ {y} → from (to y) ≡ y

Gen : Set → Set → Set
Gen A T = GenBase A (λ { tt → T }) tt

μ : ∀ {A} → Gen A A
μ = μBase tt

open import Data.Nat
open import Data.List


\end{code}

\begin{code}
Call : ∀ {a t : Set} → Gen a a → Gen a t
Call = λ _ → None 
\end{code}

%<*regular>
\begin{code}
data Reg : Set where
  Z    : Reg
  U    : Reg
  _⊕_  : Reg → Reg → Reg
  _⊗_  : Reg → Reg → Reg
  I    : Reg
  K    : Set → Reg
\end{code}
%</regular>

%<*regularsemantics>
\begin{code}
⟦_⟧ : Reg → Set → Set
⟦ Z        ⟧ r = ⊥
⟦ U        ⟧ r = ⊤
⟦ c₁ ⊕ c₂  ⟧ r = ⟦ c₁ ⟧ r ⊎ ⟦ c₂ ⟧ r
⟦ c₁ ⊗ c₂  ⟧ r = ⟦ c₁ ⟧ r × ⟦ c₂ ⟧ r
⟦ I        ⟧ r = r
⟦ K s      ⟧ r = s
\end{code}
%</regularsemantics>

%<*regularfix>
\begin{code}
data Fix (c : Reg) : Set where
  In : ⟦ c ⟧ (Fix c) → Fix c
\end{code}
%</regularfix>

%<*natregular>
\begin{code}
ℕ' : Set
ℕ' = Fix (U ⊕ I)
\end{code}
%</natregular>

%<*natiso> 
\begin{code}
fromℕ   : ℕ → ℕ'
toℕ     : ℕ' → ℕ
ℕ-iso₁  : ∀ {n} → toℕ (fromℕ n) ≡ n
ℕ-iso₂  : ∀ {n} → fromℕ (toℕ n) ≡ n

ℕ≃ℕ' : ℕ ≃ ℕ'
ℕ≃ℕ' = record { from = fromℕ ; to = toℕ ; iso₁ = ℕ-iso₁ ; iso₂ = ℕ-iso₂ }
\end{code}
%</natiso>

\begin{code}
fromℕ zero     = In (inj₁ tt)
fromℕ (suc n)  = In (inj₂ (fromℕ n))

toℕ (In (inj₁ tt))  = zero
toℕ (In (inj₂ y))   = suc (toℕ y)

ℕ-iso₁ {zero}   = refl
ℕ-iso₁ {suc n}  = cong suc ℕ-iso₁

ℕ-iso₂ {In (inj₁ tt)}  = refl
ℕ-iso₂ {In (inj₂ y)}   = cong (In ∘ inj₂) ℕ-iso₂
\end{code}

%<*regularrecord>
\begin{code}
record Regular (a : Set) : Set where
    field
      code : Reg
      iso  : a ≃ Fix code
\end{code}
%</regularrecord>

\begin{code}
module A where 
\end{code}

%<*genericgen>
\begin{code}
  deriveGen : (c : Reg) → Gen (Fix c) (Fix c)
\end{code}
%</genericgen>

\begin{code}
  deriveGen = λ c → None

module B where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
\end{code}

%<*genericgen2>
\begin{code}
  deriveGen :  (c c' : Reg)
            →  Gen (⟦ c ⟧ (Fix c')) (⟦ c' ⟧ (Fix c'))
\end{code}
 %</genericgen2>

%<*genericgenZU>
\begin{code}
  deriveGen Z c' = empty
  deriveGen U c' = pure tt
\end{code}
%</genericgenZU>μ

%<*genericgenI>
\begin{code}
  deriveGen I c' = ⦇ In μ ⦈
\end{code}
%</genericgenI>

%<*genericgenPCOP>
\begin{code}
  deriveGen (c₁ ⊕ c₂) c' =
    ⦇ inj₁ (deriveGen c₁ c') ⦈ ∥ ⦇ inj₂ (deriveGen c₂ c') ⦈
    
  deriveGen (c₁ ⊗ c₂) c' =
    ⦇ deriveGen c₁ c' , deriveGen c₂ c' ⦈
\end{code}
%</genericgenPCOP>

\begin{code}
  deriveGen (K s) c' = None
\end{code}

%<*genericgenFinal>
\begin{code}
  genericGen : (c : Reg) → Gen (Fix c) (Fix c)
  genericGen c = ⦇ In (Call (deriveGen c c)) ⦈
\end{code}
%</genericgenFinal>

%<*genericgenNat>
\begin{code}
  genℕ : Gen ℕ ℕ
  genℕ = ⦇ (_≃_.to ℕ≃ℕ') (Call (genericGen (U ⊕ I))) ⦈
\end{code}
%</genericgenNat>

%<*isogen>
\begin{code}
  isoGen : ∀ {A} ⦃ p : Regular A ⦄ → Gen A A
  isoGen ⦃ p = record { code = c ; iso =  iso } ⦄ =
    ⦇ (_≃_.to iso ∘ In) (Call (deriveGen c c)) ⦈ 
\end{code}
%</isogen>

%<*natlist>
\begin{code}
  listℕ : Set
  listℕ = Fix (U ⊕ ((U ⊗ I) ⊗ I)) 
\end{code}
%</natlist>

%<*natlist2>
\begin{code}
listℕ : Set
listℕ = Fix (U ⊕ (K (Fix (U ⊕ I)) ⊗ I)) 
\end{code}
%</natlist2>

\begin{code}
module C where
\end{code}

%<*mdstructure>
\begin{code}
  data KInfo (P : Set → Set) : Reg → Set where
    Z~    : KInfo P Z
    U~    : KInfo P U
    _⊕~_  : ∀ {cₗ cᵣ} → KInfo P cₗ → KInfo P cᵣ
                      → KInfo P (cₗ ⊕ cᵣ)
    _⊗~_  : ∀ {cₗ cᵣ} → KInfo P cₗ → KInfo P cᵣ
                      → KInfo P (cₗ ⊗ cᵣ)
    I~    : KInfo P I
    K~    : ∀ {S} → P S → KInfo P (K S) 
\end{code}
%</mdstructure>

%<*derivegenKTy>
\begin{code}
  deriveGen  : (c c' : Reg) → KInfo (λ S → Gen S S) c
             → Gen (⟦ c ⟧ (Fix c')) (⟦ c' ⟧ (Fix c'))
\end{code}
%</derivegenKTy>

%<*derivegenKCase>
\begin{code}
  deriveGen (K x) c' (K~ g) = Call g
\end{code}
%</derivegenKCase>



\begin{code}
  deriveGen c c' info = None

open import Data.Sum
open import AgdaGen.Data using (_∈_; here ; there ; merge)
open import AgdaGen.Enumerate renaming (enumerate to toList')

toList : ∀ {A T} → Gen A T → Gen T T → ℕ → List A
toList g tg n = toList' (λ { tt → tg }) tt g n

\end{code}
\begin{code}
open import AgdaGen.Data using (_∈_)
\end{code}

%<*isogenproven>
\begin{code}
isoGen :  ∀ {A}  → ⦃ p : Regular A ⦄
          → Σ[ g ∈ Gen A A ] ∀ {x} → ∃[ n ] (x ∈ toList g g n)
\end{code}
%</isogenproven>
\begin{code}

isoGen = {!!}

open B using (genericGen)
\end{code}

%<*genericgencomplete>
\begin{code}
genericGen-Complete :
  ∀ {c x} → ∃[ n ] (x ∈ toList (genericGen c) (genericGen c) n)
\end{code}
%</genericgencomplete>

\begin{code}
genericGen-Complete = {!!}

module E where
  open B
\end{code}

%<*derivegencomplete>
\begin{code}
  deriveGen-Complete : ∀ {c c' x}
    → ∃[ n ] (x ∈ toList (deriveGen c c') (deriveGen c' c') n)
\end{code}
%</derivegencomplete>

%<*derivegencompleteZU>
\begin{code}
  deriveGen-Complete {Z} {c'} {()}
  deriveGen-Complete {U} {c'} {tt}      = 1 , here
\end{code}
%</derivegencompleteZU> 

\begin{code}
  deriveGen-Complete {cₗ ⊕ cᵣ} {c'} {x} = {!!}
  deriveGen-Complete {cₗ ⊗ cᵣ} {c'} {x} = {!!}
\end{code}

%<*derivegencompleteI>
\begin{code}
  deriveGen-Complete {I} {c'} {In x}
    with deriveGen-Complete {c'} {c'} {x}
  ... | prf = {!!}
\end{code}
%</derivegencompleteI>

\begin{code}
  deriveGen-Complete {K x₁} {c'} {x} = {!!}

  enumerate : ∀ {A T} →  Gen A T → (Gen T T) → ℕ → List A
  enumerate = {!!}

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
\end{code}


%<*derivegencompleteIlemma>
\begin{code}
  lemma-In : ∀ {x g g'}
    → ∃[ n ] (x ∈ enumerate g g' n)
    → ∃[ n ] (In x ∈ enumerate (⦇ In x ⦈) g' n)
\end{code}
%</derivegencompleteIlemma>


\begin{code}
  lemma-In = {!!}

module D where
  open B
       
  open import Relation.Binary.HeterogeneousEquality
  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  open import Data.List
  eq : ∀ {cₗ cᵣ c' n} →
\end{code}

%<*tolistcopeq>
\begin{code}
    toList (deriveGen (cₗ ⊕ cᵣ) c') (deriveGen c' c') n
      ≡ merge (toList ⦇ inj₁ (deriveGen cₗ c') ⦈ (deriveGen c' c') n)
              (toList ⦇ inj₂ (deriveGen cᵣ c') ⦈ (deriveGen c' c') n)
\end{code}
%</tolistcopeq>

%<*mergecomplete>
\begin{code}
  merge-complete-left   : ∀ {A} {xsₗ xsᵣ : List A} {x : A}
    → x ∈ xsₗ → x ∈ merge xsₗ xsᵣ
    
  merge-complete-right  : ∀ {A} {xsₗ xsᵣ : List A} {x : A}
    → x ∈ xsᵣ → x ∈ merge xsₗ xsᵣ 
\end{code}
%</mergecomplete>

\begin{code}
  merge-complete-left = {!!}
  merge-complete-right = {!!}
  eq = {!!}

open import Data.List

pure : ∀ {A} → A → List A
pure x = x ∷ []

_<*>_ : ∀ {A B} → List (A → B) → List A → List B
fs <*> xs = concatMap (λ f → Data.List.map f xs) fs

module Foo where
  open B

  eq2 : ∀ {cₗ cᵣ c' n} →
\end{code}

%<*tolistpeq>
\begin{code}
    toList (deriveGen (cₗ ⊗ cᵣ) c') (deriveGen c' c') n
      ≡ ⦇ (toList (deriveGen cₗ c') (deriveGen c' c') n)
        , (toList (deriveGen cᵣ c') (deriveGen c' c') n) ⦈
\end{code}
%</tolistpeq>

\begin{code}
  eq2 = {!!}
\end{code}

%<*apcomplete>
\begin{code}
×-complete  : ∀ {A B} {x : A} {y : B} {xs ys}
            → x ∈ xs → y ∈ ys → (x , y) ∈ ⦇ xs , ys ⦈ 
\end{code}
%</apcomplete>

\begin{code}
×-complete = {!!}

open C
\end{code}

%<*kinfomap>
\begin{code}
KInfo-map : ∀ {c P Q}  → (∀ {s} → P s → Q s)
                       → KInfo P c → KInfo Q c
KInfo-map f (K~ x) = K~ (f x)
\end{code}
%</kinfomap>

\begin{code}
KInfo-map f Z~ = Z~
KInfo-map f U~ = U~
KInfo-map f (iₗ ⊕~ iᵣ) = KInfo-map f iₗ ⊕~ KInfo-map f iᵣ
KInfo-map f (iₗ ⊗~ iᵣ) = KInfo-map f iₗ ⊗~ KInfo-map f iᵣ
KInfo-map f I~ = I~
\end{code}

\begin{code}
module F where

  open C
\end{code}

%<*proofinfotype>
\begin{code}
  ProofMD : Reg → Set
  ProofMD c = KInfo  (λ S → Σ[ g ∈ Gen S S ]
                     (∀ {x} → ∃[ n ] (x ∈ toList g g n))) c
\end{code}
%</proofinfotype>

%<*mdtransform>
\begin{code}
  ◂_  : ∀ {c : Reg}  → KInfo (λ A → Σ[ g ∈ Gen A A ]
                               (∀ {x} → ∃[ n ] (x ∈ toList g g n))) c
                     → KInfo (λ A → Gen A A) c
  ◂ m = KInfo-map proj₁ m
\end{code}
%</mdtransform>

%<*derivegenwithmd>
\begin{code}
  deriveGen-Complete : (c c' : Reg)
    → (i : ProofMD c) → (i' : ProofMD c')
    → ∀ {x} → ∃[ n ] (x ∈ toList  (deriveGen c c' (◂ i))
                                  (deriveGen c' c' (◂ i')) n)
\end{code}
%</derivegenwithmd>

\begin{code}
  deriveGen-Complete = {!!}

open F

monotone : ∀ {n m : ℕ} {c c' : Reg} {x : ⟦ c ⟧ (Fix c')} {i i'} →
\end{code}

%<*derivegenmonotone>
\begin{code}
  n ≤ m  → x ∈ toList  (C.deriveGen c c' (◂ i))
                       (C.deriveGen c' c' (◂ i')) n
         → x ∈ toList  (C.deriveGen c c' (◂ i))
                       (C.deriveGen c' c' (◂ i')) m
\end{code}
%</derivegenmonotone>

\begin{code}
monotone = {!!}
\end{code}

%<*defrose>
\begin{code}
data Rose (A : Set) : Set where
  node : List (Rose A) → Rose A
\end{code}
%</defrose>
