%<*lambda> 
  data _⊢_ {A : Set} : (Γ : Ctx A) → (τ : Type A) → Set where

    [Var] : ∀ {Γ τ}
          → Γ ∋ τ
            -------
          → Γ ⊢ τ

    [Abs] : ∀ {Γ σ τ}
          → Γ , σ ⊢ τ
            -----------
          → Γ ⊢ σ `→ τ

    [App] : ∀ {Γ σ τ}
          → Γ ⊢ σ `→ τ
            --------------
          → Γ ⊢ σ → Γ ⊢ τ
\end{code}
%</lambda>