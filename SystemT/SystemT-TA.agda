-- From Andreas Abel's Habilitation thesis section 3

module SystemT-TA where
  open import Data.Nat

data tp : Set where
  nat : tp
  _⟼_ : tp -> tp -> tp

-- data var : Set where
--   top : var
--   pop : var -> var

data exp : Set where
  ▹ : ℕ -> exp -- De Bruijn indeces
  ƛ : exp -> exp
  _·_ : exp -> exp -> exp
  -- zero : exp
  -- succ : exp -> exp
  -- rec : exp -> exp -> exp -> exp

-- Sematics

mutual 
  data D : Set where
    ƛ : exp -> env -> D
    ne : Dne -> D

  data Dne : Set where
    _·_ : Dne -> D -> Dne
    ▹ : (x k : ℕ) -> Dne

  data env : Set where
    nil : env
    _,_ : env -> D -> env


-- lookup
data _[_]=_ : ℕ -> env -> D -> Set where
  l-top : ∀{ρ a} -> zero [ ρ , a ]= a
  l-pop : ∀{v ρ a b} ->  v [ ρ ]= a -> (suc v) [ ρ , b ]= a

-- evaluation relation

mutual
  data _·_↘_ : D -> D -> D -> Set where
    app-lam : ∀{t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> ƛ t ρ · a ↘ a
    app-neu : ∀{e d} -> (ne e) · d ↘ ne (e · d)

  data ⟦_⟧_↘_ : exp -> env -> D -> Set where
    e-var : ∀{v ρ i} -> v [ ρ ]= i -> ⟦ ▹ v ⟧ ρ ↘ i
    e-lam : ∀{t ρ} -> ⟦ ƛ t ⟧ ρ ↘ ƛ t ρ
    e-app : ∀{r s ρ a f b} ->
      ⟦ r ⟧ ρ ↘ f -> ⟦ s ⟧ ρ ↘ a ->  f · a ↘ b ->
      ⟦ r · s ⟧ ρ ↘ b

  
-- read-back relations


mutual
  data Rnf (n : ℕ) : D -> exp -> Set where
    r-lam : ∀{t ρ x b v} ->
      ⟦ t ⟧ ρ , (ne (▹ x n)) ↘ b -> Rnf (suc n) b v ->
      Rnf n (ƛ t ρ) (ƛ v)
    r-neu : ∀{e u} -> Rne n e u -> Rnf n (ne e) u


  data Rne (n : ℕ) : Dne -> exp -> Set where
    r-app : ∀{e d u v} ->
      Rne n e u -> Rnf n d v -> 
      Rne n (e · d) (u · v)
    r-var : ∀{x k} ->
      
      Rne n (▹ x k) (▹ (n ∸ (k + 1))) -- this is wrong
