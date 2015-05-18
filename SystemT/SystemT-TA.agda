-- From Andreas Abel's Habilitation thesis section 3

module SystemT-TA where
  open import Data.Nat

data tp : Set where
  nat : tp
  _⟼_ : tp -> tp -> tp

mutual
  data exp : Set where
    ▹ : ℕ -> exp -- De Bruijn indeces
    ƛ : exp -> exp
    _·_ : exp -> exp -> exp
    zero : exp
    suc : exp -> exp
    rec : exp -> exp -> exp -> exp
    _[_] : exp -> subst -> exp

  data subst : Set where
    ↑ : subst
    id : subst
    _∘_ : subst -> subst -> subst
    _,_ : subst -> exp -> subst
    

mutual
  data nf : Set where
    ƛ : nf -> nf 
    ne : neu -> nf
    zero : nf
    suc : nf -> nf

  data neu : Set where
    ▹ : ℕ -> neu 
    _·_ : neu -> nf -> neu
    rec : (vz vs : nf) -> (u : neu) -> neu

-- sematics

mutual 
  data D : Set where
    ƛ : exp -> env -> D
    ne : Dne -> D
    zero : D
    suc : D -> D

  data Dne : Set where
    _·_ : Dne -> D -> Dne
    ▹ : (x k : ℕ) -> Dne -- De Bruijn levels
    rec : (dz ds : D) -> (e : Dne) -> Dne

  data env : Set where
    nil : env
    _,_ : env -> D -> env

-- environment lookup

data _[_]=_ : ℕ -> env -> D -> Set where
  l-top : ∀{ρ a} -> zero [ ρ , a ]= a
  l-pop : ∀{v ρ a b} ->  v [ ρ ]= a -> (suc v) [ ρ , b ]= a

-- evaluation relation

mutual
  data _·_↘_ : D -> D -> D -> Set where
    app-lam : ∀{t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> ƛ t ρ · a ↘ b
    app-neu : ∀{e d} -> (ne e) · d ↘ ne (e · d)

  data ⟦_⟧_↘_ : exp -> env -> D -> Set where
    e-var : ∀{v ρ i} -> 
      v [ ρ ]= i -> ⟦ ▹ v ⟧ ρ ↘ i
    e-lam : ∀{t ρ} -> 
      ⟦ ƛ t ⟧ ρ ↘ ƛ t ρ
    e-app : ∀{r s ρ a f b} ->
      ⟦ r ⟧ ρ ↘ f -> ⟦ s ⟧ ρ ↘ a ->  f · a ↘ b ->
      ⟦ r · s ⟧ ρ ↘ b
    e-zero : ∀{ρ} ->
      ⟦ zero ⟧ ρ ↘ zero
    e-suc : ∀{t ρ d} ->
      ⟦ t ⟧ ρ ↘ d ->
      ⟦ suc t ⟧ ρ ↘ (suc d)
    e-rec : ∀{tz ts tn dz ds dn ρ d} ->
      ⟦ tz ⟧ ρ ↘ dz ->
      ⟦ ts ⟧ ρ ↘ ds ->
      ⟦ tn ⟧ ρ ↘ dn ->
      rec dz , ds , dn ↘ d -> 
      ⟦ rec tz ts tn ⟧ ρ ↘ d
    e-sub : ∀{t σ ρ ρ' a} ->
      ⟦ σ ⟧s ρ ↘ ρ' ->
      ⟦ t ⟧ ρ' ↘ a -> 
      ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : subst -> env -> env -> Set where
    e-shift : ∀{ρ a} -> 
      ⟦ ↑ ⟧s (ρ , a) ↘ ρ
    e-id : ∀{ρ} ->
      ⟦ id ⟧s ρ ↘ ρ
    e-comp : ∀{τ σ ρ ρ' ρ''} ->
      ⟦ τ ⟧s ρ ↘ ρ' ->
      ⟦ σ ⟧s ρ' ↘ ρ'' ->
      ⟦ σ ∘ τ ⟧s ρ ↘ ρ''
    e-ext : ∀ {σ ρ ρ' s a} ->
      ⟦ σ ⟧s ρ ↘ ρ' ->
      ⟦ s ⟧ ρ ↘ a ->
      ⟦ σ , s ⟧s ρ ↘ (ρ' , a)

  data rec_,_,_↘_ : D -> D -> D -> D -> Set where
    r-zero : ∀{dz ds} ->
      rec dz , ds , zero ↘ dz
    r-suc  : ∀{dz ds dn a f b} ->
      rec dz , ds , dn ↘ a ->
      ds · dn ↘ f ->
      f · a ↘ b -> 
      rec dz , ds , suc dn ↘ b

-- read-back relations

mutual
  data Rnf (n : ℕ) : D -> nf -> Set where
    r-lam : ∀{t ρ x b v} ->
      ⟦ t ⟧ ρ , (ne (▹ x n)) ↘ b -> Rnf (suc n) b v ->
      Rnf n (ƛ t ρ) (ƛ v)
    r-neu : ∀{e u} -> Rne n e u -> Rnf n (ne e) (ne u)
    r-zero :  Rnf n zero zero
    r-suc : ∀{d v} ->
      Rnf n d v ->
      Rnf n (suc d) (suc v)

  data Rne (n : ℕ) : Dne -> neu -> Set where
    r-app : ∀{e d u v} ->
      Rne n e u -> Rnf n d v -> 
      Rne n (e · d) (u · v)
    r-var : ∀{x k} ->
      Rne n (▹ x k) (▹ (n ∸ (k + 1))) -- this is probably wrong
    r-rec : ∀{ dz ds vz vs e u} ->
      Rnf n dz vz ->
      Rnf n ds vs ->
      Rne n e u ->
      Rne n (rec dz ds e) (rec vz vs u) 



-- candidate spaces

open import Data.Product

⊤ : D -> Set
⊤ d = ∀ n -> ∃ (λ v -> Rnf n d v)

⊥ : Dne -> Set
⊥ d = ∀ n -> ∃ (λ u -> Rne n d u)

_∈_ : ∀ {A : Set} -> A -> (A -> Set) -> Set
a ∈ P = P a

data Nat : D -> Set where
  zero : zero ∈ Nat
  suc : ∀ {d} -> d ∈ Nat -> suc d ∈ Nat
  ne : ∀ {e} -> e ∈ ⊥ -> (ne e) ∈ Nat

-- semantic typing

⟦_⟧t : tp -> Set
⟦ nat ⟧t = Nat {!!}
⟦ S ⟼ T ⟧t = ⟦ S ⟧t → ⟦ T ⟧t

