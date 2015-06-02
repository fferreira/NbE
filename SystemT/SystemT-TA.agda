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
  le-top : ∀{ρ a} -> zero [ ρ , a ]= a
  le-pop : ∀{v ρ a b} ->  v [ ρ ]= a -> (suc v) [ ρ , b ]= a

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

_⇒_ : (D -> Set) -> (D -> Set) -> (D -> Set)
(A ⇒ B) f = ∀ a -> a ∈ A -> ∃ (λ b -> b ∈ B × f · a ↘ b) 

⟦_⟧t : tp -> (D -> Set)
⟦ nat ⟧t = Nat
⟦ S ⟼ T ⟧t = ⟦ S ⟧t ⇒ ⟦ T ⟧t

data ctx : Set where
  ∅ : ctx
  _::_ : ctx -> tp -> ctx

data _[_]c=_ : ℕ -> ctx -> tp -> Set where
  lc-top : ∀{Γ T} -> zero [ Γ :: T ]c= T
  lc-pop : ∀{Γ T S v} -> v [ Γ ]c= T -> (suc v) [ Γ :: S ]c= T

data ⟦_⟧ctx : ctx -> env -> Set where
  ⟦∅⟧ctx : ∀{ρ} -> ρ ∈ ⟦ ∅ ⟧ctx -- why not nil ∈ ⟦ ∅ ⟧ctx ?
  ⟦::⟧ctx : ∀{ρ Γ d S} -> ρ ∈ ⟦ Γ ⟧ctx -> d ∈ ⟦ S ⟧t -> (ρ , d) ∈ ⟦ Γ :: S ⟧ctx


⟦_⟧_∈_ : exp -> env -> (D -> Set) -> Set
⟦ t ⟧ ρ ∈ B = ∃ (λ b → b ∈ B × ⟦ t ⟧ ρ ↘ b)

_⊨_∶_ : ctx -> exp -> tp -> Set
Γ ⊨ t ∶ T = ∀ ρ → ρ ∈ ⟦ Γ ⟧ctx → ⟦ t ⟧ ρ ∈ ⟦ T ⟧t

-- From the semantic typing we can prove these lemmas the follow the
-- structure of the typing rules, so these will help in stablishing
-- the soundness of the semantics with regard to the typing rules

lemma-zero : ∀{Γ} -> Γ ⊨ zero ∶ nat
lemma-zero Γ ρ = zero , zero , e-zero

lemma-suc : ∀{Γ t} -> Γ ⊨ t ∶ nat -> Γ ⊨ suc t ∶ nat
lemma-suc d ρ dρ with d ρ dρ 
lemma-suc d ρ dρ | n , N , e-n = (suc n) , (suc N , e-suc e-n)

lemma-var : ∀{Γ v T} -> v [ Γ ]c= T -> Γ ⊨ ▹ v ∶ T
lemma-var d ρ dρ = {!!}

lemma-lam : ∀{Γ t} S T -> (Γ :: S) ⊨ t ∶ T -> Γ ⊨ ƛ t ∶ (S ⟼ T)
lemma-lam S T d ρ dρ = {!!} 

lemma-app : ∀{Γ r s} S T -> Γ ⊨ r ∶ (S ⟼ T) -> Γ ⊨ s ∶ S -> Γ ⊨ r · s ∶ T
lemma-app S T d1 d2 ρ dρ = {!!}

lemma-rec : ∀{Γ tz ts tn} T -> 
            Γ ⊨ tz ∶ T -> Γ ⊨ ts ∶ (nat ⟼ (T ⟼ T)) -> Γ ⊨ tn ∶ nat ->
            Γ ⊨ rec tz ts tn ∶ T
lemma-rec T d1 d2 d3 ρ dρ = {!!}


data _⊢_∶_ (Γ : ctx) : exp -> tp -> Set where
  t-zero : Γ ⊢ zero ∶ nat
  t-suc  : ∀{t} -> Γ ⊢ t ∶ nat -> Γ ⊢ suc t ∶ nat
  t-var  : ∀{v T} -> v [ Γ ]c= T -> Γ ⊢ ▹ v ∶ T
  t-lam  : ∀{S T t} -> (Γ :: S) ⊢ t ∶ T -> Γ ⊢ ƛ t ∶ (S ⟼ T)
  t-app  : ∀{S T r s} -> Γ ⊢ r ∶ (S ⟼ T) -> Γ ⊢ s ∶ S -> Γ ⊢ r · s ∶ T
  t-rec  : ∀{T tz ts tn} -> 
           Γ ⊢ tz ∶ T -> Γ ⊢ ts ∶ (nat ⟼ (T ⟼ T)) -> Γ ⊢ tn ∶ nat ->
           Γ ⊢ rec tz ts tn ∶ T

soundness : ∀{Γ t T} -> Γ ⊢ t ∶ T -> Γ ⊨ t ∶ T
soundness t-zero ρ dρ = lemma-zero ρ dρ
soundness (t-suc d) ρ dρ = lemma-suc (soundness d) ρ dρ
soundness (t-var d) ρ dρ = lemma-var d ρ dρ
soundness (t-lam {S} {T} d) ρ dρ = lemma-lam S T (soundness d) ρ dρ
soundness (t-app {S} {T} d d₁) ρ dρ = lemma-app S T (soundness d) (soundness d₁) ρ dρ
soundness (t-rec {T} d d₁ d₂) ρ dρ = lemma-rec T (soundness d) (soundness d₁) (soundness d₂) ρ dρ
