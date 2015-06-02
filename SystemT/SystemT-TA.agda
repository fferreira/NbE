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

data _∋^_↘_ : env -> ℕ -> D -> Set where
  le-top : ∀{ρ a} -> (ρ , a) ∋^ zero ↘ a
  le-pop : ∀{v ρ a b} ->  ρ ∋^ v ↘ a ->  (ρ , b) ∋^ (suc v) ↘ a

-- evaluation relation

mutual
  data _·_↘_ : D -> D -> D -> Set where
    app-lam : ∀{t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> ƛ t ρ · a ↘ b
    app-neu : ∀{e d} -> (ne e) · d ↘ ne (e · d)

  data ⟦_⟧_↘_ : exp -> env -> D -> Set where
    e-var : ∀{v ρ i} -> 
      ρ ∋^ v ↘ i -> ⟦ ▹ v ⟧ ρ ↘ i
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

data _∋_∶_ : ctx -> ℕ -> tp -> Set where
  lc-top : ∀{Γ T} -> (Γ :: T) ∋ zero ∶ T
  lc-pop : ∀{Γ T S v} -> Γ ∋ v ∶ T ->  (Γ :: S) ∋ (suc v) ∶ T

data ∅' : env -> Set where
  nil : ∀ {ρ} -> ρ ∈ ∅' -- why not empty env ∈ ∅'

data _∷̂_  (Γ : env -> Set) (S : D -> Set) : (env -> Set) where
  cons : ∀{ρ d} -> ρ ∈ Γ -> d ∈ S -> (ρ , d) ∈(Γ ∷̂ S)

-- Semantic contexts (just a shortcut for predicate over environments)
Ctx : Set₁
Ctx = env -> Set

-- Semantic types
Tp : Set₁
Tp = D -> Set

⟦_⟧ctx : ctx -> Ctx
⟦ ∅ ⟧ctx = ∅'
⟦ Γ :: S ⟧ctx = ⟦ Γ ⟧ctx ∷̂ ⟦ S ⟧t

⟦_⟧_∈_ : exp -> env -> Tp -> Set
⟦ t ⟧ ρ ∈ B = ∃ (λ b → b ∈ B × ⟦ t ⟧ ρ ↘ b)

⟦_⟧_∈v_ : ℕ -> env -> Tp -> Set
⟦ v ⟧ ρ ∈v B = ∃ (λ b → b ∈ B × ρ ∋^ v ↘ b)


-- In Abel's habilitation thesis the semantic typing is presentd as
-- relating syntactic contexts, expressions and syntactic types. Here,
-- as per Andrew's suggestion, we have that semantic types relates
-- semantic contexts (aka predicates on environments), expressions and
-- semantic types (aka predicates on types).

_⊨_∶_ : Ctx -> exp -> Tp -> Set
Γ ⊨ t ∶ T = ∀ ρ → ρ ∈ Γ → ⟦ t ⟧ ρ ∈ T

_∋^_∶_ : Ctx -> ℕ -> Tp -> Set
Γ ∋^ v ∶ T = ∀ ρ → ρ ∈ Γ → ⟦ v ⟧ ρ ∈v T

-- From the semantic typing we can prove these lemmas the follow the
-- structure of the typing rules, so these will help in stablishing
-- the soundness of the semantics with regard to the typing rules

s-zero : ∀{Γ} -> Γ ⊨ zero ∶ Nat
s-zero Γ ρ = zero , zero , e-zero

s-suc : ∀{Γ t} -> Γ ⊨ t ∶ Nat -> Γ ⊨ suc t ∶ Nat
s-suc d ρ dρ with d ρ dρ 
s-suc d ρ dρ | n , N , e-n = (suc n) , (suc N , e-suc e-n)

s-lam : ∀{Γ t S T} -> (Γ ∷̂ S) ⊨ t ∶ T -> Γ ⊨ ƛ t ∶ (S ⇒ T)
s-lam d ρ dρ = {!!}

s-var : ∀ {Γ v T} -> Γ ∋^ v ∶ T -> Γ ⊨ ▹ v ∶ T
s-var d ρ dρ with d ρ dρ
... | b , B , dv = b , B , e-var dv 

s-app : ∀{Γ r s S T} -> Γ ⊨ r ∶ (S ⇒ T) -> Γ ⊨ s ∶ S -> Γ ⊨ r · s ∶ T
s-app d1 d2 ρ dρ = {!!}

s-rec : ∀{Γ tz ts tn T} -> 
            Γ ⊨ tz ∶ T -> Γ ⊨ ts ∶ (Nat ⇒ (T ⇒ T)) -> Γ ⊨ tn ∶ Nat ->
            Γ ⊨ rec tz ts tn ∶ T
s-rec d1 d2 d3 ρ dρ = {!!}

s-top : ∀{Γ T} -> (Γ ∷̂ T) ∋^ zero ∶ T
s-top ._ (cons _ t) = , (t , le-top)

s-pop : ∀{Γ T S v} -> Γ ∋^ v ∶ T ->  (Γ ∷̂ S) ∋^ (suc v) ∶ T
s-pop dv ._ (cons x x₁) with dv _ x
... | v , V , ddv = v , (V , le-pop ddv)

data _⊢_∶_ (Γ : ctx) : exp -> tp -> Set where
  t-zero : Γ ⊢ zero ∶ nat
  t-suc  : ∀{t} -> Γ ⊢ t ∶ nat -> Γ ⊢ suc t ∶ nat
  t-var  : ∀{v T} -> Γ ∋ v ∶ T -> Γ ⊢ ▹ v ∶ T
  t-lam  : ∀{S T t} -> (Γ :: S) ⊢ t ∶ T -> Γ ⊢ ƛ t ∶ (S ⟼ T)
  t-app  : ∀{S T r s} -> Γ ⊢ r ∶ (S ⟼ T) -> Γ ⊢ s ∶ S -> Γ ⊢ r · s ∶ T
  t-rec  : ∀{T tz ts tn} -> 
           Γ ⊢ tz ∶ T -> Γ ⊢ ts ∶ (nat ⟼ (T ⟼ T)) -> Γ ⊢ tn ∶ nat ->
           Γ ⊢ rec tz ts tn ∶ T

var-soundness : ∀{Γ v T} -> Γ ∋ v ∶ T -> (⟦ Γ ⟧ctx) ∋^ v ∶ ⟦ T ⟧t
var-soundness lc-top = s-top
var-soundness (lc-pop dv) = s-pop (var-soundness dv) 

soundness : ∀{Γ t T} -> Γ ⊢ t ∶ T -> ⟦ Γ ⟧ctx ⊨ t ∶ ⟦ T ⟧t
soundness t-zero = s-zero
soundness (t-suc d) = s-suc (soundness d)
soundness (t-var d) = s-var (var-soundness d)
soundness (t-lam d) = s-lam (soundness d)
soundness (t-app d d₁) = s-app (soundness d) (soundness d₁)
soundness (t-rec d d₁ d₂) = s-rec (soundness d) (soundness d₁) (soundness d₂)

