--- This presentation follows Andreas Abel's Habilitation thesis section 2

module SystemT where
  open import Var

data tp : Set where
  nat : tp
  _⟼_ : tp -> tp -> tp

infixr 2 _⟼_

data const : tp  -> Set where
  zero : const nat
  succ : const (nat ⟼ nat)
  rec  : ∀{T} -> const (T ⟼ (nat ⟼ T ⟼ T) ⟼ nat ⟼ T)


data exp (Γ : ctx tp) : tp -> Set where
  c : ∀{T} -> const T -> exp Γ T
  ▹ : ∀{T} -> var tp Γ T -> exp Γ T
  ƛ : ∀{S T} -> exp (Γ , S) T -> exp Γ (S ⟼ T)
  _·_ : ∀{T S} -> exp Γ (T ⟼ S) -> exp Γ T -> exp Γ S

--- Interpretations of types contexts and terms
module interpretation where 

  open import Data.Nat
  open import Data.Unit
  open import Data.Product

  -- we'll need primitive recursion over naturals
  recℕ : {A : Set} (ez : A) (es : ℕ -> A -> A)(n : ℕ) -> A
  recℕ ez es zero = ez
  recℕ ez es (suc n) = es n (recℕ ez es n)

  ⟦_⟧t : tp -> Set
  ⟦ nat ⟧t = ℕ
  ⟦ T ⟼ S ⟧t = ⟦ T ⟧t → ⟦ S ⟧t

  ⟦_⟧ctx : ctx tp -> Set
  ⟦ ⊡ ⟧ctx = ⊤
  ⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx × ⟦ T ⟧t

  ⟦_⟧v : ∀{Γ T} (v : var tp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t
  ⟦_⟧v top (ρ , a) = a
  ⟦_⟧v (pop v) (ρ , a) = ⟦ v ⟧v ρ

  ⟦_⟧c : ∀{T} -> const T -> ⟦ T ⟧t
  ⟦ zero ⟧c = 0
  ⟦_⟧c succ n = suc n
  ⟦_⟧c rec = recℕ 

  ⟦_⟧ : ∀{Γ T} -> (e : exp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t 
  ⟦_⟧ (c con) ρ = ⟦ con ⟧c
  ⟦_⟧ (▹ x) ρ = ⟦ x ⟧v ρ
  ⟦_⟧ (ƛ e) ρ  a = ⟦_⟧ e (ρ , a)
  ⟦_⟧ (e · e₁) ρ = ⟦ e ⟧ ρ (⟦ e₁ ⟧ ρ)

--- Normal forms
module normal-forms where
  open import Data.Nat
  open import Data.Unit
  open import Data.Empty
  open import Data.Product
  open import Data.Sum

  -- we'll need primitive recursion over naturals
  recℕ : {A : Set} (ez : A) (es : ℕ -> A -> A)(n : ℕ) -> A
  recℕ ez es zero = ez
  recℕ ez es (suc n) = es n (recℕ ez es n)

  mutual 
    data nf (Γ : ctx tp) : tp -> Set where
      zero : nf Γ nat
      succ : nf Γ nat -> nf Γ nat
      neu : ∀{T} -> ne Γ T -> nf Γ T
      ƛ : ∀{S T} -> nf (Γ , S) T -> nf Γ (S ⟼ T)

    data ne (Γ : ctx tp) : tp -> Set where
      ▹ : ∀{T} -> var tp Γ T -> ne Γ T
      _·_ : ∀{T S} -> ne Γ (T ⟼ S) -> nf Γ T -> ne Γ S
      rec : ∀{T} -> (ez : nf Γ T) (es : nf ((Γ , nat) , T) T)(e : ne Γ nat) -> ne Γ T


  Nf : tp -> Set
  Nf T = (Γ : ctx tp) -> nf Γ T

  Ne : tp -> Set
  Ne T = (Γ : ctx tp) -> (ne Γ T ⊎ ⊥)

  ⟦_⟧t : tp -> Set
  ⟦ nat ⟧t = Nf nat
  ⟦ T ⟼ S ⟧t = ⟦ T ⟧t → ⟦ S ⟧t

  ⟦_⟧ctx : ctx tp -> Set
  ⟦ ⊡ ⟧ctx = ⊤
  ⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx × ⟦ T ⟧t

  -- ⟦_⟧v : ∀{Γ T} (v : var tp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t
  -- ⟦_⟧v top (ρ , a) = a
  -- ⟦_⟧v (pop v) (ρ , a) = ⟦ v ⟧v ρ

  -- ⟦_⟧c : ∀{T} -> const T -> ⟦ T ⟧t
  -- ⟦ zero ⟧c = ?
  -- ⟦_⟧c succ n = suc n
  -- ⟦_⟧c rec = recℕ 

  -- ⟦_⟧ : ∀{Γ T} -> (e : exp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t 
  -- ⟦_⟧ (c con) ρ = ⟦ con ⟧c
  -- ⟦_⟧ (▹ x) ρ = ⟦ x ⟧v ρ
  -- ⟦_⟧ (ƛ e) ρ  a = ⟦_⟧ e (ρ , a)
  -- ⟦_⟧ (e · e₁) ρ = ⟦ e ⟧ ρ (⟦ e₁ ⟧ ρ)


  mutual 
    reflect : ∀ T -> Ne T -> ⟦ T ⟧t
    reflect nat x Γ = {!!}
    reflect (S ⟼ T) u a = {!!}

    reify : ∀ T -> ⟦ T ⟧t  -> Nf T
    reify nat v = v
    reify (S ⟼ T) f Γ = {!!}

    refΓ : ∀ Γ -> ⟦ Γ ⟧ctx
    refΓ ⊡ = tt
    refΓ (Γ , T) = (refΓ Γ) , ?
