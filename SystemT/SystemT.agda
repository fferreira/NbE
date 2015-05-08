--- This presentation follows Andreas Abel's Habilitation thesis section 2

module SystemT where
  open import Var

data tp : Set where
  nat : tp
  _⟼_ : tp -> tp -> tp

infixr 2 _⟼_

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.Sum
open import Data.Unit

decEqT : (T S : tp) -> T ≡ S ⊎ ⊤
decEqT nat nat = inj₁ refl
decEqT nat (S ⟼ S₁) = inj₂ tt
decEqT (T ⟼ T₁) nat = inj₂ tt
decEqT (T ⟼ T₁) (S ⟼ S₁) with decEqT T S
decEqT (T ⟼ T₁) (.T ⟼ S₁) | inj₁ refl with decEqT T₁ S₁
decEqT (T ⟼ T₁) (.T ⟼ .T₁) | inj₁ refl | inj₁ refl = inj₁ refl
decEqT (T ⟼ T₁) (.T ⟼ S₁) | inj₁ refl | inj₂ tt = inj₂ tt
decEqT (T ⟼ T₁) (S ⟼ S₁) | inj₂ tt = inj₂ tt

data const : tp  -> Set where
  zero : const nat
  succ : const (nat ⟼ nat)
  rec  : ∀{T} -> const (T ⟼ (nat ⟼ T ⟼ T) ⟼ nat ⟼ T)

data exp (Γ : ctx tp) : tp -> Set where
  c : ∀{T} -> const T -> exp Γ T
  ▹ : ∀{T} -> var tp Γ T -> exp Γ T
  ƛ : ∀{S T} -> exp (Γ , S) T -> exp Γ (S ⟼ T)
  _·_ : ∀{T S} -> exp Γ (T ⟼ S) -> exp Γ T -> exp Γ S

--- Normal forms
module normal-forms where
  open import Data.Nat
  open import Data.Unit
  open import Data.Empty
  open import Data.Product

  mutual
    data nf (Γ : ctx tp) : tp -> Set where
      zero : nf Γ nat
      succ : nf Γ nat -> nf Γ nat
      neu : ∀{T} -> ne Γ T -> nf Γ T
      ƛ : ∀{S T} -> nf (Γ , S) T -> nf Γ (S ⟼ T)

    data ne (Γ : ctx tp) : tp -> Set where
      ▹ : ∀{T} -> var tp Γ T -> ne Γ T
      _·_ : ∀{T S} -> ne Γ (T ⟼ S) -> nf Γ T -> ne Γ S
      rec : ∀{T} -> (ez : nf Γ T) (es : nf Γ (nat ⟼ T ⟼ T))(e : ne Γ nat) -> ne Γ T

  Nf : tp -> Set
  Nf T = (Γ : ctx tp) -> nf Γ T

  Ne : tp -> Set
  Ne T = (Γ : ctx tp) -> (ne Γ T ⊎ ⊤)
  -- If you are following Andreas's notes, you'll notice that top is
  -- bottom and war is peace. Or that {⊥} is the type with one
  -- inhabitant and that's why I use top.

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat
    neu  : Ne nat → Nat

  ⟦_⟧t : tp -> Set
  ⟦ nat ⟧t = Nat
  ⟦ T ⟼ S ⟧t = ⟦ T ⟧t → ⟦ S ⟧t

  ⟦_⟧ctx : ctx tp -> Set
  ⟦ ⊡ ⟧ctx = ⊤
  ⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx × ⟦ T ⟧t

  ⟦_⟧v : ∀{Γ T} (v : var tp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t
  ⟦_⟧v top (ρ , a) = a
  ⟦_⟧v (pop v) (ρ , a) = ⟦ v ⟧v ρ

  mutual
    ⟦_⟧c : ∀{T} -> const T -> ⟦ T ⟧t
    ⟦ zero ⟧c = zero
    ⟦_⟧c succ n = succ (n)
    ⟦_⟧c {(T ⟼ (nat ⟼ .T ⟼ .T) ⟼ nat ⟼ .T)} rec = rec-nat T

    maybe-rec : ∀ {T Γ} →
      nf Γ T → nf Γ (nat ⟼ T ⟼ T) → ne Γ nat ⊎ ⊤ → ne Γ T ⊎ ⊤
    maybe-rec vz vs (inj₁ e) = inj₁ (rec vz vs e)
    maybe-rec vz vs (inj₂ tt) = inj₂ tt

    -- Here I provide a recursion principle on Nat.
    rec-nat : (T : tp) (ez : ⟦ T ⟧t)
              (es : Nat -> ⟦ T ⟧t -> ⟦ T ⟧t)(n : Nat) -> ⟦ T ⟧t
    rec-nat T ez es zero = ez
    rec-nat T ez es (succ n) = es n (rec-nat T ez es n)
    rec-nat T ez es (neu e) =
        reflect T (λ Γ → maybe-rec (reify T ez Γ) (reify (nat ⟼ T ⟼ T) es Γ) (e Γ))

    ⟦_⟧ : ∀{Γ T} -> (e : exp Γ T)(ρ : ⟦ Γ ⟧ctx) -> ⟦ T ⟧t
    ⟦_⟧ (c con) ρ = ⟦ con ⟧c
    ⟦_⟧ (▹ x) ρ = ⟦ x ⟧v ρ
    ⟦_⟧ (ƛ e) ρ  a = ⟦_⟧ e (ρ , a)
    ⟦_⟧ (e · e₁) ρ = ⟦ e ⟧ ρ (⟦ e₁ ⟧ ρ)

    -- a maybe neutral is a normal form
    lemma₁ : ∀ {Γ} → ne Γ nat ⊎ ⊤ → nf Γ nat
    lemma₁ (inj₁ e) = neu e
    lemma₁ (inj₂ tt) = zero

    -- a maybe neutral can be applied to a normal form to get a maybe
    -- neutral
    lemma₂ : ∀ {S T Δ} → ne Δ (S ⟼ T) ⊎ ⊤ → nf Δ S → ne Δ T ⊎ ⊤
    lemma₂ (inj₁ e) n = inj₁ (e · n)
    lemma₂ (inj₂ tt) n = inj₂ tt

    reflect : ∀ T -> Ne T -> ⟦ T ⟧t
    reflect nat u = neu u
    reflect (S ⟼ T) u a = let v = reify S a in reflect T (λ Δ → lemma₂ (u Δ) (v Δ))

    fresh : ∀ S Γ → ne Γ S ⊎ ⊤
    fresh S ⊡ = inj₂ tt
    fresh S (Γ , T) with decEqT S T
    -- only gives a variable if the context is the "right" extension
    fresh S (Γ , .S) | inj₁ refl = inj₁ (▹ top)
    fresh S (Γ , T) | inj₂ tt = inj₂ tt

    reifyNat : Nat → Nf nat
    reifyNat zero Γ = zero
    reifyNat (succ n) Γ = succ (reifyNat n Γ)
    reifyNat (neu x) Γ = lemma₁ (x Γ)

    reify : ∀ T -> ⟦ T ⟧t  -> Nf T
    reify nat v = reifyNat v
    reify (S ⟼ T) f Γ = let a = reflect S (fresh S) in ƛ (reify T (f a) (Γ , S))

    refΓ : ∀ Γ -> ⟦ Γ ⟧ctx
    refΓ ⊡ = tt
    refΓ (Γ , T) = (refΓ Γ) , reflect T (fresh T)

  normal : ∀{Γ T} -> (t : exp Γ T) -> nf Γ T
  normal {Γ} {T} t = reify T (⟦ t ⟧ (refΓ Γ)) Γ
