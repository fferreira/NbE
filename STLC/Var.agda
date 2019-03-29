module Var (tp : Set) where

infixl 4 _,_
infixr 4 _::_

data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) (T : tp) → ctx

_⋈_ : ctx → ctx → ctx
Γ ⋈ ⊡ = Γ
Γ ⋈ (Γ' , T) = (Γ ⋈ Γ') , T

-- simultaneous substitutions to transport terms from a context to another
data sub (F : tp → Set) : ctx → Set where
  ∅ : sub F ⊡
  _::_ : ∀{Γ}{T : tp} → F T → sub F Γ → sub F (Γ , T)

map-sub : ∀{Γ} → {F G : tp → Set} → (∀ {T} → F T → G T) → sub F Γ → sub G Γ
map-sub f ∅ = ∅
map-sub f (FT :: σ) = f FT :: map-sub f σ 

data var : ctx → tp → Set where
  top : ∀ {Γ T} → var (Γ , T) T
  pop : ∀ {Γ T S} → var Γ T → var (Γ , S) T

-- application for sub with vars
app : ∀{Γ F T} → sub F Γ → var Γ T →  F T
app (R :: _) top = R
app (_ :: σ) (pop x) = app σ x

-- simultaneous variable renamings
ren : (Γ Γ' : ctx) → Set
ren Γ Γ' = sub (λ T → var Γ' T) Γ

-- funcrtions that use renamings
wkn-ren : ∀{Γ Δ T} → ren Γ Δ → ren (Γ , T) (Δ , T)
wkn-ren σ = top :: map-sub pop σ 

id-ren : ∀{Γ} → ren Γ Γ
id-ren {⊡} = ∅
id-ren {Γ , T} = top :: (map-sub pop id-ren)

wkn-ren-im : ∀{Γ T} → ren Γ (Γ , T)
wkn-ren-im = map-sub pop id-ren

wkn-ren-ctx-im : ∀{Γ Γ'} → ren Γ (Γ ⋈ Γ')
wkn-ren-ctx-im {Γ' = ⊡} = id-ren
wkn-ren-ctx-im {Γ} {Γ' , T} with wkn-ren-ctx-im {Γ} {Γ'}
... | θ = map-sub (λ {T₁} → pop) θ

wkn-ren-ctx : ∀{Γ Γ'} Δ → ren Γ Γ' → ren (Γ ⋈ Δ) (Γ' ⋈ Δ)
wkn-ren-ctx ⊡ σ = σ
wkn-ren-ctx (Δ , T) σ = wkn-ren (wkn-ren-ctx Δ σ)

-- one has to write [_]r :  ∀{Γ Δ T} → ren Γ Δ → exp Γ T → exp Δ T

module Subst (exp : ctx → tp → Set) (▹ : ∀{T Γ} → var Γ T → exp Γ T) ([_]r :  ∀{Γ Δ T} → ren Γ Δ → exp Γ T → exp Δ T) where

  -- we define simultaneous substitutions to transport terms from a context to another
  sub' : (Γ Γ : ctx) → Set 
  sub'  Γ Γ' =  sub (λ T → exp Γ' T) Γ

  -- before we can define the SOS we need to define how to apply
  -- substitutions

  wkn : ∀{Γ T S} → exp Γ T → exp (Γ , S) T
  wkn M = [ wkn-ren-im ]r M

  wkn-im : ∀{Γ T Δ} → sub' Γ Δ → sub' Γ (Δ , T)
  wkn-im σ = map-sub wkn σ

  wkn-im-ctx : ∀{Γ Γ'} Δ → sub' Γ Γ' → sub' Γ (Γ' ⋈ Δ)
  wkn-im-ctx ⊡ σ = σ
  wkn-im-ctx (Δ , T) σ = wkn-im (wkn-im-ctx Δ σ)

  wkn-sub : ∀{Γ Δ T} → sub' Γ Δ → sub' (Γ , T) (Δ , T)
  wkn-sub σ = ▹ top :: wkn-im σ

  wkn-ctx : ∀{Γ Γ'} Δ → sub' Γ Γ' → sub' (Γ ⋈ Δ) (Γ' ⋈ Δ)
  wkn-ctx ⊡ σ = σ
  wkn-ctx (Δ , T) σ = wkn-sub (wkn-ctx Δ σ)

  id : ∀ {Γ} → sub' Γ Γ
  id {⊡} = ∅
  id {Γ , T} = (▹ top) :: wkn-im id

  wkn-id-im-ctx : ∀{Γ} Δ → sub' Γ (Γ ⋈ Δ)
  wkn-id-im-ctx Δ = wkn-im-ctx Δ id

  wkn-id-im : ∀{Γ T} → sub' Γ (Γ , T)
  wkn-id-im = wkn-im id

  pre-wkn : ∀{Γ Γ'} → sub' Γ (Γ' ⋈ Γ)
  pre-wkn {⊡} = ∅
  pre-wkn {Γ , T} = (▹ top) :: (wkn-im pre-wkn)

  sub-pair : ∀ {Γ Δ1 Δ2} → sub' Δ1 Γ → sub' Δ2 Γ → sub' (Δ1 ⋈ Δ2) Γ
  sub-pair σ1 ∅ = σ1
  sub-pair σ1 (x :: σ2) = x :: sub-pair σ1 σ2

  -- one has to write [_] : ∀{Γ Δ T} → sub' Γ Δ → exp Γ T → exp Δ T

























