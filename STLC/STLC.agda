module STLC where
  open import Data.Nat

  -- signature types

  -- this is an example signature, it should be module and take this
  -- as parameter.
  data sigtype : Set where
    term : sigtype

  data tp : Set where
    base : sigtype -> tp
    _>->_ : tp -> tp -> tp

  -- these example constructors provide the untyped lambda calculus
  -- syntax. These too should be parametrised in a module.
  data sigcon : tp -> Set where
    lam : sigcon ((base term >-> base term) >-> base term)
    app : sigcon (base term >-> (base term >-> base term))

  mutual
    data exp : Set where
      ▹ : ℕ -> exp -- De Bruijn indeces
      ƛ : exp -> exp
      _·_ : exp -> exp -> exp
      C : ∀{A} -> sigcon A -> exp
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

    data neu : Set where
      ▹ : ℕ -> neu
      C : ∀{A} -> sigcon A -> neu
      _·_ : neu -> nf -> neu


  -- sematics

  mutual
    data D : Set where
      ƛ : exp -> env -> D
      ne : Dne -> D

    data Dne : Set where
      _·_ : Dne -> D -> Dne
      C : ∀{A} -> sigcon A -> Dne
      ▹ : (k : ℕ) -> Dne -- De Bruijn levels

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
      e-ext : ∀ {σ ρ ρ' s a} -> -- ext stands for substitution extension
        ⟦ σ ⟧s ρ ↘ ρ' ->
        ⟦ s ⟧ ρ ↘ a ->
        ⟦ σ , s ⟧s ρ ↘ (ρ' , a)


  -- read-back relations

  mutuals
    data Rnf (n : ℕ) : D -> nf -> Set where
      r-lam : ∀{t ρ b v} ->
        ⟦ t ⟧ ρ , (ne (▹ n)) ↘ b -> Rnf (suc n) b v ->
        Rnf n (ƛ t ρ) (ƛ v)
      r-neu : ∀{e u} -> Rne n e u -> Rnf n (ne e) (ne u)

    data Rne (n : ℕ) : Dne -> neu -> Set where
      r-app : ∀{e d u v} ->
        Rne n e u -> Rnf n d v ->
        Rne n (e · d) (u · v)
      r-con : ∀{A}{cons : sigcon A} ->
        Rne n (C cons) (C cons)
      r-var : ∀{k} ->
        Rne n (▹ k) (▹ (n ∸ (k + 1))) -- this is probably wrong

  -- candidate spaces

  open import Data.Product

  _∈_ : ∀ {A : Set} -> A -> (A -> Set) -> Set
  a ∈ P = P a

  ⊤ : D -> Set
  ⊤ d = ∀ n -> ∃ (λ v -> Rnf n d v)

  data ⊥ : D -> Set where
   inj : ∀ {d} -> (∀ n -> ∃ (λ u -> Rne n d u)) -> (ne d) ∈ ⊥

  -- Semantic types
  Tp : Set₁
  Tp = D -> Set

  _⊂_ : Tp -> Tp -> Set
  T ⊂ S = ∀ x → x ∈ T → x ∈ S

  Cand : Tp -> Set
  Cand A = (⊥ ⊂ A) × (A ⊂ ⊤)

  -- there are no natural numbers now, but the are constructors that
  -- form sigtypes so... do we need to have those instead of zero and
  -- suc and probably need to move the to normal forms not neutrals
  -- (check the thesis). TODO (1) add the proper constructors here
  data Nat : D -> Set where
    -- zero : zero ∈ Nat
    -- suc : ∀ {d} -> d ∈ Nat -> suc d ∈ Nat
    ne : ∀ {d} -> d ∈ ⊥ -> d ∈ Nat

  -- semantic typing

  _⇒_ : Tp -> Tp -> Tp
  (A ⇒ B) f = ∀ a -> a ∈ A -> ∃ (λ b -> b ∈ B × f · a ↘ b)

  ⟦_⟧t : tp -> (D -> Set)
  ⟦ base t ⟧t = {!!} -- TODO (2) put the new Nat here :P
  ⟦ S >-> T ⟧t = ⟦ S ⟧t ⇒ ⟦ T ⟧t

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

  ⟦_⟧ctx : ctx -> Ctx
  ⟦ ∅ ⟧ctx = ∅'
  ⟦ Γ :: S ⟧ctx = ⟦ Γ ⟧ctx ∷̂ ⟦ S ⟧t

  ⟦_⟧_∈_ : exp -> env -> Tp -> Set
  ⟦ t ⟧ ρ ∈ B = ∃ (λ b → b ∈ B × ⟦ t ⟧ ρ ↘ b)

  ⟦_⟧_∈v_ : ℕ -> env -> Tp -> Set
  ⟦ v ⟧ ρ ∈v B = ∃ (λ b → b ∈ B × ρ ∋^ v ↘ b)

  ⟦_⟧_∈s_ : subst -> env -> Ctx -> Set
  ⟦ σ ⟧ ρ ∈s Δ = ∃ (λ b → b ∈ Δ × ⟦ σ ⟧s ρ ↘ b)

  -- In Abel's habilitation thesis the semantic typing is presentd as
  -- relating syntactic contexts, expressions and syntactic types. Here,
  -- as per Andrew's suggestion, we have that semantic types relates
  -- semantic contexts (aka predicates on environments), expressions and
  -- semantic types (aka predicates on types).

  _⊨_∶_ : Ctx -> exp -> Tp -> Set
  Γ ⊨ t ∶ T = ∀ ρ → ρ ∈ Γ → ⟦ t ⟧ ρ ∈ T

  -- semantic typing for substitutions
  _⊨s_∶_ : Ctx -> subst -> Ctx -> Set
  Γ ⊨s σ ∶ Δ = ∀ ρ → ρ ∈ Γ → ⟦ σ ⟧ ρ ∈s Γ

  -- _⊨rec_,_,_∶_ : Ctx -> (tz ts tn : exp) -> Tp -> Set
  -- Γ ⊨rec tz , ts , tn ∶ T = ∀ ρ -> ρ ∈ Γ -> ⟦ (rec tz ts tn) ⟧ ρ ∈ T

  _∋^_∶_ : Ctx -> ℕ -> Tp -> Set
  Γ ∋^ v ∶ T = ∀ ρ → ρ ∈ Γ → ⟦ v ⟧ ρ ∈v T

  -- From the semantic typing we can prove these lemmas the follow the
  -- structure of the typing rules, so these will help in stablishing
  -- the soundness of the semantics with regard to the typing rules

-- TODO (3) keep pushing this comment down to finish the thing
{-
  s-zero : ∀{Γ} -> Γ ⊨ zero ∶ Nat
  s-zero Γ ρ = zero , zero , e-zero

  s-suc : ∀{Γ t} -> Γ ⊨ t ∶ Nat -> Γ ⊨ suc t ∶ Nat
  s-suc d ρ dρ with d ρ dρ
  s-suc d ρ dρ | n , N , e-n = (suc n) , (suc N , e-suc e-n)

  s-lam : ∀{Γ t S T} -> (Γ ∷̂ S) ⊨ t ∶ T -> Γ ⊨ ƛ t ∶ (S ⇒ T)
  s-lam d ρ dρ = ƛ _ ρ , (lem0 d dρ , e-lam)
    where
      lem0 : ∀ {Γ S T ρ t} -> (Γ ∷̂ S) ⊨ t ∶ T -> ρ ∈ Γ -> (ƛ t ρ) ∈ (S ⇒ T)
      lem0 d dρ a da with d _ (cons dρ da)
      ... | b , B , dv = , (B , app-lam dv)

  s-var : ∀ {Γ v T} -> Γ ∋^ v ∶ T -> Γ ⊨ ▹ v ∶ T
  s-var d ρ dρ with d ρ dρ
  ... | b , B , dv = b , B , e-var dv

  s-app : ∀{Γ r s S T} -> Γ ⊨ r ∶ (S ⇒ T) -> Γ ⊨ s ∶ S -> Γ ⊨ r · s ∶ T
  s-app d1 d2 ρ dρ with d1 ρ dρ | d2 ρ dρ
  s-app d1 d2 ρ dρ | d₁ , D₁ , da₁ | d₂ , D₂ , da₂ with D₁ d₂ D₂
  s-app d1 d2 ρ dρ | d₁ , D₁ , da₁ | d₂ , D₂ , da₂ | d₁d₂ , D₁D₂ , dapp =
    d₁d₂ , (D₁D₂ , (e-app da₁ da₂ dapp))

  s-shift : ∀{Γ S} -> (Γ ∷̂ S) ⊨s ↑ ∶ Γ
  s-shift = λ ρ x → {!!}

  s-id : ∀{Γ} -> Γ ⊨s id ∶ Γ
  s-id ρ dρ = ρ , dρ , e-id

  s-comp : ∀{Γ₁ Γ₂ Γ₃ σ τ} -> Γ₁ ⊨s τ ∶ Γ₂ -> Γ₂ ⊨s σ ∶ Γ₃ -> Γ₁ ⊨s σ ∘ τ ∶ Γ₃
  s-comp d1 d2 = {!!}

  s-ext : ∀{Γ Δ σ s S} -> Γ ⊨s σ ∶ Δ -> Γ ⊨ s ∶ S -> Γ ⊨s (σ , s) ∶ (Δ ∷̂ S)
  s-ext = {!!}

  s-sub : ∀{Γ Δ σ t T} -> Γ ⊨s σ ∶ Δ -> Δ ⊨ t ∶ T -> Γ ⊨ t [ σ ] ∶ T
  s-sub = {!!}

  rec'_,_,_∈_ : D -> D -> D -> Tp -> Set
  rec' dz , ds , dn ∈ T = ∃ (λ b → b ∈ T × rec dz , ds , dn ↘ b)

  lem1 : ∀ {dz ds n T}
   -> n ∈ Nat
   -> ds ∈ (Nat ⇒ (T ⇒ T))
   -> rec' dz , ds , n ∈ T
   -> rec' dz , ds , suc n ∈ T
  lem1 Dn Ds (r , (Dr , Ddr)) with Ds _ Dn
  ... | (f , (Df , Ddf)) with Df _ Dr
  ... | (b , (Db , Ddb)) = , (Db , r-suc Ddr Ddf Ddb)


  ⊥⊂A⇒B : ∀ {A B} -> Cand A -> Cand B -> ⊥ ⊂ (A ⇒ B)
  ⊥⊂A⇒B (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) ._ (inj e) a a∈A =
    , (⊥⊂B (ne (_ · a)) (inj (λ n → , (r-app (proj₂ (e n)) (proj₂ (A⊂⊤ a a∈A n))))) , app-neu)

  A⇒B⊂⊤ : ∀ {A B} -> Cand A -> Cand B -> (A ⇒ B) ⊂ ⊤
  A⇒B⊂⊤ (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) f f∈A⇒B n with f∈A⇒B (ne (▹ n)) (⊥⊂A _ (inj (λ n₁ → _ , r-var)))
  A⇒B⊂⊤ (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) ._ f∈A⇒B n | b , Db , app-lam x with B⊂⊤ _ Db (suc n)
  A⇒B⊂⊤ (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) ._ f∈A⇒B n | b , Db , app-lam x | _ , Dv = ƛ _ , r-lam x Dv
  A⇒B⊂⊤ (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) ._ f∈A⇒B n | ._ , Db , app-neu with B⊂⊤ _ Db n
  A⇒B⊂⊤ (⊥⊂A , A⊂⊤) (⊥⊂B , B⊂⊤) ._ f∈A⇒B n | ._ , Db , app-neu | ._ , r-neu (r-app x x₁) = , r-neu x

  Cand⇒ : ∀ {A B} -> Cand A -> Cand B -> Cand (A ⇒ B)
  Cand⇒ ca cb = ⊥⊂A⇒B ca cb , A⇒B⊂⊤ ca cb

  Cand-Nat : Cand Nat
  Cand-Nat = (λ x → ne) , Nat⊂⊤
    where
      Nat⊂⊤ : ∀ x → Nat x → ∀ n → Σ nf (Rnf n x)
      Nat⊂⊤ .zero zero n = zero , r-zero
      Nat⊂⊤ ._ (suc x) n = , (r-suc (proj₂ (Nat⊂⊤ _ x n)))
      Nat⊂⊤ ._ (ne (inj x)) n = , (r-neu (proj₂ (x n)))

  Cand' : ∀ {T} -> Cand T -> (Nat ⇒ (T ⇒ T)) ⊂ ⊤
  Cand' d = A⇒B⊂⊤ Cand-Nat (Cand⇒ d d)

  lem0 : ∀ {dz ds n T} -> Cand T ->  dz ∈ T -> ds ∈ (Nat ⇒ (T ⇒ T))
   -> n ∈ Nat
   -> rec' dz , ds , n ∈ T
  lem0 dT Dz Ds zero = , (Dz , r-zero)
  lem0 dT Dz Ds (suc x) = lem1 x Ds (lem0 dT Dz Ds x)
  lem0 (dT1 , dT2) Dz Ds (ne (inj x)) =
    , (dT1 _ (inj (λ n → , r-rec (proj₂ (dT2 _ Dz n))
                                  (proj₂ (Cand' (dT1 , dT2) _ Ds n))
                                  (proj₂ (x n)))) , r-neu)

  s-rec : ∀{Γ tz ts tn T} -> Cand T ->
              Γ ⊨ tz ∶ T -> Γ ⊨ ts ∶ (Nat ⇒ (T ⇒ T)) -> Γ ⊨ tn ∶ Nat ->
              Γ ⊨ rec tz ts tn ∶ T
  s-rec dT dz ds dn ρ dρ with dz ρ dρ | ds ρ dρ | dn ρ dρ
  s-rec dT dz ds dn ρ dρ | dz' , Dz , ddz | ds' , Ds , dds | dn' , Dn , ddn with lem0 dT Dz Ds Dn
  ... | db , Db , ddb = , (Db , e-rec ddz dds ddn ddb)

  s-top : ∀{Γ T} -> (Γ ∷̂ T) ∋^ zero ∶ T
  s-top ._ (cons _ t) = , (t , le-top)

  s-pop : ∀{Γ T S v} -> Γ ∋^ v ∶ T ->  (Γ ∷̂ S) ∋^ (suc v) ∶ T
  s-pop dv ._ (cons x x₁) with dv _ x
  ... | v , V , ddv = v , (V , le-pop ddv)

  data _⊢_∶_ (Γ : ctx) : exp -> tp -> Set where
    t-zero : Γ ⊢ zero ∶ nat
    t-suc  : ∀{t} -> Γ ⊢ t ∶ nat -> Γ ⊢ suc t ∶ nat
    t-var  : ∀{v T} -> Γ ∋ v ∶ T -> Γ ⊢ ▹ v ∶ T
    t-lam  : ∀{S T t} -> (Γ :: S) ⊢ t ∶ T -> Γ ⊢ ƛ t ∶ (S >-> T)
    t-app  : ∀{S T r s} -> Γ ⊢ r ∶ (S >-> T) -> Γ ⊢ s ∶ S -> Γ ⊢ r · s ∶ T
    t-rec  : ∀{T tz ts tn} ->
             Γ ⊢ tz ∶ T -> Γ ⊢ ts ∶ (nat >-> (T >-> T)) -> Γ ⊢ tn ∶ nat ->
             Γ ⊢ rec tz ts tn ∶ T

  lem3 : ∀ T -> Cand ⟦ T ⟧t
  lem3 nat = Cand-Nat
  lem3 (T >-> T₁) = Cand⇒ (lem3 T) (lem3 T₁)

  var-soundness : ∀{Γ v T} -> Γ ∋ v ∶ T -> (⟦ Γ ⟧ctx) ∋^ v ∶ ⟦ T ⟧t
  var-soundness lc-top = s-top
  var-soundness (lc-pop dv) = s-pop (var-soundness dv)

  soundness : ∀{Γ t T} -> Γ ⊢ t ∶ T -> ⟦ Γ ⟧ctx ⊨ t ∶ ⟦ T ⟧t
  soundness t-zero = s-zero
  soundness (t-suc d) = s-suc (soundness d)
  soundness (t-var d) = s-var (var-soundness d)
  soundness (t-lam d) = s-lam (soundness d)
  soundness (t-app d d₁) = s-app (soundness d) (soundness d₁)
  soundness (t-rec {T} d d₁ d₂) = s-rec (lem3 T) (soundness d) (soundness d₁) (soundness d₂)

  corollary : ∀ {Γ t T} -> Γ ⊢ t ∶ T -> ∃ (λ b -> ⟦ t ⟧ {!!} ↘ b)
  corollary d with soundness d nil {!nil!}
  ... | b , (_ , db) = b , db

  --- TODO : implement the part with the initial environment (kinda like
  --- an identity env) called ρ_n by Andreas
-}
