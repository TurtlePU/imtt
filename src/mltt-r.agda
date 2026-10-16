open import Data.Fin.Base
    using (Fin; zero; suc; fromℕ<)
open import Data.Nat.Base
    using (ℕ; suc; pred; _⊔_; _≤_; _<_)
open import Data.List.Base using (List; []; _∷_; lookup)
open import Data.List.NonEmpty.Base
    using (List⁺; length; toList)
open import Data.Product.Base using (_×_; _,_; proj₁)

𝓛 : Set
𝓛 = ℕ

data Type (n : ℕ) (ns : List ℕ) : Set

infix 5 _,x:_
data Ctx : ℕ → List ℕ → Set where
  ε : Ctx 0 []
  _,x:_ :
    ∀ {n ns} → Ctx n ns → Type n ns → Ctx (suc n) ns
  _·_🔒 : ∀ {n ns} → 𝓛 → Ctx n ns → Ctx 0 (n ∷ ns)

data Termᶜ (n : ℕ) (ns : List ℕ) : Set

Levels : Set
Levels = List⁺ (𝓛 × 𝓛)

data Type n ns where
  𝓤 : 𝓛 → Type n ns
  El_[_] : 𝓛 → Termᶜ n ns → Type n ns
  ℕᵀ : 𝓛 → Type n ns
  Σᵀ : Type n ns → Type (suc n) ns → Type n ns
  Πᵀ : Type n ns → Type (suc n) ns → Type n ns
  𝓘 : Type n ns → Termᶜ n ns → Termᶜ n ns → Type n ns
  □_[_] : 𝓛 → Type 0 (n ∷ ns) → Type n ns
  ⟦_⟧ᵀ :
    Type 0 (n ∷ ns) → Levels → Termᶜ n ns → Type n ns

data Termᴵ (n : ℕ) : List ℕ → Set

data Termᶜ n ns where
  0ᵗ : Termᶜ n ns
  Sᵗ : Termᶜ n ns → Termᶜ n ns
  ⟨_,_⟩ : Termᶜ n ns → Termᶜ n ns → Termᶜ n ns
  λᵗ : Termᶜ (suc n) ns → Termᶜ n ns
  rflᵗ : Termᶜ n ns
  [_]🔒 : Termᶜ 0 (n ∷ ns) → Termᶜ n ns
  ~ : Termᴵ n ns → Termᶜ n ns

data Termᴵ n where
  `_ : ∀ {ns} → Fin n → Termᴵ n ns
  Uᵗ : ∀ {ns} → 𝓛 → Termᴵ n ns
  Nᵗ : ∀ {ns} → 𝓛 → Termᴵ n ns
  ind_on_⟨_,_⟩ :
    ∀ {ns} → Type (suc n) ns → Termᴵ n ns →
    Termᶜ n ns → Termᶜ n ns → Termᴵ n ns
  Σᵗ :
    ∀ {ns} → Termᴵ n ns → Termᴵ (suc n) ns → Termᴵ n ns
  π₁ π₂ : ∀ {ns} → Termᴵ n ns → Termᴵ n ns
  Πᵗ :
    ∀ {ns} → Termᴵ n ns → Termᴵ (suc n) ns → Termᴵ n ns
  _$_ : ∀ {ns} → Termᴵ n ns → Termᶜ n ns → Termᴵ n ns
  Idᵗ :
    ∀ {ns} → Termᴵ n ns →
    Termᶜ n ns → Termᶜ n ns → Termᴵ n ns
  Jᵗ : ∀ {ns} → Type (suc (suc n)) ns →
    Termᴵ n ns → Termᶜ n ns → Termᴵ n ns
  Boxᵗ : ∀ {ns} → 𝓛 → Termᴵ 0 (n ∷ ns) → Termᴵ n ns
  [_]🔓 : ∀ {m ms} → Termᴵ m ms → Termᴵ n (m ∷ ms)
  ⟦_⟧ᵗ :
    ∀ {ns} → Termᴵ 0 (n ∷ ns) → Levels → Termᴵ n ns
  _as_ : ∀ {ns} → Termᶜ n ns → Type n ns → Termᴵ n ns

data Map : List ℕ → List ℕ → Set where
  ιₘ : ∀ {ns} → Map ns ns
  _∧ₘ_ : ∀ {ms ns m n} → Map ms ns → (Fin m → Fin n) →
    Map (m ∷ ms) (n ∷ ns)

renameᴵ :
    ∀ {m ms n ns} → Map (m ∷ ms) (n ∷ ns) →
    Termᴵ m ms → Termᴵ n ns
renameᴵ x (` x₁) = {! !}
renameᴵ x (Uᵗ x₁) = {! !}
renameᴵ x (Nᵗ x₁) = {! !}
renameᴵ x ind x₁ on x₂ ⟨ x₃ , x₄ ⟩ = {! !}
renameᴵ x (Σᵗ x₁ x₂) = {! !}
renameᴵ x (π₁ x₁) = {! !}
renameᴵ x (π₂ x₁) = {! !}
renameᴵ x (Πᵗ x₁ x₂) = {! !}
renameᴵ x (x₁ $ x₂) = {! !}
renameᴵ x (Idᵗ x₁ x₂ x₃) = {! !}
renameᴵ x (Jᵗ x₁ x₂ x₃) = {! !}
renameᴵ x (Boxᵗ x₁ x₂) = {! !}
renameᴵ x [ x₁ ]🔓 = {! !}
renameᴵ x (⟦ x₁ ⟧ᵗ x₂) = {! !}
renameᴵ x (x₁ as x₂) = {! !}

data Sub : List ℕ → List ℕ → Set where
  ιₛ : ∀ {ns} → Sub ns ns
  _∧ₛ_ :
    ∀ {ms ns m n} → Sub ms ns → (Fin m → Termᴵ n ns) →
    Sub (m ∷ ms) (n ∷ ns)

replaceᶜ :
    ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) →
    Termᶜ m ms → Termᶜ n ns
replaceᶜ = ?

wk : ∀ {m ms n ns} →
    Sub (m ∷ ms) (n ∷ ns) →
    Sub (suc m ∷ ms) (suc n ∷ ns)
wk ιₛ = ιₛ
wk (f ∧ₛ g) = f ∧ₛ λ where
    zero → ` zero
    (suc n) → renameᴵ ? (g n)

replaceᵀ :
    ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) →
    Type m ms → Type n ns
replaceᵀ _ (𝓤 ℓ) = 𝓤 ℓ
replaceᵀ f El ℓ [ t ] = El ℓ [ replaceᶜ f t ]
replaceᵀ _ (ℕᵀ ℓ) = ℕᵀ ℓ
replaceᵀ f (Σᵀ S T) =
    Σᵀ (replaceᵀ f S) (replaceᵀ (wk f) T)
replaceᵀ f (Πᵀ S T) =
    Πᵀ (replaceᵀ f S) (replaceᵀ (wk f) T)
replaceᵀ f (𝓘 T t₁ t₂) =
    𝓘 (replaceᵀ f T) (replaceᶜ f t₁) (replaceᶜ f t₂)
replaceᵀ f □ ℓ [ T ] = □ ℓ [ replaceᵀ (f ∧ₛ λ ()) T ]
replaceᵀ f (⟦ T ⟧ᵀ Ls m) =
    ⟦ replaceᵀ (f ∧ₛ λ ()) T ⟧ᵀ Ls (replaceᶜ f m)

_[x:=_]ᵀ :
  ∀ {n ns} → Type (suc n) ns → Termᴵ n ns → Type n ns
T [x:= t ]ᵀ =
  replaceᵀ (ιₛ ∧ₛ λ { zero → t ; (suc i) → ` i }) T

infix 4 _⊢_·_∈ᵀ_
data _⊢_·_∈ᵀ_ {n ns} (Γ : Ctx n ns) (ℓ : 𝓛) :
    Type n ns → 𝓛 → Set

data ⊢_·_ (ℓ : 𝓛) : ∀ {n ns} → Ctx n ns → Set where
  WF-Nil :
    -------
    ⊢ ℓ · ε
  WF-Var : ∀ {n ns} (Γ : Ctx n ns) T κ →
    ⊢ ℓ · Γ → Γ ⊢ ℓ · T ∈ᵀ κ →
    --------------------------
         ⊢ ℓ · (Γ ,x: T)
  WF-Lock : ∀ {n ns} (Γ : Ctx n ns) κ →
       ⊢ κ · Γ →
    ----------------
    ⊢ ℓ · (κ · Γ 🔒)

infix 4 _⊢_·_∋ᵗ_
data _⊢_·_∋ᵗ_ {n ns} (Γ : Ctx n ns) (ℓ : 𝓛) :
    Termᶜ n ns → Type n ns → Set

𝓜 : ∀ {n ns} → Levels → Type n ns
𝓜 _ = 𝓤 0

data _⊢_·_∈ᵀ_ Γ ℓ where
  Level-El : ∀ t κ →
      Γ ⊢ ℓ · t ∋ᵗ 𝓤 κ →
    -----------------------
    Γ ⊢ ℓ · El κ [ t ] ∈ᵀ κ
  Level-Uni : ∀ κ →
          ⊢ ℓ · Γ →
    {--------------------} (κ < ℓ) →
     Γ ⊢ ℓ · 𝓤 κ ∈ᵀ suc κ
  Level-Nat : ∀ κ →
         ⊢ ℓ · Γ →
    {-----------------} (κ ≤ ℓ) →
     Γ ⊢ ℓ · ℕᵀ κ ∈ᵀ κ
  Level-Sigma : ∀ κ j S T →
    Γ ⊢ ℓ · S ∈ᵀ κ → Γ ,x: S ⊢ ℓ · T ∈ᵀ j →
    ---------------------------------------
            Γ ⊢ ℓ · Σᵀ S T ∈ᵀ κ ⊔ j
  Level-Pi : ∀ κ j S T →
    Γ ⊢ ℓ · S ∈ᵀ κ → Γ ,x: S ⊢ ℓ · T ∈ᵀ j →
    ---------------------------------------
            Γ ⊢ ℓ · Πᵀ S T ∈ᵀ κ ⊔ j
  Level-Id : ∀ κ T t₁ t₂ →
    Γ ⊢ ℓ · T ∈ᵀ κ → Γ ⊢ ℓ · t₁ ∋ᵗ T → Γ ⊢ ℓ · t₂ ∋ᵗ T →
    ----------------------------------------------------
                   Γ ⊢ ℓ · 𝓘 T t₁ t₂ ∈ᵀ κ
  Level-Box : ∀ κ j T →
     ℓ · Γ 🔒 ⊢ κ · T ∈ᵀ j →
    {-----------------------} (κ ≤ ℓ) →
     Γ ⊢ ℓ · □ κ [ T ] ∈ᵀ κ
  Level-TyInterp : ∀ T m Ls j →
              Γ ⊢ ℓ · m ∋ᵗ 𝓜 Ls →
     ℓ · Γ 🔒 ⊢ pred (length Ls) · T ∈ᵀ j →
    {--------------------------------------
              -------------------} (H : j < length Ls) →
    Γ ⊢ ℓ · ⟦ T ⟧ᵀ Ls m ∈ᵀ
        proj₁ (lookup (toList Ls) (fromℕ< H))

data _⊢_·_∋ᵗ_ Γ ℓ where
  Check-Zero : ∀ κ →
    Γ ⊢ ℓ · 0ᵗ ∋ᵗ ℕᵀ κ
  Check-Succ : ∀ κ t →
    Γ ⊢ ℓ · t ∋ᵗ ℕᵀ κ →
    --------------------
    Γ ⊢ ℓ · Sᵗ t ∋ᵗ ℕᵀ κ
  Check-Pair : ∀ s S t T →
    Γ ⊢ ℓ · s ∋ᵗ S → Γ ⊢ ℓ · t ∋ᵗ T [x:= s as S ]ᵀ →
    ------------------------------------------------
              Γ ⊢ ℓ · ⟨ s , t ⟩ ∋ᵗ Σᵀ S T
