open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Base using (List; length; lookup)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
open import Data.List.Relation.Unary.All using (All; reduce)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc; _>_; _≥_; _<_; _⊔_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst)
open import Relation.Nullary.Decidable.Core using (yes; no)

𝓦 : Set
𝓦 = Maybe ℕ × ℕ

unc : ℕ → 𝓦
unc = nothing ,_

[_]_ : ℕ → ℕ → 𝓦
[ m ] n = just m , n

Ix : 𝓦 → Set
Ix (_ , n) = Fin n

nxt : 𝓦 → 𝓦
nxt (m , n) = m , suc n

𝓛 : Set
𝓛 = ℕ

Levels : Set
Levels = List⁺ (𝓛 × 𝓛)

data Typeᴵ : 𝓦 → Set
data Termᶜ : 𝓦 → Set
data Termᴵ : 𝓦 → Set

data Typeᶜ : 𝓦 → Set where
    𝓤ᵀ : ∀ {w} (ℓ : 𝓛) → Typeᶜ w
    ℕᵀ : ∀ {w} → Typeᶜ w
    Σᵀ Πᵀ : ∀ {w} (T : Typeᶜ w) (U : Typeᶜ (nxt w)) → Typeᶜ w
    Idᵀ : ∀ {w} (T : Typeᶜ w) (t₁ t₂ : Termᶜ w) → Typeᶜ w
    convᵀ : ∀ {w} (T : Typeᴵ w) → Typeᶜ w
    □ᵀ : ∀ {n} (ℓ : 𝓛) (T : Typeᶜ ([ n ] 0)) → Typeᶜ (unc n)

data Typeᴵ where
    _at_ : ∀ {w} (T : Typeᶜ w) (ℓ : 𝓛) → Typeᴵ w
    El : ∀ {w} (t : Termᴵ w) → Typeᴵ w
    ⟦_⟧ᵀ :
        ∀ {n} (T : Typeᴵ ([ n ] 0)) (Ls : Levels) (M : Termᶜ (unc n)) →
        Typeᴵ (unc n)

data Termᶜ where
    𝓤ᵗ : ∀ {w} (ℓ : 𝓛) → Termᶜ w
    Idᵗ : ∀ {w} (t t₁ t₂ : Termᶜ w) → Termᶜ w
    ℕᵗ 0ᵗ rflᵗ : ∀ {w} → Termᶜ w
    Sᵗ : ∀ {w} → Termᶜ w → Termᶜ w
    Σᵗ Πᵗ : ∀ {w} (t : Termᶜ w) (u : Termᶜ (nxt w)) → Termᶜ w
    ⟨_,_⟩ : ∀ {w} (t u : Termᶜ w) → Termᶜ w
    λᵗ : ∀ {w} (t : Termᶜ (nxt w)) → Termᶜ w
    convᵗ : ∀ {w} (t : Termᴵ w) → Termᶜ w
    □ᵗ : ∀ {n} (ℓ : 𝓛) (t : Termᶜ ([ n ] 0)) → Termᶜ (unc n)
    🔒 : ∀ {n} (t : Termᶜ ([ n ] 0)) → Termᶜ (unc n)

data Termᴵ where
    `_ : ∀ {w} → Ix w → Termᴵ w
    ind_on_⟨_,_⟩ :
        ∀ {w} (T : Typeᶜ (nxt w)) (n : Termᴵ w) (z s : Termᶜ w) → Termᴵ w
    π₁ π₂ : ∀ {w} (t : Termᴵ w) → Termᴵ w
    _$_ : ∀ {w} (t : Termᴵ w) (u : Termᶜ w) → Termᴵ w
    Jᵗ : ∀ {w} (T : Typeᶜ (nxt (nxt w))) (i : Termᴵ w) (t : Termᶜ w) → Termᴵ w
    _as_ : ∀ {w} (t : Termᶜ w) (T : Typeᶜ w) → Termᴵ w
    🔓 : ∀ {m n} (t : Termᴵ (unc m)) → Termᴵ ([ m ] n)
    ⟦_⟧ᵗ :
        ∀ {n} (t : Termᴵ ([ n ] 0)) (Ls : Levels) (ℓ : 𝓛) (m : Termᶜ (unc n)) →
        Termᴵ (unc n)

data Map : 𝓦 → 𝓦 → Set where
    uncᵐ : ∀ {m n} (f : Fin m → Fin n) → Map (unc m) (unc n)
    [_]ᵐ_ :
        ∀ {m₁ n₁ m₂ n₂} (f : Fin m₁ → Fin m₂) (g : Fin n₁ → Fin n₂) →
        Map ([ m₁ ] n₁) ([ m₂ ] n₂)

_!ᵐ_ : ∀ {v w} → Map v w → Ix v → Ix w
uncᵐ f !ᵐ i = f i
([ _ ]ᵐ f) !ᵐ i = f i

wkᵐ : ∀ {v w} → Map v w → Map (nxt v) (nxt w)
wkᵐ (uncᵐ f) = uncᵐ λ { zero → zero ; (suc i) → suc (f i) }
wkᵐ ([ f ]ᵐ g) = [ f ]ᵐ λ { zero → zero ; (suc i) → suc (g i) }

renameᵀᴵ : ∀ {v w} → Map v w → Typeᴵ v → Typeᴵ w
renameᵗᶜ : ∀ {v w} → Map v w → Termᶜ v → Termᶜ w
renameᵗᴵ : ∀ {v w} → Map v w → Termᴵ v → Termᴵ w

renameᵀᶜ : ∀ {v w} → Map v w → Typeᶜ v → Typeᶜ w
renameᵀᶜ _ (𝓤ᵀ ℓ) = 𝓤ᵀ ℓ
renameᵀᶜ _ ℕᵀ = ℕᵀ
renameᵀᶜ m (Σᵀ T U) = Σᵀ (renameᵀᶜ m T) (renameᵀᶜ (wkᵐ m) U)
renameᵀᶜ m (Πᵀ T U) = Πᵀ (renameᵀᶜ m T) (renameᵀᶜ (wkᵐ m) U)
renameᵀᶜ m (Idᵀ T t₁ t₂) = Idᵀ (renameᵀᶜ m T) (renameᵗᶜ m t₁) (renameᵗᶜ m t₂)
renameᵀᶜ m (convᵀ T) = convᵀ (renameᵀᴵ m T)
renameᵀᶜ (uncᵐ f) (□ᵀ ℓ T) = □ᵀ ℓ (renameᵀᶜ ([ f ]ᵐ λ ()) T)

renameᵀᴵ m (T at ℓ) = renameᵀᶜ m T at ℓ
renameᵀᴵ m (El t) = El (renameᵗᴵ m t)
renameᵀᴵ (uncᵐ f) (⟦ T ⟧ᵀ Ls M) =
    ⟦ renameᵀᴵ ([ f ]ᵐ λ ()) T ⟧ᵀ Ls (renameᵗᶜ (uncᵐ f) M)

renameᵗᶜ _ (𝓤ᵗ ℓ) = 𝓤ᵗ ℓ
renameᵗᶜ m (Idᵗ t t₁ t₂) = Idᵗ (renameᵗᶜ m t) (renameᵗᶜ m t₁) (renameᵗᶜ m t₂)
renameᵗᶜ _ ℕᵗ = ℕᵗ
renameᵗᶜ _ 0ᵗ = 0ᵗ
renameᵗᶜ _ rflᵗ = rflᵗ
renameᵗᶜ m (Sᵗ t) = Sᵗ (renameᵗᶜ m t)
renameᵗᶜ m (Σᵗ t u) = Σᵗ (renameᵗᶜ m t) (renameᵗᶜ (wkᵐ m) u)
renameᵗᶜ m (Πᵗ t u) = Πᵗ (renameᵗᶜ m t) (renameᵗᶜ (wkᵐ m) u)
renameᵗᶜ m ⟨ t , u ⟩ = ⟨ renameᵗᶜ m t , renameᵗᶜ m u ⟩
renameᵗᶜ m (λᵗ t) = λᵗ (renameᵗᶜ (wkᵐ m) t)
renameᵗᶜ m (convᵗ t) = convᵗ (renameᵗᴵ m t)
renameᵗᶜ (uncᵐ f) (□ᵗ ℓ t) = □ᵗ ℓ (renameᵗᶜ ([ f ]ᵐ λ ()) t)
renameᵗᶜ (uncᵐ f) (🔒 t) = 🔒(renameᵗᶜ ([ f ]ᵐ λ ()) t)

renameᵗᴵ m (` x) = ` (m !ᵐ x)
renameᵗᴵ m ind T on t ⟨ z , s ⟩ =
    ind renameᵀᶜ (wkᵐ m) T on renameᵗᴵ m t ⟨ renameᵗᶜ m z , renameᵗᶜ m s ⟩
renameᵗᴵ m (π₁ t) = π₁ (renameᵗᴵ m t)
renameᵗᴵ m (π₂ t) = π₂ (renameᵗᴵ m t)
renameᵗᴵ m (t $ u) = renameᵗᴵ m t $ renameᵗᶜ m u
renameᵗᴵ m (Jᵗ T i t) =
    Jᵗ (renameᵀᶜ (wkᵐ (wkᵐ m)) T) (renameᵗᴵ m i) (renameᵗᶜ m t)
renameᵗᴵ m (t as T) = renameᵗᶜ m t as renameᵀᶜ m T
renameᵗᴵ ([ f ]ᵐ _) (🔓 t) = 🔓(renameᵗᴵ (uncᵐ f) t)
renameᵗᴵ (uncᵐ f) (⟦ t ⟧ᵗ Ls ℓ m) = ⟦ renameᵗᴵ ([ f ]ᵐ λ ()) t ⟧ᵗ Ls ℓ (renameᵗᶜ ? m)

↑ᵐ : ∀ {w} → Map w (nxt w)
↑ᵐ {just _ , _} = [ (λ z → z) ]ᵐ suc
↑ᵐ {nothing , _} = uncᵐ suc

↑ᵀᶜ : ∀ {w} → Typeᶜ w → Typeᶜ (nxt w)
↑ᵀᶜ = renameᵀᶜ ↑ᵐ

↑ᵗᶜ : ∀ {w} → Termᶜ w → Termᶜ (nxt w)
↑ᵗᶜ = renameᵗᶜ ↑ᵐ

infixl 5 _,x:_
data Ctx : 𝓦 → Set where
    ε : Ctx (unc 0)
    _,x:_ : ∀ {w} (Γ : Ctx w) (T : Typeᶜ w) → Ctx (nxt w)
    _[_]🔒 : ∀ {n} (Γ : Ctx (unc n)) (ℓ : 𝓛) → Ctx ([ n ] 0)

🔓ᶜ : ∀ {m n} → Ctx ([ m ] n) → Ctx (unc m)
🔓ᶜ (Γ ,x: _) = 🔓ᶜ Γ
🔓ᶜ (Γ [ _ ]🔒) = Γ

_!!_ : ∀ {w} → Ctx w → Ix w → Typeᶜ w
(_ ,x: T) !! zero = ↑ᵀᶜ T
(Γ ,x: _) !! suc i = ↑ᵀᶜ (Γ !! i)

data Sub : 𝓦 → 𝓦 → Set where
    uncˢ : ∀ {m n} (f : Fin m → Termᴵ (unc n)) → Sub (unc m) (unc n)
    [_]ˢ_ :
        ∀ {m₁ m₂ n₁ n₂} (f : Fin m₁ → Termᴵ (unc n₁))
        (g : Fin m₂ → Termᴵ ([ n₁ ] n₂)) → Sub ([ m₁ ] m₂) ([ n₁ ] n₂)

_!ˢ_ : ∀ {v w} → Sub v w → Ix v → Termᴵ w
uncˢ f !ˢ i = f i
([ _ ]ˢ g) !ˢ i = g i

wkˢ : ∀ {v w} → Sub v w → Sub (nxt v) (nxt w)
wkˢ (uncˢ f) = uncˢ λ where
    zero → ` zero
    (suc i) → renameᵗᴵ (uncᵐ suc) (f i)
wkˢ ([ f ]ˢ g) = [ f ]ˢ λ where
    zero → ` zero
    (suc i) → renameᵗᴵ ([ (λ z → z) ]ᵐ suc) (g i)

replaceᵀᴵ : ∀ {v w} → Sub v w → Typeᴵ v → Typeᴵ w
replaceᵗᶜ : ∀ {v w} → Sub v w → Termᶜ v → Termᶜ w
replaceᵗᴵ : ∀ {v w} → Sub v w → Termᴵ v → Termᴵ w

replaceᵀᶜ : ∀ {v w} → Sub v w → Typeᶜ v → Typeᶜ w
replaceᵀᶜ _ (𝓤ᵀ ℓ) = 𝓤ᵀ ℓ
replaceᵀᶜ _ ℕᵀ = ℕᵀ
replaceᵀᶜ s (Σᵀ T U) = Σᵀ (replaceᵀᶜ s T) (replaceᵀᶜ (wkˢ s) U)
replaceᵀᶜ s (Πᵀ T U) = Πᵀ (replaceᵀᶜ s T) (replaceᵀᶜ (wkˢ s) U)
replaceᵀᶜ s (Idᵀ T t₁ t₂) =
    Idᵀ (replaceᵀᶜ s T) (replaceᵗᶜ s t₁) (replaceᵗᶜ s t₂)
replaceᵀᶜ s (convᵀ T) = convᵀ (replaceᵀᴵ s T)
replaceᵀᶜ (uncˢ f) (□ᵀ ℓ T) = □ᵀ ℓ (replaceᵀᶜ ([ f ]ˢ λ ()) T)

replaceᵀᴵ s (T at ℓ) = replaceᵀᶜ s T at ℓ
replaceᵀᴵ s (El t) = El (replaceᵗᴵ s t)
replaceᵀᴵ (uncˢ f) (⟦ T ⟧ᵀ Ls M) =
    ⟦ replaceᵀᴵ ([ f ]ˢ λ ()) T ⟧ᵀ Ls (replaceᵗᶜ (uncˢ f) M)

replaceᵗᶜ _ (𝓤ᵗ ℓ) = 𝓤ᵗ ℓ
replaceᵗᶜ s (Idᵗ t t₁ t₂) =
    Idᵗ (replaceᵗᶜ s t) (replaceᵗᶜ s t₁) (replaceᵗᶜ s t₂)
replaceᵗᶜ _ ℕᵗ = ℕᵗ
replaceᵗᶜ _ 0ᵗ = 0ᵗ
replaceᵗᶜ _ rflᵗ = rflᵗ
replaceᵗᶜ s (Sᵗ t) = Sᵗ (replaceᵗᶜ s t)
replaceᵗᶜ s (Σᵗ t u) = Σᵗ (replaceᵗᶜ s t) (replaceᵗᶜ (wkˢ s) u)
replaceᵗᶜ s (Πᵗ t u) = Πᵗ (replaceᵗᶜ s t) (replaceᵗᶜ (wkˢ s) u)
replaceᵗᶜ s ⟨ t , u ⟩ = ⟨ replaceᵗᶜ s t , replaceᵗᶜ s u ⟩
replaceᵗᶜ s (λᵗ t) = λᵗ (replaceᵗᶜ (wkˢ s) t)
replaceᵗᶜ s (convᵗ t) = convᵗ (replaceᵗᴵ s t)
replaceᵗᶜ (uncˢ f) (□ᵗ ℓ t) = □ᵗ ℓ (replaceᵗᶜ ([ f ]ˢ λ ()) t)
replaceᵗᶜ (uncˢ f) (🔒 t) = 🔒(replaceᵗᶜ ([ f ]ˢ λ ()) t)

replaceᵗᴵ s (` x) = s !ˢ x
replaceᵗᴵ s ind T on t ⟨ z , s₁ ⟩ =
    ind replaceᵀᶜ (wkˢ s) T on replaceᵗᴵ s t ⟨ replaceᵗᶜ s z , replaceᵗᶜ s s₁ ⟩
replaceᵗᴵ s (π₁ t) = π₁ (replaceᵗᴵ s t)
replaceᵗᴵ s (π₂ t) = π₂ (replaceᵗᴵ s t)
replaceᵗᴵ s (t $ u) = replaceᵗᴵ s t $ replaceᵗᶜ s u
replaceᵗᴵ s (Jᵗ T i t) =
    Jᵗ (replaceᵀᶜ (wkˢ (wkˢ s)) T) (replaceᵗᴵ s i) (replaceᵗᶜ s t)
replaceᵗᴵ s (t as T) = replaceᵗᶜ s t as replaceᵀᶜ s T
replaceᵗᴵ ([ f ]ˢ _) (🔓 t) = 🔓(replaceᵗᴵ (uncˢ f) t)
replaceᵗᴵ (uncˢ f) (⟦ t ⟧ᵗ Ls ℓ m) = ⟦ replaceᵗᴵ ([ f ]ˢ λ ()) t ⟧ᵗ Ls ℓ (replaceᵗᶜ ? m)

ty : ∀ {w} → 𝓛 → Termᶜ w → Typeᶜ w
ty ℓ t = convᵀ (El (t as 𝓤ᵀ ℓ))

𝔹 : 𝓛 → Set
𝔹 ℓ = Fin (suc ℓ)

to𝔹 : ∀ {ℓ κ} → (ℓ ≥ κ) → 𝔹 ℓ
to𝔹 H = fromℕ< (Data.Nat.Base.s≤s H)

_≥∀_ : 𝓛 → Levels → Set
ℓ ≥∀ Ls = All (λ (j , κ) → ℓ ≥ j × ℓ ≥ κ) (toList Ls)

lb : Levels → 𝓛
lb (_ ∷ Ls) = length Ls

lkp : ∀ {ℓ} (Ls : Levels) → 𝔹 (lb Ls) → ℓ ≥∀ Ls → 𝔹 ℓ
lkp Ls i all =
    lookup (reduce (λ (H , _) → to𝔹 H) all) (subst Fin (eq (toList Ls) all) i)
  where
    eq :
        ∀ {A B : Set} {P : A → Set} {f : ∀ {x} → P x → B} (xs : List A)
        (ys : All P xs) → length xs ≡ length (reduce f ys)
    eq List.[] All.[] = _≡_.refl
    eq (_ List.∷ xs) (_ All.∷ ys) = cong suc (eq xs ys)

𝓜 : ∀ {w} → Levels → Typeᶜ w
𝓜 = ?

infix 4 _⊢_ _⊢_≥ℓ_ _⊢ℓ_^_≡_ _⊢_^_∋_ _⊢_^_∈_ _⊢_∋_≡β_ _⊢_<:_
data _⊢_≥ℓ_ : ∀ {w} → Ctx w → 𝓛 → Typeᶜ w → Set
data _⊢ℓ_^_≡_ : ∀ {w} → Ctx w → Typeᴵ w → (ℓ : 𝓛) → 𝔹 ℓ → Set
data _⊢_^_∋_ : ∀ {w} → Ctx w → Typeᶜ w → 𝓛 → Termᶜ w → Set
data _⊢_^_∈_ : ∀ {w} → Ctx w → Termᴵ w → 𝓛 → Typeᶜ w → Set
data _⊢_∋_≡β_ {w} (Γ : Ctx w) (T : Typeᶜ w) (t₁ t₂ : Termᶜ w) : Set where
data _⊢_<:_ {w} (Γ : Ctx w) (T U : Typeᶜ w) : Set where

data _⊢_ (ℓ : 𝓛) : ∀ {w} → Ctx w → Set where
    WF-Nil : ℓ ⊢ ε
    WF-Var : ∀ {w T} {Γ : Ctx w} →
        ℓ ⊢ Γ → Γ ⊢ ℓ ≥ℓ T →
        --------------------
            ℓ ⊢ Γ ,x: T
    WF-Lock : ∀ {κ n} {Γ : Ctx (unc n)} →
           κ ⊢ Γ →
        -------------
        ℓ ⊢ Γ [ κ ]🔒

data _⊢_≥ℓ_ where
    Level-Uni : ∀ {w κ ℓ} {Γ : Ctx w} →
           ℓ ⊢ Γ →
       {-------------} (ℓ > κ) →
        Γ ⊢ ℓ ≥ℓ 𝓤ᵀ κ
    Level-Nat : ∀ {w ℓ} {Γ : Ctx w} →
          ℓ ⊢ Γ →
        -----------
        Γ ⊢ ℓ ≥ℓ ℕᵀ
    Level-Sigma : ∀ {w ℓ T U} {Γ : Ctx w} →
        Γ ⊢ ℓ ≥ℓ T → Γ ,x: T ⊢ ℓ ≥ℓ U →
        -------------------------------
               Γ ⊢ ℓ ≥ℓ Σᵀ T U
    Level-Pi : ∀ {w ℓ T U} {Γ : Ctx w} →
        Γ ⊢ ℓ ≥ℓ T → Γ ,x: T ⊢ ℓ ≥ℓ U →
        -------------------------------
               Γ ⊢ ℓ ≥ℓ Πᵀ T U
    Level-Id : ∀ {w ℓ T t₁ t₂} {Γ : Ctx w} →
        Γ ⊢ ℓ ≥ℓ T → Γ ⊢ T ^ ℓ ∋ t₁ → Γ ⊢ T ^ ℓ ∋ t₂ →
        ----------------------------------------------
                   Γ ⊢ ℓ ≥ℓ Idᵀ T t₁ t₂
    Level-Conv : ∀ {w ℓ κ T} {Γ : Ctx w} →
        Γ ⊢ℓ T ^ ℓ ≡ κ →
        ----------------
        Γ ⊢ ℓ ≥ℓ convᵀ T
    Level-Box : ∀ {n κ ℓ T} {Γ : Ctx (unc n)} →
        Γ [ ℓ ]🔒 ⊢ κ ≥ℓ T →
        --------------------
          Γ ⊢ ℓ ≥ℓ □ᵀ κ T

data _⊢ℓ_^_≡_ where
    Level-At : ∀ {w T κ ℓ} {Γ : Ctx w} →
             Γ ⊢ κ ≥ℓ T →
       {-----------------------} (H : ℓ ≥ κ) →
        Γ ⊢ℓ T at κ ^ ℓ ≡ to𝔹 H
    Level-El : ∀ {w t κ ℓ} {Γ : Ctx w} →
         Γ ⊢ t ^ ℓ ∈ 𝓤ᵀ κ →
       {---------------------} (H : ℓ ≥ κ) →
        Γ ⊢ℓ El t ^ ℓ ≡ to𝔹 H
    Level-TyInterp : ∀ {n T Ls κ ℓ m} {Γ : Ctx (unc n)} →
        Γ [ ℓ ]🔒 ⊢ℓ T ^ lb Ls ≡ κ → Γ ⊢ 𝓜 Ls ^ ℓ ∋ m →
       {-----------------------------------------------} (H : ℓ ≥∀ Ls) →
               Γ ⊢ℓ ⟦ T ⟧ᵀ Ls m ^ ℓ ≡ lkp Ls κ H

infixl 20 _[x:=_]ᵀ
_[x:=_]ᵀ : ∀ {w} → Typeᶜ (nxt w) → Termᴵ w → Typeᶜ w
_[x:=_]ᵀ {nothing , _} T t = replaceᵀᶜ (uncˢ λ { zero → t ; (suc i) → ` i }) T
_[x:=_]ᵀ {just _ , _} T t = replaceᵀᶜ ([ `_ ]ˢ λ { zero → t ; (suc i) → ` i }) T

data _⊢_^_∋_ where
    Check-Uni : ∀ {w j κ ℓ} {Γ : Ctx w} →
              ℓ ⊢ Γ →
       {-------------------} (j > κ) →
        Γ ⊢ 𝓤ᵀ j ^ ℓ ∋ 𝓤ᵗ κ
    Check-Id : ∀ {w κ ℓ t t₁ t₂} {Γ : Ctx w} →
        Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ t → Γ ⊢ ty κ t ^ ℓ ∋ t₁ → Γ ⊢ ty κ t ^ ℓ ∋ t₂ →
        --------------------------------------------------------------
                        Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ Idᵗ t t₁ t₂
    Check-Nat : ∀ {w κ ℓ} {Γ : Ctx w} →
             ℓ ⊢ Γ →
        -----------------
        Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ ℕᵗ
    Check-Zero : ∀ {w ℓ} {Γ : Ctx w} →
            ℓ ⊢ Γ →
        ---------------
        Γ ⊢ ℕᵀ ^ ℓ ∋ 0ᵗ
    Checl-Refl : ∀ {w ℓ T t₁ t₂} {Γ : Ctx w} →
            Γ ⊢ T ∋ t₁ ≡β t₂ →
        --------------------------
        Γ ⊢ Idᵀ T t₁ t₂ ^ ℓ ∋ rflᵗ
    Check-Succ : ∀ {w ℓ t} {Γ : Ctx w} →
        Γ ⊢ ℕᵀ ^ ℓ ∋ t →
        -----------------
        Γ ⊢ ℕᵀ ^ ℓ ∋ Sᵗ t
    Check-Sigma : ∀ {w κ ℓ t u} {Γ : Ctx w} →
        Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ t → Γ ,x: ty ℓ t ⊢ 𝓤ᵀ κ ^ ℓ ∋ u →
        ------------------------------------------------
                     Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ Σᵗ t u
    Check-Pi : ∀ {w κ ℓ t u} {Γ : Ctx w} →
        Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ t → Γ ,x: ty ℓ t ⊢ 𝓤ᵀ κ ^ ℓ ∋ u →
        ------------------------------------------------
                     Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ Πᵗ t u
    Check-Pair : ∀ {w ℓ T U t u} {Γ : Ctx w} →
        Γ ⊢ T ^ ℓ ∋ t → Γ ⊢ U [x:= t as T ]ᵀ ^ ℓ ∋ u →
        ------------------------------------------------
                  Γ ⊢ Σᵀ T U ^ ℓ ∋ ⟨ t , u ⟩
    Check-Abs : ∀ {w ℓ T U u} {Γ : Ctx w} →
        Γ ,x: T ⊢ U ^ ℓ ∋ u →
        ---------------------
        Γ ⊢ Πᵀ T U ^ ℓ ∋ λᵗ u
    Check-Conv : ∀ {w ℓ T T' t} {Γ : Ctx w} →
        Γ ⊢ t ^ ℓ ∈ T' → Γ ⊢ T' <: T →
        ------------------------------
              Γ ⊢ T ^ ℓ ∋ convᵗ t
    Check-Box : ∀ {n j κ ℓ t} {Γ : Ctx (unc n)} →
        Γ [ ℓ ]🔒 ⊢ 𝓤ᵀ κ ^ j ∋ t →
        --------------------------
          Γ ⊢ 𝓤ᵀ κ ^ ℓ ∋ □ᵗ j t
    Check-Lock : ∀ {n κ ℓ T t} {Γ : Ctx (unc n)} →
        Γ [ ℓ ]🔒 ⊢ T ^ κ ∋ t →
        -----------------------
         Γ ⊢ □ᵀ κ T ^ ℓ ∋ 🔒 t

infix 5 _⇒_
_⇒_ : ∀ {w} → Typeᶜ w → Typeᶜ w → Typeᶜ w
T ⇒ U = Πᵀ T (↑ᵀᶜ U)

_[_] : ∀ {v w} → Typeᶜ v → Sub v w → Typeᶜ w
T [ σ ] = replaceᵀᶜ σ T

pick : ∀ {m n} → Fin n → Termᴵ (m , n) → Fin n → Termᴵ (m , n)
pick i t j with i ≟ j
... | yes _ = t
... | no _ = ` j

_:=_ : ∀ {w} → Ix w → Termᴵ w → Sub w w
_:=_ {just _ , _} i t = [ `_ ]ˢ (pick i t)
_:=_ {nothing , _} i t = uncˢ (pick i t)

Sᵗᴵ : ∀ {w} → Termᴵ w → Termᴵ w
Sᵗᴵ t = Sᵗ (convᵗ t) as ℕᵀ

↓ : ∀ {m n} → Typeᶜ ([ m ] 0) → Typeᶜ ([ m ] n)
↓ = renameᵀᶜ ([ (λ z → z) ]ᵐ λ ())

data _⊢_^_∈_ where
    Infer-Var : ∀ {w ℓ i} {Γ : Ctx w} →
               ℓ ⊢ Γ →
        --------------------
        Γ ⊢ ` i ^ ℓ ∈ Γ !! i
    Infer-Ind : ∀ {w ℓ T n z s} {Γ : Ctx w} →
        Γ ,x: ℕᵀ ⊢ ℓ ≥ℓ T →
        Γ ⊢ n ^ ℓ ∈ ℕᵀ →
        Γ ⊢ T [x:= 0ᵗ as ℕᵀ ]ᵀ ^ ℓ ∋ z →
        Γ ⊢ Πᵀ ℕᵀ (T ⇒ T [ zero := Sᵗᴵ (` zero) ]) ^ ℓ ∋ s →
        ----------------------------------------------------
        Γ ⊢ ind T on n ⟨ z , s ⟩ ^ ℓ ∈ T [x:= n ]ᵀ
    Infer-Proj₁ : ∀ {w ℓ t T U} {Γ : Ctx w} →
        Γ ⊢ t ^ ℓ ∈ Σᵀ T U →
        --------------------
          Γ ⊢ π₁ t ^ ℓ ∈ T
    Infer-Proj₂ : ∀ {w ℓ t T U} {Γ : Ctx w} →
            Γ ⊢ t ^ ℓ ∈ Σᵀ T U →
        -----------------------------
        Γ ⊢ π₂ t ^ ℓ ∈ U [x:= π₁ t ]ᵀ
    Infer-App : ∀ {w ℓ t u T U} {Γ : Ctx w} →
        Γ ⊢ t ^ ℓ ∈ Πᵀ U T → Γ ⊢ U ^ ℓ ∋ u →
        ------------------------------------
          Γ ⊢ t $ u ^ ℓ ∈ T [x:= u as U ]ᵀ
    Infer-J : ∀ {w ℓ T t₁ t₂ U i u} {Γ : Ctx w} →
        Γ ⊢ i ^ ℓ ∈ Idᵀ T t₁ t₂ →
        Γ ,x: T ,x: Idᵀ (↑ᵀᶜ T) (↑ᵗᶜ t₁) (convᵗ (` zero)) ⊢ ℓ ≥ℓ U →
        Γ ⊢ U [x:= ↑ᵗᶜ t₁ as ↑ᵀᶜ T ]ᵀ [x:= rflᵗ as Idᵀ T t₁ t₁ ]ᵀ ^ ℓ ∋ u →
        -------------------------------------------------------------------
        Γ ⊢ Jᵗ U i u ^ ℓ ∈ U [x:= ↑ᵗᶜ t₂ as ↑ᵀᶜ T ]ᵀ [x:= i ]ᵀ
    Infer-As : ∀ {w ℓ t T} {Γ : Ctx w} →
         Γ ⊢ T ^ ℓ ∋ t →
        ------------------
        Γ ⊢ t as T ^ ℓ ∈ T
    Infer-Unlock : ∀ {m n κ ℓ t T} {Γ : Ctx ([ m ] n)} →
        🔓ᶜ Γ ⊢ t ^ ℓ ∈ □ᵀ κ T →
        ------------------------
           Γ ⊢ 🔓 t ^ ℓ ∈ ↓ T
    Infer-Interp : ∀ {n Ls κ ℓ t T m} {Γ : Ctx (unc n)} →
        Γ [ ℓ ]🔒 ⊢ t ^ lb Ls ∈ T → Γ [ ℓ ]🔒 ⊢ κ ≥ℓ T →
        -- FIXME: add check for m
        {- -} (ℓ ≥∀ Ls × lb Ls ≥ κ) →
        Γ ⊢ ⟦ t ⟧ᵗ Ls κ m ^ ℓ ∈ convᵀ (⟦ T at κ ⟧ᵀ Ls m)
