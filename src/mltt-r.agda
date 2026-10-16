open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_)

record 𝓦 : Set where
  constructor [_]_
  field ext int : ℕ

Ix : 𝓦 → Set
Ix ([ m ] n) = Fin n

nxt : 𝓦 → 𝓦
nxt ([ m ] n) = [ m ] (suc n)

𝓛 : Set
𝓛 = ℕ

Levels : Set
Levels = List (𝓛 × 𝓛)

data Typeᴵ : 𝓦 → Set
data Termᶜ : 𝓦 → Set
data Termᴵ : 𝓦 → Set

data Typeᶜ : 𝓦 → Set where
    𝓤ᵀ : ∀ {w} (ℓ : 𝓛) → Typeᶜ w
    ℕᵀ : ∀ {w} → Typeᶜ w
    Σᵀ Πᵀ : ∀ {w} (T : Typeᶜ w) (U : Typeᶜ (nxt w)) → Typeᶜ w
    Idᵀ : ∀ {w} (T : Typeᶜ w) (t₁ t₂ : Termᶜ w) → Typeᶜ w
    convᵀ : ∀ {w} (T : Typeᴵ w) → Typeᶜ w
    □ᵀ : ∀ {n} (T : Typeᶜ ([ n ] 0)) → Typeᶜ ([ 0 ] n)

data Typeᴵ where
    _at_ : ∀ {w} (T : Typeᶜ w) (ℓ : 𝓛) → Typeᴵ w
    El : ∀ {w} (t : Termᴵ w) → Typeᴵ w
    ⟦_⟧ᵀ :
        ∀ {n} (T : Typeᴵ ([ n ] 0)) (Ls : Levels) (M : Termᶜ ([ 0 ] n)) →
        Typeᴵ ([ 0 ] n)

data Termᶜ where
    𝓤ᵗ : ∀ {w} (ℓ : 𝓛) → Termᶜ w
    Idᵗ : ∀ {w} (t t₁ t₂ : Termᶜ w) → Termᶜ w
    ℕᵗ 0ᵗ rflᵗ : ∀ {w} → Termᶜ w
    Sᵗ : ∀ {w} → Termᶜ w → Termᶜ w
    Σᵗ Πᵗ : ∀ {w} (t : Termᶜ w) (u : Termᶜ (nxt w)) → Termᶜ w
    ⟨_,_⟩ : ∀ {w} (t u : Termᶜ w) → Termᶜ w
    λᵗ : ∀ {w} (t : Termᶜ (nxt w)) → Termᶜ w
    convᵗ : ∀ {w} (t : Termᴵ w) → Termᶜ w
    □ᵗ [_]🔒 : ∀ {n} (t : Termᶜ ([ n ] 0)) → Termᶜ ([ 0 ] n)

data Termᴵ where
    `_ : ∀ {w} → Ix w → Termᴵ w
    ind_on_⟨_,_⟩ :
        ∀ {w} (T : Typeᶜ (nxt w)) (n : Termᴵ w) (z s : Termᶜ w) → Termᴵ w
    π₁ π₂ : ∀ {w} (t : Termᴵ w) → Termᴵ w
    _$_ : ∀ {w} (t : Termᴵ w) (u : Termᶜ w) → Termᴵ w
    Jᵗ : ∀ {w} (T : Typeᶜ (nxt (nxt w))) (i : Termᴵ w) (t : Termᶜ w) → Termᴵ w
    _as_ : ∀ {w} (t : Termᶜ w) (T : Typeᶜ w) → Termᴵ w
    [_]🔓 : ∀ {m n} (t : Termᴵ ([ 0 ] m)) → Termᴵ ([ m ] n)
    ⟦_⟧ᵗ : ∀ {n} (t : Termᴵ ([ n ] 0)) (Ls : Levels) → Termᴵ ([ 0 ] n)

infix 5 _,x:_
data Ctx : 𝓦 → Set where
    ε : Ctx ([ 0 ] 0)
    _,x:_ : ∀ {w} → Ctx w → Typeᶜ w → Ctx (nxt w)
    _🔒 : ∀ {n} → Ctx ([ 0 ] n) → Ctx ([ n ] 0)

--
--data Map : List ℕ → List ℕ → Set where
--  ιₘ : ∀ {ns} → Map ns ns
--  _∧ₘ_ : ∀ {ms ns m n} → Map ms ns → (Fin m → Fin n) → Map (m ∷ ms) (n ∷ ns)
--
--wkᴹ : ∀ {m ms n ns} → Map (m ∷ ms) (n ∷ ns) → Map (suc m ∷ ms) (suc n ∷ ns)
--wkᴹ ιₘ = ιₘ
--wkᴹ (m ∧ₘ f) = m ∧ₘ λ where
--    zero → zero
--    (suc i) → suc (f i)
--
--renameᴵ : ∀ {m ms n ns} → Map (m ∷ ms) (n ∷ ns) → Termᴵ m ms → Termᴵ n ns
--
--renameᶜ : ∀ {m ms n ns} → Map (m ∷ ms) (n ∷ ns) → Termᶜ m ms → Termᶜ n ns
--renameᶜ _ 0ᵗ = 0ᵗ
--renameᶜ m (Sᵗ t) = Sᵗ (renameᶜ m t)
--renameᶜ m ⟨ t , u ⟩ = ⟨ renameᶜ m t , renameᶜ m u ⟩
--renameᶜ m (λᵗ t) = λᵗ (renameᶜ (wkᴹ m) t)
--renameᶜ _ rflᵗ = rflᵗ
--renameᶜ m [ t ]🔒 = [ renameᶜ (m ∧ₘ λ ()) t ]🔒
--renameᶜ m (~ t) = ~ (renameᴵ m t)
--
--renameᵀ : ∀ {m ms n ns} → Map (m ∷ ms) (n ∷ ns) → Type m ms → Type n ns
--renameᵀ _ (𝓤 ℓ) = 𝓤 ℓ
--renameᵀ m El ℓ [ t ] = El ℓ [ renameᶜ m t ]
--renameᵀ _ (ℕᵀ ℓ) = ℕᵀ ℓ
--renameᵀ m (Σᵀ T U) = Σᵀ (renameᵀ m T) (renameᵀ (wkᴹ m) U)
--renameᵀ m (Πᵀ T U) = Πᵀ (renameᵀ m T) (renameᵀ (wkᴹ m) U)
--renameᵀ m (𝓘 T t₁ t₂) = 𝓘 (renameᵀ m T) (renameᶜ m t₁) (renameᶜ m t₂)
--renameᵀ m □ ℓ [ T ] = □ ℓ [ renameᵀ (m ∧ₘ λ ()) T ]
--renameᵀ m (⟦ T ⟧ᵀ ℓ M) = ⟦ renameᵀ (m ∧ₘ λ ()) T ⟧ᵀ ℓ (renameᶜ m M)
--
--renameᴵ _ (Uᵗ ℓ) = Uᵗ ℓ
--renameᴵ _ (Nᵗ ℓ) = Nᵗ ℓ
--renameᴵ m ind T on t ⟨ z , s ⟩ =
--  ind renameᵀ (wkᴹ m) T on renameᴵ m t ⟨ renameᶜ m z , renameᶜ m s ⟩
--renameᴵ m (Σᵗ t u) = Σᵗ (renameᴵ m t) (renameᴵ (wkᴹ m) u)
--renameᴵ m (π₁ t) = π₁ (renameᴵ m t)
--renameᴵ m (π₂ t) = π₂ (renameᴵ m t)
--renameᴵ m (Πᵗ t u) = Πᵗ (renameᴵ m t) (renameᴵ (wkᴹ m) u)
--renameᴵ m (t $ u) = renameᴵ m t $ renameᶜ m u
--renameᴵ m (Idᵗ T t₁ t₂) = Idᵗ (renameᴵ m T) (renameᶜ m t₁) (renameᶜ m t₂)
--renameᴵ m (Jᵗ T i t) = Jᵗ (renameᵀ (wkᴹ (wkᴹ m)) T) (renameᴵ m i) (renameᶜ m t)
--renameᴵ m (Boxᵗ ℓ t) = Boxᵗ ℓ (renameᴵ (m ∧ₘ λ ()) t)
--renameᴵ m (⟦ t ⟧ᵗ ℓ) = ⟦ renameᴵ (m ∧ₘ λ ()) t ⟧ᵗ ℓ
--renameᴵ m (t as T) = renameᶜ m t as renameᵀ m T
--renameᴵ ιₘ (` x) = ` x
--renameᴵ (_ ∧ₘ f) (` x) = ` (f x)
--renameᴵ ιₘ [ t ]🔓 = [ t ]🔓
--renameᴵ (ιₘ ∧ₘ _) [ t ]🔓 = [ t ]🔓
--renameᴵ ((m ∧ₘ f) ∧ₘ _) [ t ]🔓 = [ renameᴵ (m ∧ₘ f) t ]🔓
--
--data Sub : List ℕ → List ℕ → Set where
--  ιₛ : ∀ {ns} → Sub ns ns
--  _∧ₛ_ :
--    ∀ {ms ns m n} → Sub ms ns → (Fin m → Termᴵ n ns) → Sub (m ∷ ms) (n ∷ ns)
--
--wkˢ : ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) → Sub (suc m ∷ ms) (suc n ∷ ns)
--wkˢ ιₛ = ιₛ
--wkˢ (f ∧ₛ g) = f ∧ₛ λ where
--    zero → ` zero
--    (suc n) → renameᴵ (ιₘ ∧ₘ suc) (g n)
--
--replaceᴵ : ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) → Termᴵ m ms → Termᴵ n ns
--
--replaceᶜ : ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) → Termᶜ m ms → Termᶜ n ns
--replaceᶜ _ 0ᵗ = 0ᵗ
--replaceᶜ s (Sᵗ t) = Sᵗ (replaceᶜ s t)
--replaceᶜ s ⟨ t , u ⟩ = ⟨ replaceᶜ s t , replaceᶜ s u ⟩
--replaceᶜ s (λᵗ t) = λᵗ (replaceᶜ (wkˢ s) t)
--replaceᶜ _ rflᵗ = rflᵗ
--replaceᶜ s [ t ]🔒 = [ replaceᶜ (s ∧ₛ λ ()) t ]🔒
--replaceᶜ s (~ t) = ~ (replaceᴵ s t)
--
--replaceᵀ : ∀ {m ms n ns} → Sub (m ∷ ms) (n ∷ ns) → Type m ms → Type n ns
--replaceᵀ _ (𝓤 ℓ) = 𝓤 ℓ
--replaceᵀ f El ℓ [ t ] = El ℓ [ replaceᶜ f t ]
--replaceᵀ _ (ℕᵀ ℓ) = ℕᵀ ℓ
--replaceᵀ f (Σᵀ S T) =
--    Σᵀ (replaceᵀ f S) (replaceᵀ (wkˢ f) T)
--replaceᵀ f (Πᵀ S T) =
--    Πᵀ (replaceᵀ f S) (replaceᵀ (wkˢ f) T)
--replaceᵀ f (𝓘 T t₁ t₂) =
--    𝓘 (replaceᵀ f T) (replaceᶜ f t₁) (replaceᶜ f t₂)
--replaceᵀ f □ ℓ [ T ] = □ ℓ [ replaceᵀ (f ∧ₛ λ ()) T ]
--replaceᵀ f (⟦ T ⟧ᵀ Ls m) =
--    ⟦ replaceᵀ (f ∧ₛ λ ()) T ⟧ᵀ Ls (replaceᶜ f m)
--
--replaceᴵ _ (Uᵗ ℓ) = Uᵗ ℓ
--replaceᴵ _ (Nᵗ ℓ) = Nᵗ ℓ
--replaceᴵ f ind T on n ⟨ z , s ⟩ =
--    ind replaceᵀ (wkˢ f) T on replaceᴵ f n ⟨ replaceᶜ f z , replaceᶜ f s ⟩
--replaceᴵ s (Σᵗ t u) = Σᵗ (replaceᴵ s t) (replaceᴵ (wkˢ s) u)
--replaceᴵ s (π₁ t) = π₁ (replaceᴵ s t)
--replaceᴵ s (π₂ t) = π₂ (replaceᴵ s t)
--replaceᴵ s (Πᵗ t u) = Πᵗ (replaceᴵ s t) (replaceᴵ (wkˢ s) u)
--replaceᴵ s (t $ u) = replaceᴵ s t $ replaceᶜ s u
--replaceᴵ s (Idᵗ t t₁ t₂) = Idᵗ (replaceᴵ s t) (replaceᶜ s t₁) (replaceᶜ s t₂)
--replaceᴵ s (Jᵗ T i t) =
--    Jᵗ (replaceᵀ (wkˢ (wkˢ s)) T) (replaceᴵ s i) (replaceᶜ s t)
--replaceᴵ s (Boxᵗ ℓ t) = Boxᵗ ℓ (replaceᴵ (s ∧ₛ λ ()) t)
--replaceᴵ s (⟦ t ⟧ᵗ ℓ) = ⟦ replaceᴵ (s ∧ₛ λ ()) t ⟧ᵗ ℓ
--replaceᴵ s (t as T) = replaceᶜ s t as replaceᵀ s T
--replaceᴵ ιₛ (` i) = ` i
--replaceᴵ (_ ∧ₛ f) (` i) = f i
--replaceᴵ ιₛ [ t ]🔓 = [ t ]🔓
--replaceᴵ (ιₛ ∧ₛ _) [ t ]🔓 = [ t ]🔓
--replaceᴵ ((s ∧ₛ f) ∧ₛ _) [ t ]🔓 = [ replaceᴵ (s ∧ₛ f) t ]🔓
--
--_[x:=_]ᵀ :
--  ∀ {n ns} → Type (suc n) ns → Termᴵ n ns → Type n ns
--T [x:= t ]ᵀ =
--  replaceᵀ (ιₛ ∧ₛ λ { zero → t ; (suc i) → ` i }) T
--
--infix 4 _⊢_·_∈ᵀ_
--data _⊢_·_∈ᵀ_ {n ns} (Γ : Ctx n ns) (ℓ : 𝓛) : Type n ns → 𝓛 → Set
--
--data ⊢_·_ (ℓ : 𝓛) : ∀ {n ns} → Ctx n ns → Set where
--  WF-Nil :
--    -------
--    ⊢ ℓ · ε
--  WF-Var : ∀ {n ns} (Γ : Ctx n ns) T κ →
--    ⊢ ℓ · Γ → Γ ⊢ ℓ · T ∈ᵀ κ →
--    --------------------------
--         ⊢ ℓ · (Γ ,x: T)
--  WF-Lock : ∀ {n ns} (Γ : Ctx n ns) κ →
--       ⊢ κ · Γ →
--    ----------------
--    ⊢ ℓ · (κ · Γ 🔒)
--
--infix 4 _⊢_·_∋ᵗ_
--data _⊢_·_∋ᵗ_ {n ns} : Ctx n ns → 𝓛 → Type n ns → Termᶜ n ns → Set
--
--𝓜 : ∀ {n ns} → Levels → Type n ns
--𝓜 _ = 𝓤 0
--
--data _⊢_·_∈ᵀ_ Γ ℓ where
--  Level-El : ∀ t κ →
--      Γ ⊢ ℓ · 𝓤 κ ∋ᵗ t →
--    -----------------------
--    Γ ⊢ ℓ · El κ [ t ] ∈ᵀ κ
--  Level-Uni : ∀ κ →
--          ⊢ ℓ · Γ →
--    {--------------------} (κ < ℓ) →
--     Γ ⊢ ℓ · 𝓤 κ ∈ᵀ suc κ
--  Level-Nat : ∀ κ →
--         ⊢ ℓ · Γ →
--    {-----------------} (κ ≤ ℓ) →
--     Γ ⊢ ℓ · ℕᵀ κ ∈ᵀ κ
--  Level-Sigma : ∀ κ j S T →
--    Γ ⊢ ℓ · S ∈ᵀ κ → Γ ,x: S ⊢ ℓ · T ∈ᵀ j →
--    ---------------------------------------
--            Γ ⊢ ℓ · Σᵀ S T ∈ᵀ κ ⊔ j
--  Level-Pi : ∀ κ j S T →
--    Γ ⊢ ℓ · S ∈ᵀ κ → Γ ,x: S ⊢ ℓ · T ∈ᵀ j →
--    ---------------------------------------
--            Γ ⊢ ℓ · Πᵀ S T ∈ᵀ κ ⊔ j
--  Level-Id : ∀ κ T t₁ t₂ →
--    Γ ⊢ ℓ · T ∈ᵀ κ → Γ ⊢ ℓ · T ∋ᵗ t₁ → Γ ⊢ ℓ · T ∋ᵗ t₂ →
--    ----------------------------------------------------
--                   Γ ⊢ ℓ · 𝓘 T t₁ t₂ ∈ᵀ κ
--  Level-Box : ∀ κ j T →
--     ℓ · Γ 🔒 ⊢ κ · T ∈ᵀ j →
--    {-----------------------} (κ ≤ ℓ) →
--     Γ ⊢ ℓ · □ κ [ T ] ∈ᵀ κ
--  Level-TyInterp : ∀ T m Ls j →
--     Γ ⊢ ℓ · 𝓜 Ls ∋ᵗ m → ℓ · Γ 🔒 ⊢ pred (length Ls) · T ∈ᵀ j →
--    {------------------------------------------------------------} (H : j < length Ls) →
--     Γ ⊢ ℓ · ⟦ T ⟧ᵀ Ls m ∈ᵀ proj₁ (lookup (toList Ls) (fromℕ< H))
--
--data _⊢_·_∋_≅_ {n ns} (Γ : Ctx n ns) (ℓ : 𝓛) : Type n ns → Termᶜ n ns → Termᶜ n ns → Set where
--
--data _⊢_·_∋ᵗ_ where
--  Check-Zero : ∀ Γ ℓ κ →
--    ------------------
--    Γ ⊢ ℓ · ℕᵀ κ ∋ᵗ 0ᵗ
--  Check-Succ : ∀ Γ ℓ κ t →
--    Γ ⊢ ℓ · ℕᵀ κ ∋ᵗ t →
--    --------------------
--    Γ ⊢ ℓ · ℕᵀ κ ∋ᵗ Sᵗ t
--  Check-Pair : ∀ Γ ℓ s S t T →
--    Γ ⊢ ℓ · S ∋ᵗ s → Γ ⊢ ℓ · T [x:= s as S ]ᵀ ∋ᵗ t →
--    ------------------------------------------------
--              Γ ⊢ ℓ · Σᵀ S T ∋ᵗ ⟨ s , t ⟩
--  Check-Abs : ∀ Γ ℓ S T t →
--    Γ ,x: S ⊢ ℓ · T ∋ᵗ t →
--    ----------------------
--    Γ ⊢ ℓ · Πᵀ S T ∋ᵗ λᵗ t
--  Check-Refl : ∀ Γ ℓ T t₁ t₂ →
--      Γ ⊢ ℓ · T ∋ t₁ ≅ t₂ →
--    -------------------------
--    Γ ⊢ ℓ · 𝓘 T t₁ t₂ ∋ᵗ rflᵗ
