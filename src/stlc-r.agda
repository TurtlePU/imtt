open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.Product
open import Data.Vec.Base as Vec using (Vec)

data Type (V : Set) : Set where
  _ᵀ : V -> Type V
  ⊤ᵀ : Type V
  _×ᵀ_ : Type V -> Type V -> Type V
  _⇒ᵀ_ : Type V -> Type V -> Type V
infixr 20 _⇒ᵀ_

infix 17 _/_
_/_ : ∀ {U V} -> Type V -> (V -> Type U) -> Type U
v ᵀ / σ = σ v
⊤ᵀ / _ = ⊤ᵀ
S ×ᵀ T / σ = (S / σ) ×ᵀ (T / σ)
S ⇒ᵀ T / σ = (S / σ) ⇒ᵀ (T / σ)

record Sig : Set where
  field
    C P E : Type Bool
    TT : Type ⊥

infix 18 _||_
_||_ : ∀ {ℓ} {T : Set ℓ} -> T -> T -> Bool -> T
x || y = if_then x else y

infix 19 _at-sig_
_at-sig_ : ∀ {V} -> Type V -> Sig -> Type V
v ᵀ at-sig _ = v ᵀ
⊤ᵀ at-sig 𝓤 = Sig.TT 𝓤 / ⊥-elim
(S ×ᵀ T) at-sig 𝓤 = Sig.P 𝓤 / S at-sig 𝓤 || T at-sig 𝓤
(S ⇒ᵀ T) at-sig 𝓤 = Sig.E 𝓤 / S at-sig 𝓤 || T at-sig 𝓤

PolyType : Set
PolyType = Σ[ n ∈ Nat ] (Type (Fin n))

_∀∷_ : ∀ {n} -> Type (Fin n) -> List PolyType -> List PolyType
T ∀∷ Γ = (_ , T) ∷ Γ

_⟦_⟧_ : ∀ {V} -> Sig -> (τ : PolyType) -> Vec (Type V) (proj₁ τ) -> Type V
𝓤 ⟦ T ⟧ σ = (Sig.C 𝓤 / ⊤ᵀ at-sig 𝓤 || proj₂ T at-sig 𝓤) / Vec.lookup σ

data Three : Set where
  one two three : Three

record Universe (𝓤 : Sig) : Set
data Term (Γ : List PolyType) {V} (Δ : List (Type V)) : Type V -> Set where
  `_ : (i : Fin (length Δ)) -> Term Γ Δ (lookup Δ i)
  · : Term Γ Δ ⊤ᵀ
  `λ_,_ : ∀ S {T} -> Term Γ (S ∷ Δ) T -> Term Γ Δ (S ⇒ᵀ T)
  _$_ : ∀ {S T} -> Term Γ Δ (S ⇒ᵀ T) -> Term Γ Δ S -> Term Γ Δ T
  ⟨_,_⟩ : ∀ {S T} -> Term Γ Δ S -> Term Γ Δ T -> Term Γ Δ (S ×ᵀ T)
  π₁ : ∀ {S T} -> Term Γ Δ (S ×ᵀ T) -> Term Γ Δ S
  π₂ : ∀ {S T} -> Term Γ Δ (S ×ᵀ T) -> Term Γ Δ T
  use_`in_ : ∀ {T n} {S : Type (Fin n)} ->
    Term Γ [] S -> Term (S ∀∷ Γ) Δ T -> Term Γ Δ T
  _#_ :
    ∀ (i : Fin (length Γ)) {σ 𝓤} -> Universe 𝓤 -> Term Γ Δ (𝓤 ⟦ lookup Γ i ⟧ σ)
record Universe 𝓤 where
  inductive
  field
    id : Term [] [] (Sig.C 𝓤 / tt ᵀ || tt ᵀ)
    comp : Term [] [] ((Sig.C 𝓤 / two ᵀ || three ᵀ) ⇒ᵀ
                       (Sig.C 𝓤 / one ᵀ || two ᵀ) ⇒ᵀ
                       (Sig.C 𝓤 / one ᵀ || three ᵀ))
    cnst : Term [] [] (Sig.TT 𝓤)
    pair : Term [] [] ((Sig.C 𝓤 / three ᵀ || one ᵀ) ⇒ᵀ
                       (Sig.C 𝓤 / three ᵀ || two ᵀ) ⇒ᵀ
                       (Sig.C 𝓤 / three ᵀ || (Sig.P 𝓤 / one ᵀ || two ᵀ)))
    proj₁ : Term [] [] (Sig.C 𝓤 / (Sig.P 𝓤 / true ᵀ || false ᵀ) || true ᵀ)
    proj₂ : Term [] [] (Sig.C 𝓤 / (Sig.P 𝓤 / true ᵀ || false ᵀ) || false ᵀ)
    lam : Term [] [] ((Sig.C 𝓤 / (Sig.P 𝓤 / one ᵀ || two ᵀ) || three ᵀ) ⇒ᵀ
                      (Sig.C 𝓤 / one ᵀ || (Sig.E 𝓤 / three ᵀ || two ᵀ)))
    eval : Term [] [] (Sig.C 𝓤
        / (Sig.P 𝓤 / (Sig.E 𝓤 / true ᵀ || false ᵀ) || false ᵀ)
        || true ᵀ)

record Sem {ℓ} (𝓤 : Set ℓ) : Set (lsuc ℓ) where
  field
    ⊤ˢ : 𝓤
    Pˢ Eˢ : 𝓤 -> 𝓤 -> 𝓤

sem-ty : ∀ {ℓ V} {𝓤 : Set ℓ} -> Sem 𝓤 -> Type V -> (V -> 𝓤) -> 𝓤
sem-ty _ (v ᵀ) f = f v
sem-ty 𝓢 ⊤ᵀ _ = Sem.⊤ˢ 𝓢
sem-ty 𝓢 (S ×ᵀ T) f = Sem.Pˢ 𝓢 (sem-ty 𝓢 S f) (sem-ty 𝓢 T f)
sem-ty 𝓢 (S ⇒ᵀ T) f = Sem.Eˢ 𝓢 (sem-ty 𝓢 S f) (sem-ty 𝓢 T f)

record SemV {ℓ} {𝓤 : Set ℓ} (𝓢 : Sem 𝓤) ℓ' : Set (ℓ ⊔ lsuc ℓ') where
  field
    ty : 𝓤 -> Set ℓ'

sem : ∀ {ℓ ℓ' V} {T : Type V} {𝓤 : Set ℓ} {𝓢 : Sem 𝓤} {τ : V -> 𝓤} ->
    (𝓥 : SemV 𝓢 ℓ') -> Term [] [] T -> SemV.ty 𝓥 (sem-ty 𝓢 T τ)
sem = _
