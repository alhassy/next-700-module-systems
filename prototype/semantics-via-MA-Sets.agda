-- The .agda file is trangled from an org file.
module semantics-via-MA-Sets

  -- We need an ambient type theory:
  --
  -- An infinite set of variable names
  (𝕍 : Set)
  -- A typing judgement for terms e of
  -- type τ in a context Γ,
  -- which we write Γ ⊢ e : τ
  (let Context = Set)
  (Expr    : Set)
  (_⊢_∶_ : Context → Expr → Expr → Set)
  (_⊢_type : Context → Expr → Set)

  where
  -- TODO: Ignoring optional definitions for now.

open import Data.Unit
open import Data.Product hiding (_,_)
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

data Declaration (Γ : Context) : Set where
  _∶_≔_ : (n : 𝕍) {τ δ : Expr} → Γ ⊢ τ type → Γ ⊢ δ ∶ τ → Declaration Γ

∅ : Context
∅ = ⊤

type : Context → Set₁
type Γ = Γ → Set

_⨾_ : (Γ : Context) (τ : type Γ) → Context
Γ ⨾ τ = Σ γ ∶ Γ • τ γ

-- We need to be able to speak about “contexts over contexts”

Context′ : Context → Set₁
Context′ Ξ = Ξ → Set

∅′ : ∀ {Ξ} → Context′ Ξ
∅′ = λ _ → ⊤

type′ : ∀ {Ξ} → Context′ Ξ → Set₁
type′ Γ = ∀ {ξ} → Γ ξ → Set

_⨾′_ : ∀ {Ξ} → (Γ : Context′ Ξ) (τ : type′ Γ) → Context′ Ξ
Γ ⨾′ τ = λ ξ → Σ γ ∶ Γ ξ • τ γ

record PackageFormer : Set₁ where
  constructor _❙_
  field
    parameters : Context
    body       : Context′ parameters

_⊎ₚ_ : PackageFormer → PackageFormer → PackageFormer
(Γ₁ ❙ Γ₂) ⊎ₚ (Γ₁′ ❙ Γ₂′) = (Γ₁ ⊎ Γ₁′) ❙ [ Γ₂ , Γ₂′ ]





record MA-Set : Set₁ where
  field
    ℳ  : Set
    _⊕_ : ℳ → ℳ → ℳ
    Id  : ℳ
    𝒜 :  Set
    _·_ : ℳ → 𝒜 → ℳ
    -- TODO: Ommiting axioms for now.

open MA-Set

record Hom (Src Tgt : MA-Set) : Set₁ where
  field
    mor₁ : ℳ Src → ℳ Tgt
    mor₂ : 𝒜 Src → 𝒜 Tgt
    pres-Id : mor₁ (Id Src) ≡ Id Tgt
    pres-⊕  : ∀ {x y} → mor₁ (_⊕_ Src x y) ≡ _⊕_ Tgt (mor₁ x) (mor₁ y)
    coherence : ∀ {m a} → mor₁ (_·_ Src m a) ≡ _·_ Tgt (mor₁ m) (mor₂ a)

open Hom

id : ∀ {MA : MA-Set} → Hom MA MA
id = record
  { mor₁      = λ x → x
  ; mor₂      = λ x → x
  ; pres-Id   = refl
  ; pres-⊕    = refl
  ; coherence = refl
  }

_∘_ : ∀ {MA MB MC : MA-Set}
    → Hom MB MC
    → Hom MA MB
    → Hom MA MC
_∘_ {MA} {MB} {MC} F G = record
  { mor₁ = λ x → mor₁ F (mor₁ G x)
  ; mor₂ = λ x → mor₂ F (mor₂ G x)
  ; pres-Id = trans (cong (mor₁ F) (pres-Id G)) (pres-Id F)
  ; pres-⊕ = λ {x y} → begin
      mor₁ F (mor₁ G (_⊕_ MA x y))          ≡⟨ cong (mor₁ F) (pres-⊕ G) ⟩
      mor₁ F (_⊕_ MB (mor₁ G x) (mor₁ G y)) ≡⟨ pres-⊕ F ⟩
      _⊕_ MC (mor₁ F (mor₁ G x)) (mor₁ F (mor₁ G y)) ∎
  ; coherence = λ {m a} → begin
      mor₁ F (mor₁ G (_·_ MA m a)) ≡⟨ cong (mor₁ F) (coherence G) ⟩
      mor₁ F (_·_ MB (mor₁ G m) (mor₂ G a)) ≡⟨ coherence F ⟩
      _·_ MC (mor₁ F (mor₁ G m)) (mor₂ F (mor₂ G a)) ∎ }
