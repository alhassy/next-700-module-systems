-- The .agda file is trangled from an org file.
module semantics-via-MA-Sets where

open import Data.Product
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Level renaming (zero to ℓ₀; suc to ℓsuc; _⊔_ to _⊍_)

Σ∶• : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Σ∶• = Σ

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

record ⊤ {ℓ} : Set ℓ where
  constructor tt

data Just {ℓ} {A : Set ℓ} : A → Set where
  just : (a : A) → Just a

Context = λ ℓ → Set ℓ

type : ∀ {ℓ} → Context ℓ → Set (ℓsuc ℓ)
type {ℓ} Γ = Γ → Set ℓ

Context′ : ∀ {ℓ} → Context ℓ → Set (ℓsuc ℓ)
Context′ {ℓ} Ξ  =  Ξ → Set ℓ

type′ : ∀ {ℓ} {Ξ : Context ℓ} → Context′ Ξ → Set (ℓsuc ℓ)
type′ {ℓ} Γ = ∀ {ξ} → Γ ξ → Set ℓ

record PackageFormer (ℓ : Level) : Set (ℓsuc ℓ) where
  constructor _❙_
  field
    parameters : Context ℓ
    body       : Context′ parameters

  toContext : Context ℓ
  toContext = Σ γ ∶ parameters • body γ

∅ₚ : ∀ {ℓ} → PackageFormer ℓ
∅ₚ = ⊤ ❙ (λ _ → ⊤)

typeₚ : ∀ {ℓ} → PackageFormer ℓ → Set (ℓsuc ℓ)
typeₚ {ℓ} (parameters ❙ body) = (Σ ξ ∶ parameters • body ξ) → Set ℓ

_⊎ₚ_ : ∀ {ℓ} → PackageFormer ℓ → PackageFormer ℓ → PackageFormer ℓ
(Γ₁ ❙ Γ₂) ⊎ₚ (Γ₁′ ❙ Γ₂′) = (Γ₁ ⊎ Γ₁′) ❙ [ Γ₂ , Γ₂′ ]

_⨾ₚ_ :  ∀ {ℓ} (p : PackageFormer ℓ) → typeₚ p → PackageFormer ℓ
(parameters ❙ body) ⨾ₚ d = parameters ❙ λ ξ → Σ β ∶ body ξ • d (ξ , β)

record MA-Set (ℓ₁ ℓ₂ : Level) : Set (ℓsuc (ℓ₁ ⊍ ℓ₂)) where
  field
    ℳ  : Set ℓ₁
    _⊕_ : ℳ → ℳ → ℳ
    Id  : ℳ
    𝒜 :  ℳ → Set ℓ₂
    _·_ : (m : ℳ) → 𝒜 m → ℳ  -- Note the dependency
    -- TODO: Ommiting axioms for now; likely want a setoid structure.

open MA-Set

MonoidPF : PackageFormer (ℓsuc ℓ₀)
MonoidPF = (((∅ₚ
           ⨾ₚ λ{ (tt , _) → Set})
           ⨾ₚ λ{ (tt , (tt , Carrier)) → Lift (ℓsuc ℓ₀) Carrier})
           ⨾ₚ λ{ (tt , ((tt , Carrier), lift point))
                 → Lift (ℓsuc ℓ₀) (Carrier → Carrier → Carrier)})
           ⨾ₚ λ{ (tt , (((tt , Carrier) , lift point) , lift _⊕_))
                 → Lift (ℓsuc ℓ₀) (∀ {x} → x ⊕ point ≡ x × point ⊕ x ≡ x)}

PFs-are-MA-Sets : ∀ {ℓ} → MA-Set (ℓsuc ℓ) (ℓsuc ℓ)
PFs-are-MA-Sets {ℓ} = record
  { ℳ   = PackageFormer ℓ
  ; _⊕_ = _⊎ₚ_
  ; Id  = ∅ₚ
  ; 𝒜   = typeₚ
  ; _·_ = _⨾ₚ_
  }

record Hom {ℓ₁ ℓ₂} (Src Tgt : MA-Set ℓ₁ ℓ₂) : Set (ℓsuc (ℓ₁ ⊍ ℓ₂)) where
  field
    mor₁ : ℳ Src → ℳ Tgt
    mor₂ : ∀ {m} → 𝒜 Src m → 𝒜 Tgt (mor₁ m)
    pres-Id : mor₁ (Id Src) ≡ Id Tgt
    pres-⊕  : ∀ {x y} → mor₁ (_⊕_ Src x y) ≡ _⊕_ Tgt (mor₁ x) (mor₁ y)
    coherence : ∀ {m a} → mor₁ (_·_ Src m a) ≡ _·_ Tgt (mor₁ m) (mor₂ a)

open Hom

id : ∀ {ℓ₁ ℓ₂} {MA : MA-Set ℓ₁ ℓ₂} → Hom MA MA
id = record
  { mor₁      = λ x → x
  ; mor₂      = λ x → x
  ; pres-Id   = refl
  ; pres-⊕    = refl
  ; coherence = refl
  }

_∘_ : ∀ {ℓ₁ ℓ₂} {MA MB MC : MA-Set ℓ₁ ℓ₂}
    → Hom MB MC
    → Hom MA MB
    → Hom MA MC
_∘_ {MA = MA} {MB} {MC} F G = record
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
