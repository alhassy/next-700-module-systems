-- [[file:~/thesis-proposal/papers/Paper2.org::*Header][Header:1]]
module paper2 where

--------------------------------------------------------------------------------
-- (shell-command "ln -s /Users/musa/thesis-proposal/prototype/semantics-with-waist.agda semantics-with-waist.agda")

open import semantics-with-waist as W hiding (⟨ ; _⟩; End)
open import Data.Product
open import Level renaming (zero to ℓ₀) hiding (suc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Function using (id)
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Sum

open import Data.List
import Data.Unit as Unit
open import Reflection hiding (name; Type) renaming (_>>=_ to _>>=ₘ_)

ℓ₁ = Level.suc ℓ₀
-- Header:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Introduction][Introduction:1]]
Graph₀ : Context ℓ₁
Graph₀ = do Vertex ← Set
            Edges  ← (Vertex → Vertex → Set)
            End {ℓ₀}

-- Helpers for readability
pattern ⟨_⟩₁ x    = x , tt
pattern ⟨_,_⟩ x y = x , y , tt
-- Introduction:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Introduction][Introduction:2]]
comap₀ : ∀ {A B : Set}
      → (f : A → B)
      → Σ G ∶ Graph₀ :kind ‵record • Field 0 G ≡ B
      → Σ G ∶ Graph₀ :kind ‵record • Field 0 G ≡ A
comap₀ {A} {B} f (⟨ .B , edgs ⟩ , refl) = (A , (λ a₁ a₂ → edgs (f a₁) (f a₂)) , tt) , refl
-- Introduction:2 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Introduction][Introduction:3]]
-- Way better and less akward!
comap : ∀ {A B : Set}
     → (f : A → B)
     → (Graph₀ :kind ‵typeclass) B
     → (Graph₀ :kind ‵typeclass) A
comap f ⟨ edgs ⟩₁ = ⟨ (λ a₁ a₂ → edgs (f a₁) (f a₂)) ⟩₁
-- Introduction:3 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*A Grouping Mechanism: Automata][A Grouping Mechanism: Automata:1]]
record DynamicSystem₀ : Set₁ where
  field
    States : Set
    start  : States
    next   : States → States

record DynamicSystem₁ (States : Set) : Set where
  field
    start : States
    next  : States → States

record DynamicSystem₂ (States : Set) (start : States) : Set where
  field
    next : States → States
-- A Grouping Mechanism: Automata:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*A Grouping Mechanism: Automata][A Grouping Mechanism: Automata:2]]
_ : Set₁
_ = DynamicSystem₀

_ : Π X ∶ Set • Set
_ = DynamicSystem₁

_ : Π X ∶ Set • Π x ∶ X • Set
_ = DynamicSystem₂
-- A Grouping Mechanism: Automata:2 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*Unbundling: From Function Types to Functions /on/ Types][Unbundling: From Function Types to Functions /on/ Types:1]]
C″ : Π X ∶ Set • Π x ∶ X • Set₁
C″ X x = Σ 𝒟 ∶ DynamicSystem 0
       • Σ Carrier-is-X ∶ proj₁ 𝒟 ≡ X
       • proj₁ (proj₂ 𝒟) ≡ subst id (sym Carrier-is-X) x

𝒩²eek : C″ ℕ 0
𝒩²eek = (ℕ , 0 , suc , tt) , refl , refl
-- Unbundling: From Function Types to Functions /on/ Types:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:1]]
PointedSet : Context ℓ₁
PointedSet = do Carrier ← Set
                point   ← Carrier
                End {ℓ₁}
-- What about the meta-language's parameters?:1 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:2]]
PointedPF : (Ξ : Set₁) → Context ℓ₁
PointedPF Ξ = do Carrier ← Set
                 point   ← Carrier
                 ‵ Ξ
-- What about the meta-language's parameters?:2 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:3]]
_ : ∀ {n} → PointedPF ⊤ n ≡ PointedSet n
_ = refl
-- What about the meta-language's parameters?:3 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:4]]
-- Convenience names
PointedSetᵣ = PointedSet        :kind ‵record
PointedPFᵣ  = λ Ξ → PointedPF Ξ :kind ‵record

-- An extended record type: Two types with a point of each.
TwoPointedSets = PointedPFᵣ PointedSetᵣ

_ :   TwoPointedSets
    ≡ ( Σ Carrier₁ ∶ Set • Σ point₁ ∶ Carrier₁
      • Σ Carrier₂ ∶ Set • Σ point₂ ∶ Carrier₂ • ⊤)
_ = refl

-- Here's an instance
one : PointedSet :kind ‵record
one = 𝔹 , false , tt

-- Another; a pointed natural extended by a pointed bool,
-- with particular choices for both.
two : TwoPointedSets
two = ℕ , 0 , one
-- What about the meta-language's parameters?:4 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:5]]
_PointedSets : ℕ → Set₁
zero  PointedSets = ⊤
suc n PointedSets = PointedPFᵣ (n PointedSets)

_ :   4 PointedSets
    ≡ (Σ Carrier₁ ∶ Set • Σ point₁ ∶ Carrier₁
      • Σ Carrier₂ ∶ Set • Σ point₂ ∶ Carrier₂
      • Σ Carrier₃ ∶ Set • Σ point₃ ∶ Carrier₃
      • Σ Carrier₄ ∶ Set • Σ point₄ ∶ Carrier₄ • ⊤)
_ = refl
-- What about the meta-language's parameters?:5 ends here

-- [[file:~/thesis-proposal/papers/Paper2.org::*What about the meta-language's parameters?][What about the meta-language's parameters?:6]]
PointedD : (X : Set) → Set₁
PointedD X = termtype (PointedPF (Lift _ X) :waist 1)

-- Pattern synonyms for more compact presentation
pattern nothingP = μ (inj₁ tt)
pattern justP x  = μ (inj₂ (lift x))

casingP : ∀ {X} (e : PointedD X)
        → (e ≡ nothingP) ⊎ (Σ x ∶ X • e ≡ justP x)
casingP nothingP  = inj₁ refl
casingP (justP x) = inj₂ (x , refl)
-- What about the meta-language's parameters?:6 ends here
