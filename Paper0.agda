{- (progn (load-file "PackageFormer.el") (700-mode) (setq 700-folding t))

Press ENTER on “…” to unfold the regions; or use the “700PackageFormers” menu bar.
-}

module Paper0 where
open import Paper0_Generated
open import Relation.Binary.PropositionalEquality using (_≡_)

{-700
PackageFormer MonoidP : Set₁ where
    Carrier : Set
    _⨾_     : Carrier → Carrier → Carrier
    Id      : Carrier
    assoc   : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
    leftId  : ∀ {x : Carrier} → Id ⨾ x ≡ x
    rightId : ∀ {x : Carrier} → x ⨾ Id ≡ x
-}

{- Find definition with M-. on the “_ = ⋯” lines to see the generated code -}

-----------------------------------------------------------------------------------------
------ Identity variational

{-700
-- Variational with empty right hand side.
𝒱-identity =
MonoidPⁱᵈ = MonoidP identity

-- No variational clauses needed!
MonoidP⁰  = MonoidP

-- Identity of composition ⟴
MonoidPᶜ = MonoidP ⟴

-- Operationally: Pf ⟴ v  ≈  Pf v ⟴  ≈  Pf v
--                id ⟴ v  ≈ v ≈ v ⟴ id

-- “⟴” is just forwards composition:
-- We ‘thread’ the Pf through the compositions vᵢ in order.
-}

--------------------------------------------------------------------------------------
----- “record” Variational

{-700
𝒱-record = :type record :waist-strings ("field")

Monoid₀′ = MonoidP record
Monoid₁″ = MonoidP record ⟴ :waist 1
Monoid₂″ = MonoidP record ⟴ :wast 2
-}

_ = Monoid₀′
_ = Monoid₁″
_ = Monoid₂″

--------------------------------------------------------------------------------------
--- Algebraic Data Types

{-lisp
(𝒱 data carrier
  = :type data
    :level dec
    :alter-elements (lambda (fs)
      (thread-last fs
        (--filter (s-contains? carrier (target (get-type it))))
        (--map (map-type (s-replace carrier $𝑛𝑎𝑚𝑒 type) it))))
)
-}

{-700
Monoid₃′ = MonoidP data :carrier "Carrier"
-}
_ = Monoid₃′

-- Note: This is not the same as “termtype” as in Paper0.
