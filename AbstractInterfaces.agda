module AbstractInterfaces where

open import Prelude public


-- Process identifiers.

record IsProc : Set₁ where
  field
    Proc    : Set
    _≡ₚ?_   : Decidable (_≡_ {A = Proc})
    _<ₚ_    : Proc → Proc → Set
    trans<ₚ : Transitive _<ₚ_
    tri<ₚ   : Trichotomous _≡_ _<ₚ_

  _≮ₚ_ : Proc → Proc → Set
  P ≮ₚ P′ = ¬ (P <ₚ P′)

open IsProc {{…}} public


-- Process clocks, message timestamps, and event timestamps.

record IsTime : Set₁ where
  field
    Time      : Set
    _≡ₜ?_     : Decidable (_≡_ {A = Time})
    _<ₜ_      : Time → Time → Set
    trans<ₜ   : Transitive _<ₜ_
    tri<ₜ     : Trichotomous _≡_ _<ₜ_
    irrefl<ₜ  : Irreflexive _<ₜ_
    sucₜ      : Time → Time
    _⊔ₜ_      : Time → Time → Time
    n<s[n⊔m]ₜ : ∀ T T′ → T <ₜ sucₜ (T ⊔ₜ T′)

  _≮ₜ_ : Time → Time → Set
  T ≮ₜ T′ = ¬ (T <ₜ T′)

open IsTime {{…}} public


-- Messages.

record IsMsg {{_ : IsProc}} {{_ : IsTime}} : Set₁ where
  field
    Msg : (Pᵢ Pⱼ : Proc) (Tₘ : Time) → Set

open IsMsg {{…}} public


-- Events within one process.

record IsEvent {{_ : IsProc}} {{_ : IsTime}} {{_ : IsMsg}} : Set₁ where
  field
    Event  : Proc → Time → Set

    isSend : ∀ {Cᵢ Pᵢ Pⱼ Tₘ} {{_ : Tₘ ≡ sucₜ Cᵢ}} →
             Msg Pᵢ Pⱼ Tₘ → Event Pᵢ Tₘ → Set

    isRecv : ∀ {Cⱼ Pᵢ Pⱼ Tₘ Tⱼ} {{_ : Tⱼ ≡ sucₜ (Tₘ ⊔ₜ Cⱼ)}} →
             Msg Pᵢ Pⱼ Tₘ → Event Pⱼ Tⱼ → Set

    absurd : ∀ {Cᵢ Cⱼ P Tₘ} {m : Msg P P Tₘ} {a : Event P Tₘ} →
             {{_ : Tₘ ≡ sucₜ Cᵢ}} {{_ : Tₘ ≡ sucₜ (Tₘ ⊔ₜ Cⱼ)}} →
             ¬ (isSend {Cᵢ} m a × isRecv {Cⱼ} m a)

open IsEvent {{…}} public
