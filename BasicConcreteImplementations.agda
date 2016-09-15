module BasicConcreteImplementations where

open import AbstractInterfaces public


-- Process identifiers.

instance
  ⟨P⟩ : IsProc
  ⟨P⟩ = record
          { Proc    = ℕ
          ; _≡ₚ?_   = _≡?_
          ; _<ₚ_    = _<_
          ; trans<ₚ = trans<
          ; tri<ₚ   = tri<
          }


-- Process clocks, message timestamps, and event timestamps.

instance
  ⟨T⟩ : IsTime
  ⟨T⟩ = record
          { Time      = ℕ
          ; _≡ₜ?_     = _≡?_
          ; _<ₜ_      = _<_
          ; trans<ₜ   = trans<
          ; tri<ₜ     = tri<
          ; irrefl<ₜ  = irrefl<
          ; sucₜ      = suc
          ; _⊔ₜ_      = _⊔_
          ; n<s[n⊔m]ₜ = n<s[n⊔m]
          }


-- Messages.

data BasicMsg : (Pᵢ Pⱼ : Proc) (Tₘ : Time) → Set where

instance
  ⟨M⟩ : IsMsg
  ⟨M⟩ = record
          { Msg = BasicMsg
          }


-- Events within one process.

data BasicEvent : Proc → Time → Set where
  send : ∀ {Cᵢ Pᵢ Pⱼ Tₘ} {{_ : Tₘ ≡ sucₜ Cᵢ}} →
         Msg Pᵢ Pⱼ Tₘ → BasicEvent Pᵢ Tₘ

  recv : ∀ {Cⱼ Pᵢ Pⱼ Tₘ Tⱼ} {{_ : Tⱼ ≡ sucₜ (Tₘ ⊔ₜ Cⱼ)}} →
         Msg Pᵢ Pⱼ Tₘ → BasicEvent Pⱼ Tⱼ

instance
  ⟨E⟩ : IsEvent
  ⟨E⟩ = record
          { Event  = BasicEvent
          ; isSend = λ {Cᵢ} m a → a ≡ send {Cᵢ} m
          ; isRecv = λ {Cⱼ} m a → a ≡ recv {Cⱼ} m
          ; absurd = λ { {{refl}} (refl , ()) }
          }
