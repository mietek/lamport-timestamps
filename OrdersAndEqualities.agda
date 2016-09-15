open import AbstractInterfaces public

module OrdersAndEqualities {{_ : IsProc}} {{_ : IsTime}} {{_ : IsMsg}} {{_ : IsEvent}} where


-- _≡ₑ_ is a decidable equality on events within one process.

data _≡ₑ_ : ∀ {P T T′} → Event P T → Event P T′ → Set where
  refl≡ₑ : ∀ {P T} {a b : Event P T} →
           a ≡ₑ b


_≢ₑ_ : ∀ {P T T′} → Event P T → Event P T′ → Set
a ≢ₑ b = ¬ (a ≡ₑ b)

≡→≡ₑ : ∀ {P T T′} {a : Event P T} {b : Event P T′} →
        T ≡ T′ → a ≡ₑ b
≡→≡ₑ refl = refl≡ₑ

≢→≢ₑ : ∀ {P T T′} {a : Event P T} {b : Event P T′} →
        T ≢ T′ → a ≢ₑ b
≢→≢ₑ T≢T′ refl≡ₑ = refl ↯ T≢T′

_≡ₑ?_ : ∀ {T T′ P} → (a : Event P T) (b : Event P T′) → Dec (a ≡ₑ b)
_≡ₑ?_ {T} {T′} a b with T ≡ₜ? T′
a ≡ₑ? b | yes T≡T′ = yes (≡→≡ₑ T≡T′)
a ≡ₑ? b | no  T≢T′ = no (≢→≢ₑ T≢T′)


-- _≅ₑ_ is a decidable equality on events across all processes.

data _≅ₑ_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set where
  refl≅ₑ : ∀ {P T} {a : Event P T} {b : Event P T} →
           a ≅ₑ b


_≇ₑ_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set
a ≇ₑ b = ¬ (a ≅ₑ b)

≡ₑ→≅ₑ : ∀ {P T T′} {a : Event P T} {b : Event P T′} →
         a ≡ₑ b → a ≅ₑ b
≡ₑ→≅ₑ refl≡ₑ = refl≅ₑ

≢ₑ→≇ₑ : ∀ {P T T′} {a : Event P T} {b : Event P T′} →
         a ≢ₑ b → a ≇ₑ b
≢ₑ→≇ₑ a≢b refl≅ₑ = refl≡ₑ ↯ a≢b

≢ₚ→≇ₑ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
         Pᵢ ≢ Pⱼ → a ≇ₑ b
≢ₚ→≇ₑ P≢P′ refl≅ₑ = refl ↯ P≢P′

≢ₜ→≇ₑ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
         Tᵢ ≢ Tⱼ → a ≇ₑ b
≢ₜ→≇ₑ T≢T′ refl≅ₑ = refl ↯ T≢T′

_≅ₑ?_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → (a : Event Pᵢ Tᵢ) (b : Event Pⱼ Tⱼ) → Dec (a ≅ₑ b)
_≅ₑ?_ {Pᵢ} {Pⱼ} a b with Pᵢ ≡ₚ? Pⱼ
a ≅ₑ? b | yes refl  with a ≡ₑ? b
a ≅ₑ? b | yes refl  | yes a≡b = yes (≡ₑ→≅ₑ a≡b)
a ≅ₑ? b | yes refl  | no  a≢b = no (≢ₑ→≇ₑ a≢b)
a ≅ₑ? b | no  Pᵢ≢Pⱼ = no (≢ₚ→≇ₑ Pᵢ≢Pⱼ)


-- _<ₑ_ is a decidable strict total order on events within one process.

_<ₑ_ : ∀ {T T′ P} → Event P T → Event P T′ → Set
_<ₑ_ {T} {T′} a b = T <ₜ T′


_≮ₑ_ : ∀ {P T T′} → Event P T → Event P T′ → Set
a ≮ₑ b = ¬ (a <ₑ b)

trans<ₑ : ∀ {P T T′ T″} {a : Event P T} {b : Event P T′} {c : Event P T″} →
          a <ₑ b → b <ₑ c → a <ₑ c
trans<ₑ = trans<ₜ

tri<ₑ : ∀ {T T′ P} → (a : Event P T) (b : Event P T′) →
        Tri (a <ₑ b) (a ≡ₑ b) (b <ₑ a)
tri<ₑ {T} {T′} a b with tri<ₜ T T′
tri<ₑ a b | τ₍ T<T′ T≢T′ T′≮T = τ₍ T<T′ (≢→≢ₑ T≢T′) T′≮T
tri<ₑ a b | τ₌ T≮T′ T≡T′ T′≮T = τ₌ T≮T′ (≡→≡ₑ T≡T′) T′≮T
tri<ₑ a b | τ₎ T≮T′ T≢T′ T′<T = τ₎ T≮T′ (≢→≢ₑ T≢T′) T′<T

irrefl<ₑ : ∀ {P T} {a : Event P T} → a ≮ₑ a
irrefl<ₑ {a = a} with tri<ₑ a a
irrefl<ₑ | τ₍ a<a a≢a a≮a = a≮a
irrefl<ₑ | τ₌ a≮a a≡a _   = a≮a
irrefl<ₑ | τ₎ a≮a a≢a a<a = a≮a

_<ₑ?_ : ∀ {P T T′} → (a : Event P T) (b : Event P T′) → Dec (a <ₑ b)
a <ₑ? b with tri<ₑ a b
a <ₑ? b | τ₍ a<b a≢b b≮a = yes a<b
a <ₑ? b | τ₌ a≮b a≡b b≮a = no a≮b
a <ₑ? b | τ₎ a≮b a≢b b<a = no a≮b


-- _⊳_ is a strict partial order on events across all processes.

data _⊳_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set where
  lift⊳  : ∀ {P T T′} {a : Event P T} {b : Event P T′} →
           a <ₑ b → a ⊳ b

  pass⊳  : ∀ {Cᵢ Cⱼ Pᵢ Pⱼ Tₘ Tⱼ} {{_ : Tₘ ≡ sucₜ Cᵢ}} {{_ : Tⱼ ≡ sucₜ (Tₘ ⊔ₜ Cⱼ)}} →
           {m : Msg Pᵢ Pⱼ Tₘ} {a : Event Pᵢ Tₘ} {b : Event Pⱼ Tⱼ} →
           isSendₑ {Cᵢ} m a → isRecvₑ {Cⱼ} m b → a ⊳ b

  trans⊳ : ∀ {Pᵢ Pⱼ Pₖ Tᵢ Tⱼ Tₖ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} {c : Event Pₖ Tₖ} →
           a ⊳ b → b ⊳ c → a ⊳ c


_⋫_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set
a ⋫ b = ¬ (a ⊳ b)

clock⊳ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
         a ⊳ b → Tᵢ <ₜ Tⱼ
clock⊳ (lift⊳ Tᵢ<Tⱼ)                           = Tᵢ<Tⱼ
clock⊳ (pass⊳ {Cᵢ} {Cⱼ} {{refl}} {{refl}} _ _) = n<s[n⊔m]ₜ (sucₜ Cᵢ) Cⱼ
clock⊳ (trans⊳ a⊳b b⊳c)                        = trans<ₜ (clock⊳ a⊳b) (clock⊳ b⊳c)

irrefl⊳ : ∀ {P T} {a : Event P T} → a ⋫ a
irrefl⊳ (lift⊳ {a = a} a<a) = a<a ↯ irrefl<ₑ {a = a}
irrefl⊳ (pass⊳ x y)         = (x , y) ↯ absurdₑ
irrefl⊳ (trans⊳ {Tᵢ = Tᵢ} {Tⱼ} a⊳b b⊳a) with tri<ₜ Tᵢ Tⱼ
irrefl⊳ (trans⊳ a⊳b b⊳a) | τ₍ Tᵢ<Tⱼ Tᵢ≢Tⱼ Tⱼ≮Tᵢ = clock⊳ b⊳a ↯ Tⱼ≮Tᵢ
irrefl⊳ (trans⊳ a⊳b b⊳a) | τ₌ Tᵢ≮Tⱼ Tᵢ≡Tⱼ Tⱼ≮Tᵢ = clock⊳ a⊳b ↯ Tᵢ≮Tⱼ
irrefl⊳ (trans⊳ a⊳b b⊳a) | τ₎ Tᵢ≮Tⱼ Tᵢ≢Tⱼ Tⱼ<Tᵢ = clock⊳ a⊳b ↯ Tᵢ≮Tⱼ

asym⊳ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} → a ⊳ b → b ⋫ a
asym⊳ a⊳b b⊳a = irrefl⊳ (trans⊳ a⊳b b⊳a)


-- _⇒_ is a decidable strict total order on events across all processes.

data _⇒_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set where
  diff⇒ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
           Tᵢ <ₜ Tⱼ → a ⇒ b

  same⇒ : ∀ {Pᵢ Pⱼ T} {a : Event Pᵢ T} {b : Event Pⱼ T} →
           Pᵢ <ₚ Pⱼ → a ⇒ b


_⇏_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → Event Pᵢ Tᵢ → Event Pⱼ Tⱼ → Set
a ⇏ b = ¬ (a ⇒ b)

lift⇒ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
         a ⊳ b → a ⇒ b
lift⇒ = diff⇒ ∘ clock⊳

trans⇒ : ∀ {Pᵢ Pⱼ Pₖ Tᵢ Tⱼ Tₖ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} {c : Event Pₖ Tₖ} →
          a ⇒ b → b ⇒ c → a ⇒ c
trans⇒ (diff⇒ Tᵢ<Tⱼ) (diff⇒ Tⱼ<Tₖ) = diff⇒ (trans<ₜ Tᵢ<Tⱼ Tⱼ<Tₖ)
trans⇒ (diff⇒ Tᵢ<Tⱼ) (same⇒ Pⱼ<Pₖ) = diff⇒ Tᵢ<Tⱼ
trans⇒ (same⇒ Pᵢ<Pⱼ) (diff⇒ Tⱼ<Tₖ) = diff⇒ Tⱼ<Tₖ
trans⇒ (same⇒ Pᵢ<Pⱼ) (same⇒ Pⱼ<Pₖ) = same⇒ (trans<ₚ Pᵢ<Pⱼ Pⱼ<Pₖ)

≮→⇏ : ∀ {Pᵢ Pⱼ T} {a : Event Pᵢ T} {b : Event Pⱼ T} →
        Pᵢ ≮ₚ Pⱼ → a ⇏ b
≮→⇏ Pᵢ≮Pⱼ (diff⇒ T<T)   = T<T ↯ irrefl<ₜ
≮→⇏ Pᵢ≮Pⱼ (same⇒ Pᵢ<Pⱼ) = Pᵢ<Pⱼ ↯ Pᵢ≮Pⱼ

≮×≮→⇏ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
          Tᵢ ≮ₜ Tⱼ → Pᵢ ≮ₚ Pⱼ → a ⇏ b
≮×≮→⇏ Tᵢ≮Tⱼ Pᵢ≮Pⱼ (diff⇒ Tᵢ<Tⱼ) = Tᵢ<Tⱼ ↯ Tᵢ≮Tⱼ
≮×≮→⇏ Tᵢ≮Tⱼ Pᵢ≮Pⱼ (same⇒ Pᵢ<Pⱼ) = Pᵢ<Pⱼ ↯ Pᵢ≮Pⱼ

≮×≢→⇏ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} {a : Event Pᵢ Tᵢ} {b : Event Pⱼ Tⱼ} →
          Tᵢ ≮ₜ Tⱼ → Tᵢ ≢ Tⱼ → a ⇏ b
≮×≢→⇏ Tᵢ≮Tⱼ Tᵢ≢Tⱼ (diff⇒ Tᵢ<Tⱼ) = Tᵢ<Tⱼ ↯ Tᵢ≮Tⱼ
≮×≢→⇏ Tᵢ≮Tⱼ Tᵢ≢Tⱼ (same⇒ Pᵢ<Pⱼ) = refl ↯ Tᵢ≢Tⱼ

tri⇒₌ : ∀ {Pᵢ Pⱼ T} → (a : Event Pᵢ T) (b : Event Pⱼ T) →
         Tri (a ⇒ b) (a ≅ₑ b) (b ⇒ a)
tri⇒₌ {Pᵢ} {Pⱼ} a b with tri<ₚ Pᵢ Pⱼ
tri⇒₌ a b | τ₍ Pᵢ<Pⱼ Pᵢ≢Pⱼ Pⱼ≮Pᵢ = τ₍ (same⇒ Pᵢ<Pⱼ) (≢ₚ→≇ₑ Pᵢ≢Pⱼ) (≮→⇏ Pⱼ≮Pᵢ)
tri⇒₌ a b | τ₌ Pᵢ≮Pⱼ refl  Pⱼ≮Pᵢ = τ₌ (≮→⇏ Pᵢ≮Pⱼ) refl≅ₑ  (≮→⇏ Pⱼ≮Pᵢ)
tri⇒₌ a b | τ₎ Pᵢ≮Pⱼ Pᵢ≢Pⱼ Pⱼ<Pᵢ = τ₎ (≮→⇏ Pᵢ≮Pⱼ) (≢ₚ→≇ₑ Pᵢ≢Pⱼ) (same⇒ Pⱼ<Pᵢ)

tri⇒ : ∀ {Tᵢ Tⱼ Pᵢ Pⱼ} → (a : Event Pᵢ Tᵢ) (b : Event Pⱼ Tⱼ) →
        Tri (a ⇒ b) (a ≅ₑ b) (b ⇒ a)
tri⇒ {Tᵢ} {Tⱼ} a b with tri<ₜ Tᵢ Tⱼ
tri⇒ a b | τ₍ Tᵢ<Tⱼ Tᵢ≢Tⱼ Tⱼ≮Tᵢ = τ₍ (diff⇒ Tᵢ<Tⱼ) (≢ₜ→≇ₑ Tᵢ≢Tⱼ) (≮×≢→⇏ Tⱼ≮Tᵢ (sym≢ Tᵢ≢Tⱼ))
tri⇒ a b | τ₌ Tᵢ≮Tⱼ refl  Tⱼ≮Tᵢ = tri⇒₌ a b
tri⇒ a b | τ₎ Tᵢ≮Tⱼ Tᵢ≢Tⱼ Tⱼ<Tᵢ = τ₎ (≮×≢→⇏ Tᵢ≮Tⱼ Tᵢ≢Tⱼ) (≢ₜ→≇ₑ Tᵢ≢Tⱼ) (diff⇒ Tⱼ<Tᵢ)

irrefl⇒ : ∀ {P T} {a : Event P T} → a ⇏ a
irrefl⇒ {a = a} with tri⇒ a a
irrefl⇒ | τ₍ a⇒a a≢a a⇏a = a⇏a
irrefl⇒ | τ₌ a⇏a a≢a _    = a⇏a
irrefl⇒ | τ₎ a⇏a a≢a a⇒a = a⇏a

_⇒?_ : ∀ {Pᵢ Pⱼ Tᵢ Tⱼ} → (a : Event Pᵢ Tᵢ) (b : Event Pⱼ Tⱼ) → Dec (a ⇒ b)
a ⇒? b with tri⇒ a b
a ⇒? b | τ₍ a⇒b a≇b b⇏a = yes a⇒b
a ⇒? b | τ₌ a⇏b a≅b b⇏a = no a⇏b
a ⇒? b | τ₎ a⇏b a≇b b⇒a = no a⇏b
