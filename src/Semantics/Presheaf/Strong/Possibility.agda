
  where

  open import Semantics.Presheaf.Possibility C _⊆_ _R_ IF FMF
   
  ◇'-strength-natural : {p : 𝒫 ₀ Γ } {◇q : ◇'-Fam 𝒬 Γ} (w : Γ ⊆ Γ') →
    wk[ ◇' (𝒫 ×' 𝒬) ] w (◇'-strength-fun p ◇q) ≋[ ◇' (𝒫 ×' 𝒬) ] ◇'-strength-fun (wk[ 𝒫 ] w p) (wk[ ◇' 𝒬 ] w ◇q)
  ◇'-strength-natural {𝒫 = 𝒫} {𝒬 = 𝒬} w = proof (≡-refl , ≡-refl , proof
    ((let open EqReasoning ≋[ 𝒫 ]-setoid in
      begin
        wk[ 𝒫 ] (factor⊆ w _{-m-}) (wk[ 𝒫 ] (R-to-⊆ _{-m-}) _)
          ≈˘⟨ wk[ 𝒫 ]-pres-trans (R-to-⊆ _{-m-}) (factor⊆ w _{-m-}) _ ⟩
        wk[ 𝒫 ] (⊆-trans (R-to-⊆ _{-m-}) (factor⊆ w _{-m-})) _
         ≡⟨ cong (λ w → wk[ 𝒫 ] w _) (factor-square-commutes w _) ⟩
        wk[ 𝒫 ] (⊆-trans w (R-to-⊆ (factorR w _{-m-}))) _
          ≈⟨ wk[ 𝒫 ]-pres-trans w (R-to-⊆ (factorR w _{-m-})) _ ⟩
        wk[ 𝒫 ] (R-to-⊆ (factorR w _{-m-})) (wk[ 𝒫 ] w _) ∎)
    , ≋[ 𝒬 ]-refl))
  
  ◇'-strength : (𝒫 𝒬 : Psh) → 𝒫 ×' (◇' 𝒬) →̇ ◇' (𝒫 ×' 𝒬)
  ◇'-strength 𝒫 𝒬 = record
    { fun     = λ p×◇q → ◇'-strength-fun (π₁' .apply p×◇q) (π₂' .apply p×◇q)
    ; pres-≋  = λ r≋r' → ◇'-strength-fun-pres-≋ (π₁' .apply-≋ r≋r') (π₂' .apply-≋ r≋r')
    ; natural = λ w p → ◇'-strength-natural w }


  abstract
    ◇'-strength-natural₁ : (t : 𝒫 →̇ 𝒫') → ◇'-strength 𝒫' 𝒬 ∘ (t ×'-map id') ≈̇ (◇'-map (t ×'-map id')) ∘ ◇'-strength 𝒫 𝒬
    ◇'-strength-natural₁ {𝒫} {𝒫'} {𝒬} t = record { proof = λ p → ◇'-strength-fun-square₁ t }

    ◇'-strength-natural₂ : (t : 𝒬 →̇ 𝒬') → ◇'-strength 𝒫 𝒬' ∘ (id' ×'-map (◇'-map t)) ≈̇ (◇'-map (id' ×'-map t)) ∘ ◇'-strength 𝒫 𝒬
    ◇'-strength-natural₂ t = record { proof = λ _p → ◇'-strength-fun-square₂ t } 

    ◇'-strength-assoc : ◇'-map assoc' ∘ ◇'-strength (𝒫 ×' 𝒬) ℛ ≈̇ (◇'-strength 𝒫 (𝒬 ×' ℛ) ∘ (id' ×'-map (◇'-strength 𝒬 ℛ)) ∘ assoc')
    ◇'-strength-assoc {𝒫} {𝒬} {ℛ} = record { proof = λ _p → ≋[ ◇' (𝒫 ×' (𝒬 ×' ℛ)) ]-refl }

    ◇'-strength-unit :  ◇'-map π₂' ∘ ◇'-strength []' 𝒫 ≈̇ π₂'
    ◇'-strength-unit {𝒫} = record { proof = λ _p → ≋[ ◇' 𝒫 ]-refl }

  ◇'-is-strong : StrongFunctor PshCat-is-CC ◇'-is-PshFunctor
  ◇'-is-strong = record
                   { ◯'-strength[_,_]     = ◇'-strength
                   ; ◯'-strength-natural₁ = ◇'-strength-natural₁
                   ; ◯'-strength-natural₂ = ◇'-strength-natural₂
                   ; ◯'-strength-assoc    = {!◇'-strength-assoc!} -- 
                   ; ◯'-strength-unit     = ◇'-strength-unit
                   }


