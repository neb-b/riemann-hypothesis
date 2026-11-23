module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PsiCc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.Top

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv)
    (hψ : PsiEven e ψ) : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
  have h1 : cycZ ℚ Ω l σ = -1 := h.cyc (E := ℚ)
  have h2 : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have h3 : chiO ℚ Ω l O σ = -1 := by
    ext
    simp [chiO, h1]
  have h4 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : Oˣ) : O) = (-1) ^ e * ψ (-1) := by
    simp [Chr.Psi, Chr.dirG, h2, h3]
  have h5 : ((-1 : O) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Units.ext_iff, h4, Units.val_one, hψ, h5]

theorem UpperTheory.V.Ws.xi2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → (∃ n : ℕ, D.ξ ^ 2 ^ n = 1) ∧ (∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1 := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, h, t, e, ψ, -, -, -, hψ, -, hO⟩ := hD
  obtain ⟨he, hp, -, _, ξ', ξ₀, -, -, h0, hξ⟩ := hO
  generalize h.nII l ψ = n at ξ' hξ
  have h1 : ξ₀ = 1 := orderOf_eq_one_iff.1 h0
  have h2 : ∀ σ, D.ξ σ = ξ'.toUnitHom (Chr.cls ℚ Ω (2 ^ n) σ) := by
    intro σ
    rw [hξ, MonoidHom.mul_apply, h1]
    have : Chr.cls ℚ Ω 1 σ = 1 := Subsingleton.elim _ _
    simp [Chr.dirG, this]
  refine ⟨⟨n, ?_⟩, fun A hA σ hσ => ?_, fun σ hσ => ?_⟩
  · ext1 σ
    rw [MonoidHom.pow_apply, h2, ← map_pow, MonoidHom.one_apply]
    have h3 : Chr.cls ℚ Ω (2 ^ n) σ ^ 2 ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      refine orderOf_dvd_card.trans ?_
      rw [ZMod.card_units_eq_totient]
      rcases n with _ | n
      · simp
      · rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp [pow_succ]
    rw [h3, map_one]
  · have h3 : ¬ A.valuation ((2 ^ n : ℕ) : Ω) < 1 := by
      have h4 := hA 2 (Finset.mem_singleton_self 2)
      rw [Nat.cast_pow, map_pow]
      exact not_lt.2 (one_le_pow₀ (not_lt.1 h4))
    have h4 : Chr.cls ℚ Ω (2 ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (2 ^ n)).2.2.2.2 A h3 hσ
    rw [MonoidHom.mem_ker, h2, h4, map_one]
  · rw [Raw.Psi, he, hp]
    exact psi_cc Ω l ψ e hσ (h.mem_X.1 hψ).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Two2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.two2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 → IsTotallyReal k₀ → k₀.fixingSubgroup = X.φ.ker → T.Two := by
  intro Ω _ _ _ l hl c D hD X T hOn k₀ hk hr hfix
  obtain ⟨hne, -, -, -, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨-, -, -, -, haw⟩ := away D hD
  have hH : ∀ g : G T.F Ω, Raw.bar D.Psi (resQ T.F g) = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g =>
    (X.mem_H.1 (hOn.1 ▸ resQ_mem T.F g)).1
  have hps : ∀ g : G T.F Ω, T.rb wPs g = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hrb, hH]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> cases T.pr <;> simp [wPs]
  have hal : ∀ g : G T.F Ω, T.rb wAl g = Raw.bar D.ξ (resQ T.F g) := fun g => by
    rw [hrb]
    cases T.pr <;> simp [wAl]
  have hiff : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ X.φ (resQ T.F g) = 1 := fun g => by
    rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h]
    · simp
    · constructor
      · intro h'
        exact absurd (by simpa using h') hne
      · intro h'
        exact absurd h' (by decide)
  have key : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A,
      Raw.bar D.Psi g = 1 → X.κ g = 1 → ∃ s : G T.F Ω, resQ T.F s = g := fun q hq A hA g hg h1 h2 => by
    have a : X.φ g = 1 := X.hφ.split q hq A hA hg
    have b : X.η g = 1 := X.hη.split q (Finset.mem_insert_of_mem hq) A hA hg
    have d : X.η' g = 1 := X.hη'.split q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) A hA hg
    refine exists_resQ ?_
    rw [hOn.1, X.mem_H]
    refine ⟨?_, b.trans d.symm, h2⟩
    rw [h1, a]
    simp
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ⟨k₀, hk, hr, fun p hp A hA => ?_, fun g => ?_⟩,
    X.ord, X.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> simp
  · have hg' := (resQ_Ine T.F A g).1 hg
    by_cases hA : A.valuation (X.p₃ : Ω) < 1
    · rw [hps, ← hH, Raw.bar, ((haw A X.p₃ X.hφ.prime X.hφ.nm hA).2 _ hg').1]
      simp
    · exact (hiff g).2 (X.hφ.unr A hA hg')
  · exact (hiff g).2 (X.hφ.split l hD.l_mem A hA ((resQ_Dec T.F A g).1 hg))
  · rw [hfix]
    refine X.hφ.split p ?_ A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hD.two_mem
    · exact hD.l_mem
  · rw [hfix, MonoidHom.mem_ker]
    exact hiff g
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.bigL A hA
    obtain ⟨s, rfl⟩ := key l hD.l_mem A hA g hg h1 h2
    exact ⟨s, (resQ_Dec T.F A s).2 hg, by rw [hal]; exact h3⟩
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.big2 A hA
    obtain ⟨s, rfl⟩ := key 2 hD.two_mem A (by exact_mod_cast hA) g (Ine_le_Dec A hg) h1 h2
    exact ⟨s, (resQ_Ine T.F A s).2 hg, by rw [hal]; exact h3⟩
end

