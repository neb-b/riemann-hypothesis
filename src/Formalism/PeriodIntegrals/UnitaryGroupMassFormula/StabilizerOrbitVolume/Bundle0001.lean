module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.CosDens
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

def CosDens : Prop :=
  ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν m : Measure X) [IsFiniteMeasure m],
    IsFiniteMeasureOnCompacts ν →
    ∀ (H : ℕ → AddSubgroup X), (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      Antitone H → (∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) →
      ∀ (c0 : X) (κ : ENNReal), m {z | z - c0 ∈ H 0}ᶜ = 0 →
        (∀ n h, h - c0 ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n}) →
        ∀ S : Set X, IsCompact S → m S = κ * ν (S ∩ {z | z - c0 ∈ H 0})

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HenselCount
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

def HenselCount : Prop :=
  ∀ (V X : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), (∀ n, IsOpen (Λ n : Set V)) →
      (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ → (∀ n, IsOpen (H n : Set X)) →
      (∀ n, IsCompact (H n : Set X)) →
      ∀ D : V →+ X, (∀ n, (Λ n).map D = H n) →
      ∀ (G : V → X) (y : V),
        (∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
        ∀ n h, h - G y ∈ H 0 →
          μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) = μ (Λ 0) * ν (H n)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
section
noncomputable section

namespace PI.VolStabSW

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar
section
noncomputable section

open NumberField

namespace PI.VolStabSW

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnd χ hχ h1 x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let g : F →+ ℂ := AddMonoidHom.mk' (fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) /
    (2 * Real.pi * Complex.I)) (by intro a b; simp only [map_add (f := _), add_div])
  have hint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have he : Complex.exp (ℓ (algebraMap F (InfiniteAdeleRing F) a)) = 1 := by
      rw [← hℓ]
      exact h1 a ha
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    show ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = n
    rw [hn, mul_div_assoc, div_self hI, mul_one]
  have hg := hA F Λ hne hnd g hint
  have hzero : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h := hg a
    change ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hI
  have hdense : DenseRange (algebraMap F (InfiniteAdeleRing F)) := by
    first
      | exact InfiniteAdeleRing.denseRange_algebraMap F
      | exact InfiniteAdeleRing.denseRange_algebraMap
      | exact NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have hx : ℓ x = 0 :=
    hdense.induction_on x (isClosed_eq hℓc continuous_const) hzero
  rw [hℓ, hx, Complex.exp_zero]

end PI.VolStabSW
end
end

