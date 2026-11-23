module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
section
set_option linter.deprecated false

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain

section General

private theorem absNorm_eq_prime_pow_of_natCast_mem (K : Type) [Field K] [NumberField K] {g : ℕ} (hg : g.Prime)
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hgP : ((g : ℕ) : 𝓞 K) ∈ P) :
    ∃ m, 0 < m ∧ Ideal.absNorm P = g ^ m := by
  have h1 : (Ideal.absNorm P : ℤ) ∣ Algebra.norm ℤ ((g : ℕ) : 𝓞 K) := Ideal.absNorm_dvd_norm_of_mem hgP
  have h2 : Algebra.norm ℤ ((g : ℕ) : 𝓞 K) = (g : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap]
  rw [h2] at h1
  have h3 : Ideal.absNorm P ∣ g ^ Module.finrank ℤ (𝓞 K) := by exact_mod_cast h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).mp h3
  refine ⟨m, Nat.pos_of_ne_zero ?_, hm⟩
  rintro rfl
  rw [pow_zero, Ideal.absNorm_eq_one_iff] at hm
  exact hP.ne_top hm

theorem splitsCompl_down (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : ℕ)
    (hg : g.Prime) (h : SplitsCompl E g) : SplitsCompl F g := by
  intro P hP hgP
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) P
  have hPQ : P = Q.comap (algebraMap (𝓞 F) (𝓞 E)) := hQl.over
  have hgQ : ((g : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q := by
      rw [← Ideal.mem_comap, ← hPQ]
      exact hgP
    simpa using h1
  obtain ⟨hN, hsq⟩ := h Q hQ hgQ
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm0, hm⟩ := absNorm_eq_prime_pow_of_natCast_mem F hg P hgP
    have hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 F) (𝓞 E)) hPQ.le) :=
      Ideal.quotientMap_injective' hPQ.ge
    have hcQ : Nat.card (𝓞 E ⧸ Q) = g := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
    haveI : Finite (𝓞 E ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcQ]; exact hg.ne_zero)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcQ, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hm] at hle
    have hm1 : m ≤ 1 := by
      by_contra hc
      have h5 : g ^ 1 < g ^ m := Nat.pow_lt_pow_right hg.one_lt (by omega)
      rw [pow_one] at h5
      omega
    rw [hm, show m = 1 by omega, pow_one]
  · intro hsq2
    apply hsq
    have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) P ≤ Q := Ideal.map_le_iff_le_comap.mpr hPQ.le
    have h2 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q ^ 2 := by
      rw [sq] at hsq2 ⊢
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hsq2
      rw [Ideal.map_mul] at h3
      exact Ideal.mul_mono hle hle h3
    simpa using h2

variable (K : Type) [Field K] [NumberField K]

def plOver (g : ℕ) : Set (HeightOneSpectrum (𝓞 K)) := {p | ((g : ℕ) : 𝓞 K) ∈ p.asIdeal}

theorem span_ne_bot {g : ℕ} (hg : g.Prime) : Ideal.span {(g : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hg.ne_zero

theorem span_isMaximal {g : ℕ} (hg : g.Prime) : (Ideal.span {(g : ℤ)}).IsMaximal := by
  haveI := Fact.mk hg
  exact Int.ideal_span_isMaximal_of_prime g

theorem card_primesOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  classical
  haveI := span_isMaximal hg
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K (span_ne_bot hg), Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 K) := by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
    exact hP
  obtain ⟨hPp, hPl⟩ := hP'
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under_def] using h1
  have hne : P ≠ ⊥ := by
    rintro rfl
    simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
    exact hg.ne_zero hgP
  have hmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hPp
  obtain ⟨hN, hsq⟩ := h P hmax hgP
  have he : (Ideal.span {(g : ℤ)}).ramificationIdx' P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [Ideal.map_span, Set.image_singleton, pow_one, Ideal.span_singleton_le_iff_mem]
      simpa using hgP
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      simpa using hsq
  have hf : (Ideal.span {(g : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hg
    rw [hN] at h1
    have h2 : g ^ (Ideal.span {(g : ℤ)}).inertiaDeg' P = g ^ 1 := by
      rw [pow_one]
      exact h1.symm
    exact Nat.pow_right_injective hg.two_le h2
  rw [he, hf]

theorem image_plOver {g : ℕ} (hg : g.Prime) :
    HeightOneSpectrum.asIdeal '' plOver K g = (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K) : Set (Ideal (𝓞 K))) := by
  haveI := span_isMaximal hg
  ext P
  rw [IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    refine (span_isMaximal hg).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have hv' : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := hv
    simpa using hv'
  · rintro ⟨hPp, hPl⟩
    have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
      have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
      simpa [Ideal.under_def] using h1
    have hne : P ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
      exact hg.ne_zero hgP
    exact ⟨⟨P, hPp, hne⟩, hgP, rfl⟩

theorem injOn_asIdeal (s : Set (HeightOneSpectrum (𝓞 K))) : Set.InjOn HeightOneSpectrum.asIdeal s := fun _ _ _ _ h => HeightOneSpectrum.ext h

theorem finite_plOver {g : ℕ} (hg : g.Prime) : (plOver K g).Finite := by
  have h := image_plOver K hg
  exact Set.Finite.of_finite_image (h ▸ Finset.finite_toSet _) (injOn_asIdeal K _)

theorem ncard_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) : (plOver K g).ncard = Module.finrank ℚ K := by
  rw [← (injOn_asIdeal K _).ncard_image, image_plOver K hg, Set.ncard_coe_finset,
    card_primesOver K hg h]

theorem finprod_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g ^ Module.finrank ℚ K := by
  have hfin := finite_plOver K hg
  have hc : ∀ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g := by
    intro p hp
    rw [(h p.asIdeal p.isMaximal hp).1]
  rw [finprod_mem_congr rfl hc, finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_const,
    ← Set.ncard_eq_toFinset_card _ hfin, ncard_plOver K hg h]

theorem disjoint_plOver {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g') :
    Disjoint (plOver K g) (plOver K g') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨a, b, hab⟩ : IsCoprime (g : ℤ) (g' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hg hg').mpr hne)
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * g + b * g' : ℤ) : 𝓞 K) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hp')

end General

section Record

variable (D : D7)

theorem finrank_hostF_eq : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  rfl

theorem typedPl_eq : typedPl D = plOver D.host.F (D.host.g 0) ∪ plOver D.host.F (D.host.g 1) := rfl

theorem finprod_typedPl (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ typedPl D, φ (Ideal.absNorm p.asIdeal : ℝ) =
      φ (D.host.g 0 : ℝ) ^ D.R.f * φ (D.host.g 1 : ℝ) ^ D.R.f := by
  have hF0 : SplitsCompl D.host.F (D.host.g 0) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0
  have hF1 : SplitsCompl D.host.F (D.host.g 1) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1
  rw [typedPl_eq, finprod_mem_union (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne)
    (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)),
    finprod_plOver _ (D.host.g_prime 0) hF0, finprod_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq]

theorem gaG_eq (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    gaG D = (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 0 : ℝ) ^ i - 1)) ^ D.R.f *
      (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 1 : ℝ) ^ i - 1)) ^ D.R.f := by
  unfold gaG
  exact finprod_typedPl D h0 h1 (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1))

end Record

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section SlopeTestRemainingChoices

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_highest_weight_unit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsDS ε lam σ) : ∃ w : H, IsHighestUnit ε lam σ w := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · exact (le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS) :
      S ≤ lowKSub ε lam σ) (S.smul_mem _ hvS)
  · intro θ hθ
    rw [map_smul, hwt θ hθ, smul_comm]

end SlopeTestRemainingChoices

section Dec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Dec

section Core

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Core

section Core2

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Core2

section Poly

variable {n : ℕ}

end Poly

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Conj

section Bessel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Bessel

end Formalism.MainNotions.BridgeLemma

end
end

