module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalValueOfQuotientAddOfCommonDenominator
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralHeisKerSumDiag
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem heis_kerSum_diag {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsPosHerm H)
    (Λ : AddSubgroup V) (α : V → ℂ) (r z : V) :
    Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) =
      ∑' x : Λ, (α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
        + 2 * π * I * ((H x r).im : ℂ))) * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := by
  simp only [Heisenberg₂, kerSum]
  rw [← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr fun x => ?_
  simp only [kerTerm, mul_assoc, ← Complex.exp_add]
  congr 2
  have hc : ∀ w : ℂ, (starRingEnd ℂ) w = w - 2 * (w.im : ℂ) * I := by
    intro w
    apply Complex.ext <;> simp
    ring
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_im, Complex.ofReal_add]
  rw [hH.1 z r, hH.1 z x, hH.1 r x]
  simp only [hc]
  ring

theorem integral_heis_kerSum_diag : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → ∀ α : V → ℂ, IsSemichar H Λ α → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → μ Fd ≠ ⊤ → ∀ r : V, (∀ y ∈ Λ', ∃ m : ℤ, (H r y).im = m) → IntegrableOn (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) Fd μ ∧ ∫ z in Fd, Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) ∂μ = if r ∈ Λ then α (-r) * (μ.real Fd : ℂ) else 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ Λ' _ hle α hα Fd hFd hFdfin r hr
  have hΛc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hΛ'c : Countable Λ' := by
    have h1 : (Λ : Set V).Countable := Set.countable_coe_iff.mp hΛc
    exact (h1.mono (fun y hy => hle hy)).to_subtype
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : V, ‖H x r‖ ≤ K * ‖x‖ :=
    ⟨‖LinearMap.toContinuousLinearMap (H.flip r)‖, fun x => by
      simpa using (LinearMap.toContinuousLinearMap (H.flip r)).le_opNorm x⟩
  have hcontH : ∀ v : V, Continuous fun z : V => H z v := fun v =>
    Continuous.congr (H.flip v).continuous_of_finiteDimensional
      (fun z => LinearMap.flip_apply _ _ _)
  have hcim : ∀ v : V, Continuous fun z : V => (H v z).im := by
    intro v
    have e : (fun z : V => (H v z).im) = fun z => -(H z v).im := by
      funext z
      rw [hH.1 v z, Complex.conj_im]
    rw [e]
    exact (Complex.continuous_im.comp (hcontH v)).neg
  have he1 : ∀ t : ℝ, ‖cexp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  obtain ⟨c, hc⟩ : ∃ c : Λ → ℂ, ∀ x, c x = α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2
      - (π : ℂ) * H r r / 2 + 2 * π * I * ((H x r).im : ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Λ → V → ℂ, ∀ x z,
      F x z = c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := ⟨_, fun _ _ => rfl⟩
  have hfun : (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) =
      fun z => ∑' x : Λ, F x z := by
    funext z
    rw [heis_kerSum_diag H hH Λ α r z]
    simp only [hF, hc]
  have hre : ∀ x : Λ, (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
      + 2 * π * I * ((H x r).im : ℂ)).re =
      -π * (H x r).re - π / 2 * (H x x).re - π / 2 * (H r r).re := by
    intro x
    simp [Complex.mul_re]
    ring
  have hcle : ∀ x : Λ, ‖c x‖ ≤ Real.exp (-(π / 2) * (H x x).re + π * K * ‖(x : V)‖) *
      Real.exp (-(π / 2) * (H r r).re) := by
    intro x
    have hα1 : ‖α x‖ = 1 := by
      rcases hα.1 x x.2 with h | h <;> simp [h]
    rw [hc, norm_mul, hα1, one_mul, Complex.norm_exp, hre, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(H x r).re ≤ K * ‖(x : V)‖ := by
      have := (abs_le.mp (Complex.abs_re_le_norm (H x r))).1
      linarith [hK x]
    have hπ : 0 ≤ π := Real.pi_pos.le
    nlinarith
  have hcsum : Summable fun x : Λ => ‖c x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcle
      ((_root_.GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm V H hH Λ (π * K)).mul_right _)
  have hFnorm : ∀ x z, ‖F x z‖ = ‖c x‖ := by
    intro x z
    rw [hF, norm_mul, he1, mul_one]
  have hFcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    have e : F x = fun z => c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := funext (hF x)
    rw [e]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hcim _))))
  have hsumcont : Continuous fun z => ∑' x : Λ, F x z :=
    continuous_tsum hFcont hcsum (fun x z => (hFnorm x z).le)
  have hFs : ∀ z, Summable fun x : Λ => ‖F x z‖ := fun z => by
    simp only [hFnorm]
    exact hcsum
  have hbdd : ∀ z, ‖∑' x : Λ, F x z‖ ≤ ∑' x : Λ, ‖c x‖ := fun z => by
    refine (norm_tsum_le_tsum_norm (hFs z)).trans (le_of_eq ?_)
    simp only [hFnorm]
  have hFint : ∀ x : Λ, IntegrableOn (F x) Fd μ := fun x =>
    Measure.integrableOn_of_bounded hFdfin (hFcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hFnorm x z).le)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Measure.integrableOn_of_bounded hFdfin hsumcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  · rw [hfun]
    have hnormint : (fun x : Λ => ∫ z in Fd, ‖F x z‖ ∂μ) = fun x => μ.real Fd * ‖c x‖ := by
      funext x
      simp only [hFnorm]
      rw [setIntegral_const, smul_eq_mul]
    rw [← integral_tsum_of_summable_integral_norm hFint
      (by rw [hnormint]; exact hcsum.mul_left _)]
    have hint : ∀ x : Λ, ∫ z in Fd, F x z ∂μ =
        if (x : V) = -r then c x * (μ.real Fd : ℂ) else 0 := by
      intro x
      simp only [hF]
      rw [integral_const_mul]
      split_ifs with hx
      · have h0 : r + (x : V) = 0 := by
          rw [hx]
          abel
        simp only [h0, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero,
          mul_zero, Complex.exp_zero]
        rw [setIntegral_const, Complex.real_smul, mul_one]
      · have hne : r + (x : V) ≠ 0 := by
          intro h
          apply hx
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h
        rw [_root_.GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero V μ H hH Λ' Fd hFd (r + x) hne ?_, mul_zero]
        intro y hy
        obtain ⟨m1, hm1⟩ := hr y hy
        obtain ⟨m2, hm2⟩ := hα.2.1 x x.2 y (hle hy)
        refine ⟨m1 + m2, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, Complex.add_im, hm1, hm2]
        push_cast
        ring
    simp only [hint]
    by_cases hrΛ : r ∈ Λ
    · rw [if_pos hrΛ, tsum_eq_single ⟨-r, neg_mem hrΛ⟩]
      · have hcoe : ((⟨-r, neg_mem hrΛ⟩ : Λ) : V) = -r := rfl
        have him : (H r r).im = 0 := Complex.conj_eq_iff_im.mp (hH.1 r r).symm
        have hA : cexp (-(π : ℂ) * H (-r) r - (π : ℂ) * H (-r) (-r) / 2 - (π : ℂ) * H r r / 2
            + 2 * π * I * ((H (-r) r).im : ℂ)) = 1 := by
          rw [← Complex.exp_zero]
          congr 1
          simp only [map_neg, LinearMap.neg_apply, neg_neg, Complex.neg_im, him, neg_zero,
            Complex.ofReal_zero, mul_zero, add_zero]
          ring
        rw [hc, hcoe, if_pos rfl, hA, mul_one]
      · intro x hx
        rw [if_neg]
        intro h
        apply hx
        exact Subtype.ext h
    · rw [if_neg hrΛ]
      have hno : ∀ x : Λ, ¬ ((x : V) = -r) := by
        intro x h
        apply hrΛ
        have hm := neg_mem x.2
        rw [h, neg_neg] at hm
        exact hm
      simp [hno]

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IoConstOfMem
section
noncomputable section

namespace GlobalTheory.Glue.IoInh

open GlobalTheory.K5 GlobalTheory.KZ

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem ev_single (ψ : O0 p →+* Ωl) (e : Ωl) (h1 : IsInt (p := p) e) (h2 : IsAlgZp p e) (a : Lau p) (c : ℤ → Ωl)
    (hc : ∀ r, c r = e * zp Ωl (a.coeff r)) :
    Ev ψ c (e * ψ (algebraMap (Lau p) (O0 p) a)) (e * ψ (algebraMap (Lau p) (O0 p) (thL a))) :=
  ⟨1, fun _ => e, fun _ => a, fun _ => ⟨h1, h2⟩, fun r => by simp [hc], by simp, by simp⟩

theorem zp_intCast (m : ℤ) : zp Ωl (m : ℤ_[p]) = (m : Ωl) := by
  rw [zp, ← HahnSeries.C_apply, map_intCast, map_intCast, map_intCast]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem const_mem (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : algebraMap Ω X.K c ∈ KT X L :=
  (X.sl _).commutes c

theorem exp_const (X : GlobalTheory.KZ.Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ}
  {ψ : O0 p →+* Ωl} {io : KT X (p ^ n) →+* Ωl}

theorem io_const_of_mem (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) (hA : c ∈ A) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  classical
  obtain ⟨x', hx⟩ := hio.ev ⟨algebraMap Ω X.K c, const_mem X _ c⟩ {c} (fun r => by
    simp only [exp_const]
    split_ifs
    · exact ⟨hA, IntermediateField.subset_adjoin _ _ (by simp)⟩
    · exact ⟨zero_mem _, zero_mem _⟩)
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h2 := ev_single ψ (j c) ((hc.int c).1 hA) (hc.alg c) 1
    (fun r : ℤ => j ((X.exp (algebraMap Ω X.K c)).coeff ((r : ℚ) / (p : ℚ) ^ n))) (fun r => by
      simp only [exp_const]
      by_cases hr : r = 0
      · subst hr
        have : zp Ωl (1 : ℤ_[p]) = 1 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 1
        simp [this]
      · have : zp Ωl (0 : ℤ_[p]) = 0 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 0
        have h3 : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr) hp0
        simp [this, h3, HahnSeries.coeff_one, hr])
  have := (GlobalTheory.EvUniq.ev_unique p Ωl h T n ψ hψ _ _ _ _ _ hx h2).1
  rwa [map_one, map_one, mul_one] at this

theorem io_const (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  rcases A.mem_or_inv_mem c with hA | hA
  · exact io_const_of_mem h hc hψ hio c hA
  · have h1 := io_const_of_mem h hc hψ hio c⁻¹ hA
    have h2 : (⟨algebraMap Ω X.K c⁻¹, const_mem X _ c⁻¹⟩ : KT X (p ^ n)) = ⟨algebraMap Ω X.K c, const_mem X _ c⟩⁻¹ :=
      Subtype.ext (map_inv₀ _ _)
    rw [h2, map_inv₀, map_inv₀] at h1
    exact inv_injective h1

end Local

end GlobalTheory.Glue.IoInh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.MeanSquareConj

theorem mem_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  have e : ∀ x y : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) x) * (starRingEnd ℂ) y).im| =
      |((starRingEnd ℂ) x * y).im| := by
    intro x y
    rw [← map_mul, Complex.conj_im, abs_neg]
  simp only [Set.mem_setOf_eq, mem_conj]
  constructor
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, _, hx, _, hy, (e x y).symm⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) x, by simpa using hx, (starRingEnd ℂ) y, by simpa using hy, (e x y).symm⟩

theorem lattice_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      Λ.map (starRingEnd ℂ).toAddMonoidHom = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  refine ⟨(starRingEnd ℂ) w₁, (starRingEnd ℂ) w₂, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t h
    refine hli s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (t z : ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) t (fun z => (starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z =
      (starRingEnd ℂ) (U1 Λ ((starRingEnd ℂ) t) G ((starRingEnd ℂ) z)) := by
  unfold U1
  rw [area_conj, map_mul, ← Complex.exp_conj]
  simp only [map_add (f := _), map_sub, map_div₀, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

theorem sgStar_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) =
      fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)) := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ (lattice_conj Λ hΛ)
  have hder : ∀ z, HasDerivAt (fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv (sgStar Λ) ((starRingEnd ℂ) z))) z := by
    intro z
    have := (hd ((starRingEnd ℂ) z)).hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this
  funext z
  have := huniq _ (fun z => (hder z).differentiableAt) (by
    intro ω hω z
    rw [thetaTranslate_conjugateLattice, hU _ ((mem_conj Λ ω).1 hω), map_mul]
    congr 1
    have e : (starRingEnd ℂ) (ω / 2) = (starRingEnd ℂ) ω / 2 := by
      rw [map_div₀, map_ofNat]
    simp only [mem_conj, e]
    split_ifs <;> simp) z
  rw [(hder 0).deriv, map_zero, h1, map_one, one_mul] at this
  exact this.symm

theorem evenTheta_conjugateLattice (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t z : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) z =
      (starRingEnd ℂ) (GL3Theta.th0 Λ t ((starRingEnd ℂ) z)) := by
  unfold GL3Theta.th0
  rw [sgStar_conj Λ hΛ, thetaTranslate_conjugateLattice, thetaTranslate_conjugateLattice, map_div₀, map_zero, Complex.conj_conj]

theorem evenTheta_weightedNormSq_periodic (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t : ℂ)
    (x : ℂ) (hx : x ∈ Λ) (z : ℂ) :
    ‖GL3Theta.th0 Λ t (x + z)‖ ^ 2 * Real.exp (-Real.pi * ‖x + z‖ ^ 2 / area Λ) =
      ‖GL3Theta.th0 Λ t z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
  obtain ⟨⟨-, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hper : ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro z
    rw [← GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  unfold GL3Theta.th0
  simp only [norm_div, div_pow, div_mul_eq_mul_div]
  rw [GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq,
    show x + z + t = z + t + x by ring, hper]

theorem nrm1Sq_th0_map_conj_eq : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  intro Λ hΛ t
  have hex : ∀ A : AddSubgroup ℂ,
      (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ A = AddSubgroup.closure {w₁, w₂}) →
      IsAddFundamentalDomain A
        (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain A Fd volume) volume := by
    rintro A ⟨w₁, w₂, hli, rfl⟩
    obtain ⟨F, hF, -⟩ := GlobalTheory.GenusOneSup.exists_domain hli
    exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain _ Fd volume) ⟨F, hF⟩
  have hF := hex Λ hΛ
  have hF' := hex _ (lattice_conj Λ hΛ)
  have hcount : Countable Λ := by
    obtain ⟨w₁, w₂, -, h⟩ := hΛ
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      rw [h] at hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  set F := Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume
  set F' := Classical.epsilon fun Fd : Set ℂ =>
    IsAddFundamentalDomain (Λ.map (starRingEnd ℂ).toAddMonoidHom) Fd volume
  have hmp : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hF2 : IsAddFundamentalDomain Λ ((starRingEnd ℂ) ⁻¹' F') volume := by
    refine hF'.preimage_of_equiv (f := starRingEnd ℂ)
      (e := fun y => (⟨(starRingEnd ℂ) y, (mem_conj Λ _).1 y.2⟩ : Λ))
      hmp.quasiMeasurePreserving ⟨?_, ?_⟩ ?_
    · intro x y h
      exact Subtype.ext (star_injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨(starRingEnd ℂ) x, (mem_conj Λ _).2 (by simp)⟩, Subtype.ext (by simp)⟩
    · intro y x
      show (starRingEnd ℂ) ((starRingEnd ℂ) y + x) = (y : ℂ) + (starRingEnd ℂ) x
      simp
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, hF.measure_eq hF2,
    hF.setIntegral_eq hF2 (fun γ z => evenTheta_weightedNormSq_periodic Λ hΛ t γ γ.2 z), hmp.measure_preimage_emb hemb,
    ← hmp.setIntegral_preimage_emb hemb]
  simp only [evenTheta_conjugateLattice Λ hΛ, area_conj, Complex.conj_conj, Complex.norm_conj]

end GlobalTheory.MeanSquareConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulByIntegralIsClosed
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory


open Formalism.MainNotions.GL3Theta in
theorem mulBy_integral_isClosed : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsClosed {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} := by
  intro p _ g
  set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    rw [hLdef, GL3Theta.G1.lg]
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _
      (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p],
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
        ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
    intro e
    have hfin := PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e
    have hfin' : (Function.support fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite := hfin
    refine ⟨hfin'.toFinset, fun c => ?_⟩
    have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0 := by
      simp [hL0]
    have ha : PowerSeries.HasSubst (MvPowerSeries.C c * L) :=
      PowerSeries.HasSubst.of_constantCoeff_zero ha0
    show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _
    rw [PowerSeries.coeff_subst ha]
    have hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) =
        PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
      intro d
      rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]
    simp_rw [hterm]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hd
    simp only [PowerSeries.coeff_mk, one_smul] at h0
    rw [h0, mul_zero, mul_zero]
  have hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} =
      ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] |
        ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [hset]
  refine isClosed_iInter fun e => ?_
  obtain ⟨S, hS⟩ := key e
  have hfun : (fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) =
      fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) :=
    funext hS
  have hcont : Continuous fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    rw [hfun]
    fun_prop
  exact isClosed_le (continuous_norm.comp hcont) continuous_const

end GlobalTheory
end

