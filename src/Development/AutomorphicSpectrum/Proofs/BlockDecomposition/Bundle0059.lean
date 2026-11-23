module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0148

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumCosetSmulLinear
section
namespace GlobalTheory.CompanionTheory.HeckeSum

theorem finsum_coset_smul_linear :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (J : Type) [Fintype J] (c : J → ℂ) (f : J → G → ℂ),
      (∀ j, (Function.support fun q : G ⧸ K => f j q.out).Finite) → ∀ v : V,
      ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
        = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
  intro G V _ _ _ ρ K J _ c f hf v
  have hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite := by
    intro j
    refine (hf j).subset ?_
    intro q hq h0
    apply hq
    show f j q.out • ρ q.out v = 0
    have h0' : f j q.out = 0 := h0
    rw [h0', zero_smul]
  have hs' : ∀ j ∈ (Finset.univ : Finset J),
      (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite := by
    intro j _
    refine (hs j).subset ?_
    intro q hq h0
    apply hq
    show c j • (f j q.out • ρ q.out v) = 0
    have h0' : f j q.out • ρ q.out v = 0 := h0
    rw [h0', smul_zero]
  calc ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
      = ∑ᶠ q : G ⧸ K, ∑ j, c j • (f j q.out • ρ q.out v) := by
        refine finsum_congr fun q => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) :=
        finsum_sum_comm _ _ hs'
    _ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_finsum' (c j) (hs j)]

end GlobalTheory.CompanionTheory.HeckeSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
section
noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionProd
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open scoped FourierTransform

namespace GlobalTheory.CompanionTheory.TubeFourier

def planeCoord : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem planeCoord_apply (v : EuclideanSpace ℝ (Fin 2)) : planeCoord v = (v 0, v 1) := rfl

theorem continuous_planeCoord : Continuous planeCoord := by
  rw [show (planeCoord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun v => (v 0, v 1) from funext planeCoord_apply]
  fun_prop

theorem measurePreserving_planeCoord : MeasurePreserving planeCoord volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem inner_eq_rdot (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = rdot (planeCoord v) (planeCoord w) := by
  rw [planeCoord_apply, planeCoord_apply]
  simp [rdot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem fourier_comp_planeCoord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℝ × ℝ → X) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v => h (planeCoord v)) w =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y := by
  rw [Real.fourier_eq', ← measurePreserving_planeCoord.integral_comp'
    (fun y : ℝ × ℝ => Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y)]
  congr 1
  ext v
  rw [inner_eq_rdot]
  congr 2
  simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

theorem fourier_inversion_prod : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  intro X _ _ _ h hc hi hT y
  set T : ℝ × ℝ → X := fun t => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y with hTdef
  set f : EuclideanSpace ℝ (Fin 2) → X := fun v => h (planeCoord v) with hf
  have hfc : Continuous f := hc.comp continuous_planeCoord
  have hfi : Integrable f :=
    (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr hi
  have hFf : ∀ w, 𝓕 f w = T ((2 * Real.pi) • planeCoord w) := fun w => fourier_comp_planeCoord h w
  have hFi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => T ((2 * Real.pi) • planeCoord w) from funext hFf]
    have h1 : Integrable (fun t : ℝ × ℝ => T ((2 * Real.pi) • t)) := hT.comp_smul (by positivity)
    exact (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr h1
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) (planeCoord.symm y)
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (f := fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) (R := 2 * Real.pi)
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hrank] at hsub
  have hlhs : 𝓕⁻ (𝓕 f) (planeCoord.symm y) = ∫ s : ℝ × ℝ,
      (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s) := by
    rw [Real.fourierInv_eq', ← measurePreserving_planeCoord.integral_comp'
      (fun s : ℝ × ℝ => (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s))]
    congr 1
    ext w
    simp only [hFf, inner_eq_rdot, MeasurableEquiv.apply_symm_apply]
    congr 2
    simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    ring
  rw [hinv] at hlhs
  have hy : h y = f (planeCoord.symm y) := by simp [hf]
  rw [hy, hlhs, hsub, abs_of_pos (by positivity), ← Complex.coe_smul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformBound
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformContinuous
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem re_dot_pt_eq_rdot (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot]

theorem integrable_gaussian_plane :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h := h1.mul_prod h1
  have e : (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) =
      fun z : ℝ × ℝ => Real.exp (-1 * z.1 ^ 2) * Real.exp (-1 * z.2 ^ 2) := by
    funext z
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  exact h

theorem phi_joint_continuous (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ)
    (hG : Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)))
    (hb : ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :
    Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  have hform : ∀ y t : ℝ × ℝ, dot (pt x y) t =
      ((x.1 * t.1 + x.2 * t.2 : ℝ) : ℂ) + ((y.1 * t.1 + y.2 * t.2 : ℝ) : ℂ) * Complex.I := by
    intro y t
    apply Complex.ext <;> simp [dot, pt]
  have hdt : ∀ y : ℝ × ℝ, Continuous (fun t : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro y
    simp_rw [hform]
    fun_prop
  have hdy : ∀ t : ℝ × ℝ, Continuous (fun y : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro t
    simp_rw [hform]
    fun_prop
  have hnorm : ∀ y t : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t)‖ = Real.exp (-rdot x t) := by
    intro y t
    rw [Complex.norm_exp, Complex.neg_re, re_dot_pt_eq_rdot]
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨U, hU, M, hM⟩ := hb p₀.2
  have hr : Continuous (fun p : (ℝ × ℝ) × T => Real.exp (-rdot x p.1)) := by
    unfold rdot
    fun_prop
  have hV : ∀ᶠ p in 𝓝 p₀, Real.exp (-rdot x p.1) < Real.exp (-rdot x p₀.1) + 1 :=
    (hr.tendsto p₀).eventually (eventually_lt_nhds (lt_add_one _))
  have hU' : ∀ᶠ p in 𝓝 p₀, p.2 ∈ U := continuous_snd.continuousAt.preimage_mem_nhds hU
  unfold phi
  refine continuousAt_of_dominated
    (bound := fun y => (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)))) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    apply Continuous.aestronglyMeasurable
    exact (hdy p.1).smul (hG.comp (continuous_id.prodMk continuous_const))
  · filter_upwards [hV, hU'] with p hp1 hp2
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul, hnorm]
    have hg := hM p.2 hp2 y
    have hg' : ‖G p.2 (pt x y)‖ ≤ |M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) :=
      hg.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc Real.exp (-rdot x p.1) * ‖G p.2 (pt x y)‖
        ≤ Real.exp (-rdot x p.1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le
      _ ≤ (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_right hp1.le (mul_nonneg (abs_nonneg M) (Real.exp_pos _).le)
  · exact (integrable_gaussian_plane.const_mul _).const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (((hdt y).comp continuous_fst).smul (hG.comp (continuous_const.prodMk continuous_snd))).continuousAt

end GlobalTheory.CompanionTheory.TubeFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacter
section
open MeasureTheory Topology Pointwise
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.QKAvg

theorem mass_const {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Q K : Subgroup G) [LocallyCompactSpace Q]
    (hdec : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (δ : Q →* ℝ≥0) (hδc : Continuous δ)
    (hΔ : ∀ q : Q, Measure.modularCharacterFun q = δ q) (ν : Measure Q) [ν.IsHaarMeasure]
    [SecondCountableTopology Q] {E : Set G} (hEm : MeasurableSet E)
    (hEK : ∀ g, ∀ k ∈ K, g * k ∈ E ↔ g ∈ E) (g : G) :
    ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * g) * (δ q : ℝ≥0∞) ∂ν =
      ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
  obtain ⟨q0, hq0, k, hk, rfl⟩ := hdec g
  obtain ⟨p, hp⟩ : ∃ p : Q, p.1 = q0 := ⟨⟨q0, hq0⟩, rfl⟩
  have hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) :=
    ((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal
  have hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) =
      (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) := by
    intro q
    have hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E := by
      rw [← mul_assoc, Subgroup.coe_mul, hp]
      exact hEK _ k hk
    have h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]
    have h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1 := by
      classical
      by_cases hm : (q * p).1 ∈ E
      · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]
        rfl
      · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]
    rw [h3, h2]
    ring
  have hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞) := by
    rw [hΔ p]
  calc ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) ∂ν
      = ∫⁻ q : Q, (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) ∂ν := by
        congr 1
        funext q
        exact hpt q
    _ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν :=
        lintegral_const_mul _ (hF.comp (measurable_mul_const p))
    _ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) *
          ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) :=
        congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)
    _ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
        rw [hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one,
          one_mul]

theorem lintegral_mul_right_of_modular_law : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g
  haveI := hκ
  haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  haveI := hν
  obtain ⟨c, hc0, hctop, hdecomp⟩ :=
    GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ
  obtain ⟨S, hSc, hS1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := S * (K : Set G) with hE
  have hEc : IsCompact E := hSc.mul hK
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E := by
    intro h k hk
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h * k := hab
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      show a * (b * k⁻¹) = h
      rw [← mul_assoc, hab', mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h := hab
      refine ⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩
      show a * (b * k) = h * k
      rw [← mul_assoc, hab']
  set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef
  have hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M :=
    fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t
  have hT : IsCompact (((↑) : Q → G) ⁻¹' E) := hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc
  have hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν := by
    rw [hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ E
    · simp [Set.indicator_apply, hq]
    · simp [Set.indicator_apply, hq]
  have hMtop : M ≠ ⊤ := by
    rw [hMeq]
    exact (setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne
  have hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0 := by
    intro q hq
    have h1 := map_mul_eq_one δ (mul_inv_cancel q)
    rw [ENNReal.coe_eq_zero] at hq
    rw [hq, zero_mul] at h1
    exact zero_ne_one h1
  have hM0 : M ≠ 0 := by
    rw [hMeq]
    intro h0
    rw [lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False :=
      h0.mono fun q hq => hδ0 q hq
    rw [ae_iff] at h1
    have hTz : ν (((↑) : Q → G) ⁻¹' E) = 0 := by simpa using h1
    have hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS1
    have hpos := Measure.measure_pos_of_mem_nhds ν hV
    have hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E := fun q hq =>
      ⟨q.1, hq, 1, K.one_mem, mul_one _⟩
    have := measure_mono (μ := ν) hsub
    rw [hTz] at this
    exact (lt_irrefl 0 (hpos.trans_le this))
  have hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b := by
    intro a b
    have h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) =
        E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b := by
      intro q
      rw [hsq q b, mul_assoc]
    have hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) :=
      ((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul
        hδc.measurable.coe_nnreal_ennreal
    rw [lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]
  have hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ) := by
    have hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g) :=
      (measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k) (↑k * g)
  have hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ) := by
    have hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h :=
      ((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k * g⁻¹) ↑k
  have hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ =
      ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]
    simp only [mul_inv_cancel_right]
  rw [hA, hB] at hI
  exact (ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)

end GlobalTheory.CompanionTheory.QKAvg
end

