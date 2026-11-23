module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0009
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModuleStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0006

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapIntegrabilityStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.isBes_bessel_integral_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  first | exact @GlobalTheory.be_apply_isBes | exact GlobalTheory.be_apply_isBes | (intros; apply GlobalTheory.be_apply_isBes <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  first | exact @GlobalTheory.isCoef_ckOn_inCC | exact GlobalTheory.isCoef_ckOn_inCC | (intros; apply GlobalTheory.isCoef_ckOn_inCC <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCayleyWeighted
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CayleyTens

theorem gram_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    PI.UpqRep.Hpk k r j i = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold PI.UpqRep.Hpk Formalism.QuantumDeterminants.Hpk
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | omega

theorem gram_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (i j : Fin (2 * r + k + 1)) :
    ∑ d, (if ε d then (1 : ℂ) else -1) * ((starRingEnd ℂ) (Q⁻¹ i d) * Q⁻¹ j d) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv (by
    have := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    simpa [Matrix.star_eq_conjTranspose] using this)
  rw [← gram_symm, ← hQ.1.2, hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [PI.UpqRep.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  by_cases h : ε d <;> simp [h, mul_comm]

theorem hhJ_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (R : Rep k r) (x y : Fin (2 * r + k + 1) → R.smSub)
    (u v : Fin (2 * r + k + 1) → R.H)
    (hx : ∀ d, ((x d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • u c)
    (hy : ∀ d, ((y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • v c) :
    hhJ ε x y = hh (Formalism.QuantumDeterminants.Hpk k r) R u v := by
  unfold hhJ hh
  simp only [← gram_cayley hQ, Submodule.coe_inner, hx, hy, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem algTens_cayley : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDG ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr ep Q E F hRI hT hQ hE hF
  obtain ⟨io', pr', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI muI io pr Q E F hRI hT.raw hQ.1.1 hE hF
  refine ⟨io', pr', ⟨h1, h2, h3, h4, h5, ?_, ?_⟩, h7⟩
  · intro s t hst y y'
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 t y')]
    exact hT.orth s t hst _ y.2 _ y'.2
  · intro s
    refine ⟨ep s, hT.ep_sq s, fun y y' => ?_⟩
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 s y'), Submodule.coe_inner]
    exact hT.iso s _ y.2 _ y'.2

end GlobalTheory.CayleyTens
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientDerivativeBound
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem l2SG_of_ae_smul {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F G : Mx k r → Wp) (c : ℝ)
    (h : ∀ᵐ x ∂νq, F (Matrix.of x) = (c : ℂ) • G (Matrix.of x)) :
    PI.BesselPeriodGGP.l2SG νq F = ENNReal.ofReal (c ^ 2) * PI.BesselPeriodGGP.l2SG νq G := by
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow]
  congr 1
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg c), ← Real.norm_eq_abs, ← Complex.norm_real,
    ofReal_norm_eq_enorm]
  rfl

theorem scaled_bessel_isometric : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq l dd hDS hgap hok hS hl hd hnz
  refine ⟨Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 _, fun w hw => ?_⟩
  obtain ⟨v, hv, hlv⟩ := GlobalTheory.bessel_nonzero_on_translates hH k r ε mu R Wp z π l hDS hl.1 hnz
  obtain ⟨-, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  obtain ⟨-, -, hdd, hP⟩ := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS dd hd v hv (l v)
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hn : 0 < ‖l v‖ := norm_pos_iff.mpr hlv
  have hin : ⟪l v, l v⟫_ℂ = ((‖l v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; first | rfl | norm_cast | simp
  have hbe : ∀ y ∈ R.sm, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN y v (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l y := by
    intro y hy
    rw [(hl.2 y hy v hv).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hin]
  have hre : (⟪l v, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v (l v)⟫_ℂ).re = ‖l v‖ ^ 2 * ‖l v‖ ^ 2 := by
    rw [hbe v (hTK v hv), inner_smul_right, hin, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [l2SG_of_ae_smul νq _ (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v (l v))
    (Real.sqrt dd / ‖l v‖ ^ 2), hP w hw, hre, ← ENNReal.ofReal_mul (sq_nonneg _)]
  · congr 1
    rw [div_pow, Real.sq_sqrt hdd.le]
    field_simp
  · filter_upwards [hae] with x hx
    rw [hbe _ (hsm _ hx w hw), smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hn 2).ne']

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselSideBound
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hf : AEStronglyMeasurable f μ) (hc : 0 ≤ c) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal c ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← h]
    refine lintegral_congr fun x => ?_
    simp [enorm_eq_nnnorm]
  rw [h2, ← ENNReal.rpow_mul]
  norm_num

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ := by
  let L : S →ₗᵢ[ℂ] Lp F 2 μ :=
    { toFun := fun v => (hm v v.2).toLp (Φ v)
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd v v.2 w w.2)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c v v.2)
      norm_map' := fun v => by
        change ‖(hm v v.2).toLp (Φ v)‖ = _
        rw [Lp.norm_toLp, hn v v.2, ENNReal.toReal_ofReal (norm_nonneg _)]
        rfl }
  intro w hw w' hw'
  have h := L.inner_map_map ⟨w', hw'⟩ ⟨w, hw⟩
  rw [L2.inner_def] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae ?_
  filter_upwards [(hm w hw).coeFn_toLp, (hm w' hw').coeFn_toLp] with x h1 h2
  change _ = ⟪((hm w' hw').toLp (Φ w')) x, ((hm w hw).toLp (Φ w)) x⟫_ℂ
  rw [h1, h2]

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq Bm hDS hS hB
  obtain ⟨hae, -, -, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hDS hS
  obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hDS
  have hn : ∀ w ∈ R.sm, eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq =
      ENNReal.ofReal ‖w‖ := fun w hw =>
    eLpNorm_two_of_lintegral_sq _ _ (hmeas Bm hB.1 w hw) (norm_nonneg _) (hB.2 w hw)
  have hm : ∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq := fun w hw =>
    by rw [memLp_iff, hn w hw]; exact ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  refine integral_inner_of_isometric R.smSub
    (fun w (x : Formalism.QuantumDeterminants.Mt k r) => Bm (R.σ (Matrix.of x) w)) hm hn ?_ ?_
  · intro v hv w hw
    filter_upwards [hae] with x hx
    simp only [Pi.add_apply, map_add (f := _)]
    exact hB.1.1 _ (hsm _ hx v hv) _ (hsm _ hx w hw)
  · intro c v hv
    filter_upwards [hae] with x hx
    simp only [Pi.smul_apply, map_smul]
    exact hB.1.2.1 c _ (hsm _ hx v hv)

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecompositionStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.pieri_tensor_decomposition : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFamG lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  first | exact @GlobalTheory.TensExists.tens_exists | exact GlobalTheory.TensExists.tens_exists | (intros; apply GlobalTheory.TensExists.tens_exists <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuantumDeterminantEigenvalue
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

theorem qdet_smooth : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, ⟨Q0, hQ0, hDS⟩, hgp⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := _root_.GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := _root_.GlobalTheory.CapelliFreeAction.actU_qdet _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC k r ε mu R.H _ ⟨Q0, hQ0⟩ hgp hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimate
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.FamilyDerivativeExpansion.Kap

theorem mul_mem_GG {k r : ℕ} {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  simp only [GG, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem ae_pair {k r : ℕ} {U V : Set (Mx k r)} {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn V ν) :
    ∀ᵐ p ∂(μ.prod ν), Matrix.of p.1 ∈ U ∧ Matrix.of p.2 ∈ V := by
  haveI := hμ.1
  haveI := hν.1
  have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ U := ae_iff.2 hμ.2.2.1
  have h2 : ∀ᵐ x ∂ν, Matrix.of x ∈ V := ae_iff.2 hν.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem bessel_add {k r : ℕ} {R : Rep k r} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {A A' : R.H → Wp}
    (h : IsBes R z π A) (h' : IsBes R z π A') : IsBes R z π (fun v => A v + A' v) := by
  obtain ⟨h1, h2, h3, C, Ws, hW, h4⟩ := h
  obtain ⟨h1', h2', h3', C', Ws', hW', h4'⟩ := h'
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun g hg m hm v hv => ?_, max |C| |C'|, Ws ++ Ws', ?_, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, h1' v hv w hw]; abel
  · simp only [h2 a v hv, h2' a v hv, smul_add]
  · simp only [h3 g hg m hm v hv, h3' g hg m hm v hv, map_add (f := _), smul_add]
  · intro w hw
    rcases List.mem_append.1 hw with e | e
    exacts [hW w e, hW' w e]
  · have n : ∀ L : List (List (Mx k r)), 0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w v‖).sum :=
      fun L => List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)
    rw [List.map_append, List.sum_append, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ((h4 v hv).trans ?_) ((h4' v hv).trans ?_))
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (n _)
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) (n _)

theorem kappa_dual : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om l hR hRI hF hT hS hom
    hl hnz I lI hlI
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hbes, hS_eq, hsm⟩ :=
    GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om hR hRI hF hT.raw hom I
  obtain ⟨-, -, -, -, hTKsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨-, -, -, hIsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε (muI I) (RI I) (hRI I)
  obtain ⟨hadj, -, hev, -⟩ := GlobalTheory.T.frep_discrete_series_sum hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hprTK⟩ := GlobalTheory.T.tensor_raw_of_frep hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw
  have key : ∀ y ∈ (RI I).sm, ∀ v ∈ R.TK, (innerSL ℂ (l v)).smulRight (l (ev Γ R om (fun c => io I c y))) =
      (ep I : ℂ) • (innerSL ℂ (lI (∑ c, pr I c (tm R om v c)))).smulRight (lI y) := by
    intro y hy v hvTK
    have htmTK : ∀ c, tm R om v c ∈ R.TK := fun c => R.TK.smul_mem _ hvTK
    have hPTK : (∑ c, pr I c (tm R om v c)) ∈ (RI I).TK :=
      Submodule.sum_mem _ fun c _ => hprTK I c _ (htmTK c)
    rw [← (hl.2 _ (hsm.mem y hy) v hvTK).2, ← (hlI.2 y hy _ hPTK).2]
    unfold be
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pair hS.2.2.2.2.1 hS.2.2.2.2.2.1] with p hp
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨_, hp.1, _, hp.2, rfl⟩
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := mul_mem_GG hp.1.1 hp.2.1
    unfold beInt
    rw [← hS_eq _ hs y hy, ← hev, hadj I _ (hIsm _ hg y hy) _ (fun c => hTKsm _ (htmTK c)), smul_smul, mul_assoc]
  have hep : (ep I : ℂ) * (ep I : ℂ) = 1 := by rcases hT.ep_sq I with e | e <;> simp [e]
  constructor
  · obtain ⟨κ₀, hκ⟩ : ∃ κ₀ : ℂ, ∀ v ∈ R.TK, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v := by
      by_cases hI : NzOn (RI I) lI
      · obtain ⟨y, hy, hy0⟩ := hI
        have hyy : ⟪lI y, lI y⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hy0
        refine ⟨star ((ep I : ℂ) * ⟪lI y, l (ev Γ R om (fun c => io I c y))⟫_ℂ / ⟪lI y, lI y⟫_ℂ), fun v hv => ?_⟩
        refine ext_inner_right ℂ fun ξ => ?_
        have h4 := congrArg (fun T : Wp →L[ℂ] Wp => ⟪lI y, T ξ⟫_ℂ) (key y hy v hv)
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          inner_smul_right] at h4
        rw [inner_smul_left, starRingEnd_apply, star_star, div_mul_eq_mul_div, eq_div_iff hyy]
        linear_combination (-(ep I : ℂ)) * h4 - (⟪lI (∑ c, pr I c (tm R om v c)), ξ⟫_ℂ * ⟪lI y, lI y⟫_ℂ) * hep
      · refine ⟨0, fun v hv => ?_⟩
        rw [zero_smul]
        by_contra hne
        exact hI ⟨_, Submodule.sum_mem (RI I).smSub fun c _ =>
          (hT.raw.pr_sm I c).mem _ (R.smSub.smul_mem _ (hTKsm v hv)), hne⟩
    refine ⟨κ₀, fun v hv => ?_⟩
    by_contra hne
    have hB := bessel_add (hbes lI hlI.1) (Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 (-κ₀))
    obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π _ hR hB
      ⟨v, hv, fun e => hne (by simpa only [neg_smul, add_neg_eq_zero] using e)⟩
    exact hx0 (by rw [hκ x hx, neg_smul, add_neg_cancel])
  intro κ₀ hκ y hy
  obtain ⟨v, hvTK, hv0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π l hR hl.1 hnz
  have h3 := key y hy v hvTK
  rw [hκ v (hTKsm v hvTK)] at h3
  have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l v)) h3
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left] at h4
  have hne : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  apply smul_right_injective Wp hne
  simp only
  rw [h4, smul_smul, smul_smul]
  congr 1
  simp only [starRingEnd_apply]
  ring

end CompanionTheory.FamilyDerivativeExpansion.Kap
end Gp91
end

