module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotential
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

theorem phla_laS_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 →
    phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  intro E _ _ _ r X x0 ho k z hz
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) =
      2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ) := fun i => by
    unfold laS
    by_cases h : (i : ℕ) < X.p0
    · rw [if_neg (not_le.2 h), if_pos h]; push_cast; ring
    · rw [if_pos (not_lt.1 h), if_neg h]; push_cast; ring
  have hL0 : L' 0 = 0 := by
    simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]
  have hsplit : ∑ i ∈ Finset.range r,
      (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) =
      2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) -
        (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]
  ring

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

open Matrix

noncomputable section

theorem normSq_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    Complex.normSq g.det = 1 := by
  have hJ : (Jf p q).det * (Jf p q).det = 1 := by
    rw [← det_mul, sumBdJf_mul_Jf, det_one]
  have hJ0 : (Jf p q).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h1 := congrArg det (show gᴴ * Jf p q * g = Jf p q from h)
  rw [det_mul, det_mul, det_conjTranspose] at h1
  have h2 : ((Complex.normSq g.det : ℂ) - 1) * (Jf p q).det = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : star g.det = (starRingEnd ℂ) g.det := rfl
    rw [this] at h1
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ0
  exact_mod_cast sub_eq_zero.1 h3

theorem norm_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    ‖g.det‖ = 1 := by
  have h1 := normSq_det_of_isUpq h
  rw [Complex.normSq_eq_norm_sq] at h1
  have h0 := norm_nonneg g.det
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Mx_self (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    KU.Mx X x0 x0 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl, Matrix.submatrix_one_equiv]

theorem norm_fac_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    ‖(KU.Mx X x0 (lact γ x0) τ).det / (KU.Mx X x0 (lact γ x0) τ).toBlocks₂₂.det ^ 2‖ =
      (Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det)⁻¹ := by
  rw [KU.Mx_lact X ho, Mx_self X ho, Matrix.mul_one, norm_div, norm_pow,
    norm_det_of_isUpq (KU.gm_upq X ho hγ τ), Complex.normSq_eq_norm_sq, one_div]

theorem one_add_fsq_le (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det :=
  sumBd_detD_ge (KU.gm_upq X ho hγ τ)

theorem norm_qS_lact_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧
      (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  intro E _ _ _ r X x0 ho γ hγ
  classical
  set N : X.Ψ → ℝ := fun τ => Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det with hNdef
  have hF : ∀ τ, 1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ N τ := fun τ => one_add_fsq_le X ho hγ τ
  have hN1 : ∀ τ, 1 ≤ N τ := fun τ => by
    have := sumBdFsq_nonneg (KU.gm X x0 γ τ).toBlocks₁₂; linarith [hF τ]
  have hq : ‖qS X x0 1 (lact γ x0)‖ = ∏ τ, (N τ)⁻¹ := by
    simp only [qS, pow_one]
    rw [norm_prod]
    exact Finset.prod_congr rfl fun τ _ => norm_fac_lact X ho hγ τ
  have ha0 : ∀ τ, 0 ≤ (N τ)⁻¹ := fun τ => inv_nonneg.2 (by linarith [hN1 τ])
  have ha1 : ∀ τ, (N τ)⁻¹ ≤ 1 := fun τ => inv_le_one_of_one_le₀ (hN1 τ)
  refine ⟨?_, fun h1 σ => ?_⟩
  · rw [hq]; exact Finset.prod_le_one₀ (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
  · rw [hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ)] at h1
    have hP0 : 0 ≤ ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := Finset.prod_nonneg fun τ _ => ha0 τ
    have hP1 : ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ ≤ 1 := Finset.prod_le_one₀ (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
    have hs : 1 ≤ (N σ)⁻¹ := by
      calc (1 : ℝ) = (N σ)⁻¹ * ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := h1.symm
        _ ≤ (N σ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hP1 (ha0 σ)
        _ = (N σ)⁻¹ := mul_one _
    have hNs : N σ ≤ 1 := by
      have hpos : 0 < N σ := by linarith [hN1 σ]
      rw [le_inv_comm₀ one_pos hpos, inv_one] at hs
      exact hs
    have hF0 : sumBdFsq (KU.gm X x0 γ σ).toBlocks₁₂ ≤ 0 := by linarith [hF σ]
    ext i j
    have he := sumBd_entry_le_fsq (KU.gm X x0 γ σ).toBlocks₁₂ i j
    have : Complex.normSq ((KU.gm X x0 γ σ).toBlocks₁₂ i j) = 0 :=
      le_antisymm (by linarith) (Complex.normSq_nonneg _)
    simpa using this

end

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists
section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj det_ne_zero_of_pos colMat exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

theorem coords_sum {d : ℕ} (π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ)) (S : Matrix (Fin g) (Fin g) ℂ) (k : Fin d) :
    π S k = ∑ i, ∑ j, S i j * π (Matrix.single i j 1) k := by
  conv_lhs => rw [matrix_eq_sum_single S]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (S i j) = S i j • Matrix.single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Pi.smul_apply, smul_eq_mul]

theorem perCoord_exists : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  intro O _ bar g ρ D
  classical
  refine ⟨Module.finrank ℂ (Tsp bar ρ), fun P₀ hP₀ => ?_⟩
  set d := Module.finrank ℂ (Tsp bar ρ)
  let bV := Module.finBasis ℂ (Tsp bar ρ)
  obtain ⟨p, hp⟩ := (Tsp bar ρ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let ι : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := (Tsp bar ρ).subtype ∘ₗ bV.equivFun.symm.toLinearMap
  let π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ) := bV.equivFun.toLinearMap ∘ₗ p
  have hιeq : ∀ b, ι b = ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) := fun b => rfl
  have hιT : ∀ b, ι b ∈ Tsp bar ρ := fun b => by rw [hιeq]; exact Submodule.coe_mem _
  have hpv : ∀ v : Tsp bar ρ, p ((Tsp bar ρ).subtype v) = v := fun v => LinearMap.congr_fun hp v
  have hπι : ∀ b, π (ι b) = b := fun b => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) = (Tsp bar ρ).subtype (bV.equivFun.symm b) from rfl, hpv, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ S ∈ Tsp bar ρ, ι (π S) = S := fun S hS => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show S = (Tsp bar ρ).subtype ⟨S, hS⟩ from rfl, hpv, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨α, β, hαβ⟩ := exists_colMat_per hP₀
  obtain ⟨M₀, hM₀h, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hdet₀ : M₀.det ≠ 0 := det_ne_zero_of_pos hpos₀
  have hu₀ : IsUnit M₀.det := isUnit_iff_ne_zero.2 hdet₀
  have hA₀ : colMat α P₀ = 1 ∧ colMat β P₀ = 0 :=
    realMap_inj (ext_per hP₀ fun x => by rw [← hαβ P₀ hP₀]; simp [realMap_apply])
  let Cf : (D.La → Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun f => (colMat α f)⁻¹ * colMat β f
  let Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ) := fun P => π ((Cf P)ᵀ * M₀)
  let Cof : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (ι b * M₀⁻¹)ᵀ
  let Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)) := fun b => (realMap 1 (Cof b)).toAddMonoidHom.comp P₀
  have hQ : ∀ b x, Q b x = realMap 1 (Cof b) (P₀ x) := fun b x => rfl
  have hCofT : ∀ b, (Cof b)ᵀ * M₀ = ι b := fun b => by
    simp only [Cof, transpose_transpose, nonsing_inv_mul_cancel_right _ _ hu₀]
  obtain ⟨U, hUg, hUo, hU0⟩ := mem_nhds_iff.1 (_root_.GlobalTheory.PosOpen.posopen M₀ hpos₀)
  have hQper : ∀ b, Cof b ∈ U → IsPeriod D ρ (Q b) := fun b hb => by
    obtain ⟨hY, hX, hpos⟩ := hUg hb
    have hT : (Cof b)ᵀ * M₀ ∈ Tsp bar ρ := by rw [hCofT]; exact hιT b
    obtain ⟨hMh, hMim⟩ := GlobalTheory.T.riemann_relation_converse_conjAffine M₀ (Cof b) hM₀h hdet₀ hT.1 hY
    refine GlobalTheory.T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (Cof b)) _ hP₀ (realMap_one_injective hX) (fun a x => ?_) hMh hpos (fun x y => ?_)
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, star_mulVec_map, mulVec_mulVec,
        ← comm_of_mem_Tsp hP₀ hM₀ hdet₀ hT a, ← mulVec_mulVec, mulVec_add]
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, hMim, hM₀]
  have hCofc : Continuous Cof := by
    exact (Continuous.matrix_mul ι.continuous_of_finiteDimensional continuous_const).matrix_transpose
  have hCof0 : Cof 0 = 0 := by simp [Cof, ι]
  have hZ0 : Z P₀ = 0 := by simp [Z, Cf, hA₀]
  have hcol : ∀ γ : Fin g → (D.La →₀ ℂ), Continuous fun f : D.La → Fin g → ℂ => colMat γ f := fun γ =>
    continuous_matrix fun i j => by simp only [colMat, of_apply]; fun_prop
  have hCfc : ContinuousAt Cf ⇑P₀ := by
    refine ContinuousAt.mul ?_ (hcol β).continuousAt
    refine ContinuousAt.comp (f := fun f => colMat α f) ?_ (hcol α).continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [hA₀.1, det_one]
    exact (Ring.inverse_eq_inv' (G₀ := ℂ)) ▸ continuousAt_inv₀ one_ne_zero
  have hCf0 : Cf P₀ = 0 := by simp [Cf, hA₀]
  have hdetc : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := (hcol α).matrix_det
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hdetc.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀.1]) |>.and
      (hCfc.preimage_mem_nhds (hUo.mem_nhds (by rw [hCf0]; exact hU0))))
  refine ⟨Cof ⁻¹' U, Q, Z, s, ε, hUo.preimage hCofc, hε, ⟨fun b hb => hQper b hb, fun x => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let F : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => Cof b *ᵥ star (P₀ x)
        map_add' := fun b b' => by simp only [Cof, map_add (f := _), Matrix.add_mul, transpose_add, add_mulVec]
        map_smul' := fun c b => by
          simp only [Cof, map_smul, Matrix.smul_mul, transpose_smul, smul_mulVec, RingHom.id_apply] }
    have hF : Differentiable ℂ (fun b => F b) := (LinearMap.toContinuousLinearMap F).differentiable
    refine ((differentiableOn_const (P₀ x)).add hF.differentiableOn).congr fun b _ => ?_
    rw [hQ, realMap_apply, one_mulVec]; rfl
  · show Cof (Z P₀) ∈ U
    rw [hZ0, hCof0]; exact hU0
  · ext x
    rw [hZ0, hQ, hCof0, realMap_apply, one_mulVec, zero_mulVec, add_zero]
  · intro b hb _
    have h1 := hαβ (Q b) (hQper b hb)
    have key : colMat α (Q b) = 1 ∧ colMat β (Q b) = Cof b :=
      realMap_inj (ext_per hP₀ fun x => by rw [← h1 x, hQ])
    show π (((colMat α (Q b))⁻¹ * colMat β (Q b))ᵀ * M₀) = b
    rw [key.1, key.2, inv_one, Matrix.one_mul, hCofT, hπι]
  · intro P hP hn
    obtain ⟨hdetA, hCU⟩ := hs _ hn
    have hu : IsUnit (colMat α P).det := isUnit_iff_ne_zero.2 hdetA
    have hT := mem_Tsp_of_period hP₀ hP hM₀ (hαβ P hP) hdetA
    have hCofZ : Cof (Z P) = Cf P := by
      show (ι (π ((Cf P)ᵀ * M₀)) * M₀⁻¹)ᵀ = Cf P
      rw [hιπ _ hT, mul_nonsing_inv_cancel_right _ _ hu₀, transpose_transpose]
    refine ⟨show Cof (Z P) ∈ U by rw [hCofZ]; exact hCU, Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hu),
      fun x => ?_⟩
    rw [hQ, hCofZ]
    change P x = colMat α P *ᵥ realMap 1 ((colMat α P)⁻¹ * colMat β P) (P₀ x)
    rw [hαβ P hP x, realMap_apply, realMap_apply, one_mulVec, mulVec_add, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hu]
  · intro P P' hP hP' _ _ h hh
    let H := LinearMap.toMatrix' h.toLinearMap
    have hHv : ∀ v, h v = H *ᵥ v := fun v => (LinearMap.toMatrix'_mulVec _ v).symm
    have hHinv : LinearMap.toMatrix' h.symm.toLinearMap * H = 1 := by
      rw [← LinearMap.toMatrix'_comp, show h.symm.toLinearMap ∘ₗ h.toLinearMap = LinearMap.id from
        LinearMap.ext fun v => h.symm_apply_apply v, LinearMap.toMatrix'_id]
    have hHu : IsUnit H.det := isUnit_det_of_left_inverse hHinv
    have key : colMat α P' = H * colMat α P ∧ colMat β P' = H * colMat β P :=
      realMap_inj (ext_per hP₀ fun x => by
        rw [← hαβ P' hP' x, hh x, hαβ P hP x, hHv]
        simp only [realMap_apply, mulVec_add, mulVec_mulVec])
    show π (((colMat α P')⁻¹ * colMat β P')ᵀ * M₀) = π (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀)
    rw [key.1, key.2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H⁻¹ H, nonsing_inv_mul _ hHu,
      Matrix.one_mul]
  · intro m B' P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B' :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb)).1))
    refine differentiableOn_pi.2 fun k => ?_
    show DifferentiableOn ℂ (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) B'
    have hd : DifferentiableOn ℂ (fun b => ∑ i : Fin g, ∑ j : Fin g,
        (∑ l : Fin g, (∑ n : Fin g, (colMat α (P b))⁻¹ l n * colMat β (P b) n i) * M₀ l j) *
          π (Matrix.single i j 1) k) B' :=
      DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (DifferentiableOn.fun_sum fun l _ => (DifferentiableOn.fun_sum fun n _ =>
          (hinv _ _).mul (hc β _ _)).mul_const _).mul_const _
    apply hd.congr
    intro b _
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
      (coords_sum π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k)

end

end GlobalTheory.PerCoordU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.LastPeriod

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum

theorem gramSum_one {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) :
    gramSum hN (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]
  split_ifs <;> first | rfl | omega

theorem coefOpLe_brAt (hL : LastMapNorm) {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (T : ℝ) (hT : 0 < T) (t : ι → K)
    (ht : ∀ τ, star (σ (t τ)) * σ (t τ) = (T : ℂ)) :
    CoefOpLe σ lam sg (Br.brAt hN lam sg t) (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg) := by
  intro x
  have h := (hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1)
    (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ))
    (fun τ => by simpa using ht τ)).2.2.1
    ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  simp only [gramSum_one] at h
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h
  simp only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem sqAt_eq_dot {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (x : Formalism.L2.DIV.VV K lam) :
    sqAt σ lam x = (star (fun i => σ ((bVV K lam).repr x i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map σ *ᵥ
      fun i => σ ((bVV K lam).repr x i)).re := by
  simp only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

theorem sum_pair_le {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (B : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K sg) (t : ℝ)
    (hB : CoefOpLe σ lam sg B t) {C : Type} [Fintype C] (w : C → ℕ) (x : C → Formalism.L2.DIV.VV K lam)
    (y : C → Formalism.L2.DIV.VV K sg) :
    ‖σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c))‖ ^ 2 ≤
      t * (∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ lam (x c)) * ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (y c) := by
  have hG := (gramB_posDef sg σ).posSemidef
  have hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re =
      ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c) := fun z => by
    rw [wForm, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sqAt_eq_dot, ← Complex.re_ofReal_mul]
    push_cast
    rfl
  have e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, wForm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, star_star, map_pairBK]
  have h := wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))
  rw [wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3] at h
  have h0 := (Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1
  rw [hre] at h0
  rw [hre fun c => B (x c), hre] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ h0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem sqAt_nonneg {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : 0 ≤ sqAt σ lam x := by
  rw [sqAt_eq_dot]
  exact (Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem re_inv_mul (w : ℕ) (z : ℂ) : ((w : ℂ)⁻¹ * z).re = (w : ℝ)⁻¹ * z.re := by
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

end GlobalTheory.LastPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfRowTestOfScalar
section
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

end Concrete

end GlobalTheory.OneFormTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  first | exact @GlobalTheory.ringHom_charEnd_of_torusExtension | exact GlobalTheory.ringHom_charEnd_of_torusExtension | (intros; apply GlobalTheory.ringHom_charEnd_of_torusExtension <;> assumption)
end

