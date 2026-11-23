module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactor
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection.GSSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Mat

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

theorem cdo_det {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) : ContDiffOn ℝ ∞ (fun w => (f w).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem cdo_inv {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hd : ∀ w ∈ s, (f w).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((cdo_det f hf).inv hd).mul (cdo_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem cdo_mul {m : Type} [Fintype m] (f g : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w => g w i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w * g w) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

end Mat

theorem contDiff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => mat (nmat X w) τ a b := by
  show ContDiff ℝ ∞ fun w : V (nd X) => nmat X w τ a b
  unfold nmat
  split_ifs
  · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_Gw (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => PoinPf.Gw X w τ a b := by
  simp only [PoinPf.Gw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul
    (ContDiff.sum fun l _ => (contDiff_nmat X τ l a).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_nmat X τ k b)

theorem blk_det_on (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (c : Fin r) :
    ∀ w ∈ {w : V (nd X) | cpt X x w ∈ X.dom}, (FrameDegreeData.blk (PoinPf.Gw X w τ) c).det ≠ 0 := by
  intro w hw
  have h := FrameDegreeData.blk_det X hw τ c
  rwa [gram_cpt X hx] at h

theorem cdo_gsU (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (j c : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsU X w τ j c) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  simp only [gsU, FrameDegreeData.uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact contDiffOn_const
  · refine ContDiffOn.neg ?_
    simp only [Matrix.vecMul, dotProduct]
    refine ContDiffOn.sum fun m _ => ContDiffOn.mul ?_ ?_
    · exact (contDiff_Gw X τ c (Fin.castLE c.isLt.le m)).contDiffOn
    · exact cdo_inv (fun w => FrameDegreeData.blk (PoinPf.Gw X w τ) c)
        (fun a b => (contDiff_Gw X τ (Fin.castLE c.isLt.le a) (Fin.castLE c.isLt.le b)).contDiffOn)
        (blk_det_on X hx τ c) _ _
  · exact contDiffOn_const

theorem cdo_q (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ContDiffOn ℝ ∞ (fun w => ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) i j)
      {w : V (nd X) | cpt X x w ∈ X.dom} := by
  refine cdo_mul _ _ (fun a b => cdo_mul _ _ (fun a' b' => ?_) (fun a' b' => (contDiff_Gw X τ a' b').contDiffOn) a b)
    (fun a b => ?_) i j
  · exact cdo_gsU X hx τ b' a'
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (cdo_gsU X hx τ a b)

theorem q_eq_dOf (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) :
    ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k = FrameDegreeData.dOf X (cpt X x w) τ k := by
  simp only [FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsU]

theorem cdo_gsS (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (k : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsS X w τ k) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  set S := {w : V (nd X) | cpt X x w ∈ X.dom}
  have hpos : ∀ w ∈ S, 0 < sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re := by
    intro w hw
    rw [q_eq_dOf X hx w τ k]
    exact FrameDegreeData.sgn_dOf_pos X hw τ k
  have hf : ContDiffOn ℝ ∞ (fun w => sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re) S :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (cdo_q X hx τ k k))
  refine ContDiffOn.congr (ContDiffOn.inv (hf.sqrt fun w hw => (hpos w hw).ne')
    fun w hw => (Real.sqrt_pos.2 (hpos w hw)).ne') fun w hw => ?_
  have h := hpos w hw
  simp only [gsS]
  congr 2
  rcases FrameDegreeData.sgn_sq X.p0 k with hs | hs <;> rw [hs] at h ⊢
  · rw [one_mul] at h ⊢
    exact abs_of_pos h
  · rw [neg_one_mul] at h ⊢
    exact abs_of_neg (neg_pos.1 h)

theorem gsB_contDiffOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r},
    IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  intro E _ _ _ r X x hx τ a b
  have e : (fun w => gsB X w τ a b) = fun w => gsU X w τ a b * ((gsS X w τ b : ℝ) : ℂ) := by
    funext w
    simp only [gsB, Matrix.mul_diagonal]
  rw [e]
  exact (cdo_gsU X hx τ a b).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (cdo_gsS X hx τ b))

end GlobalTheory.SUChartSection.GSSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowOfConvSubConstantCoeffInvariantDerivation
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.LawDer TensorProduct

namespace GlobalTheory.LawDer

theorem convPow_ev_sub_constantCoeff_iterate_mem : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m →
    ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) →
    ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O),
      (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  intro p O _ G d c n m hp u φ hφ k
  induction k with
  | zero =>
    intro F
    obtain ⟨a, ha⟩ := GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd p O G d c n F
    rw [pow_zero, Function.iterate_zero, id, LinearMap.convOne_apply, Algebra.algebraMap_self,
      RingHom.id_apply, ha]
    exact m.mul_mem_right a hp
  | succ k ih =>
    intro F
    obtain ⟨t, ht⟩ := GlobalTheory.T.comul_chart_sub_subst_mem_p_smul p O G d c n F
    rw [pow_succ, LinearMap.convMul_apply, Function.iterate_succ_apply, sub_eq_iff_eq_add.1 ht,
      map_add, map_add, map_smul, map_smul]
    have h1 := GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max p O G d c n m hp u φ hφ (φ ^ k).ofConv (subst c.μ F)
    have h2 := ih (invDer c.μ u F)
    have h3 : (p : O) • LinearMap.mul' O O (TensorProduct.map (φ ^ k).ofConv φ.ofConv t) ∈ m := by
      rw [smul_eq_mul]; exact m.mul_mem_right _ hp
    have := m.add_mem (m.add_mem h1 h2) h3
    convert this using 1
    simp only [invDer]
    ring

end GlobalTheory.LawDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBalls
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.CoverCurv

theorem curv_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  intro n Y _ _ _ _ _ ι La _ A C H G hH t
  have hk : ∀ a : Fin C.m, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ Metric.closedBall (C.c a) (C.r a),
      ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤
        A.leviAt (C.idx a) (A.ph (G + k • H) (C.idx a)) ((A.chart (C.idx a)).symm v) ξ :=
    fun a => _root_.GlobalTheory.OTY.LeviLarge.curv_large n Y ι La A H G hH (C.idx a) _ t
      (isCompact_closedBall (C.c a) (C.r a)) (C.sub a)
  choose k0 hk0 using hk
  refine ⟨Finset.univ.sup k0, fun k hk a v hv ξ => ?_⟩
  exact hk0 a k (le_trans (Finset.le_sup (Finset.mem_univ a)) hk) v
    (Metric.ball_subset_closedBall hv) ξ

end GlobalTheory.OTY.CoverCurv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
section
noncomputable section

namespace GlobalTheory.CuspidalIdempotentCharacters

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

theorem isIndCuspChar_iff {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) :
    GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.IsIndCuspChar Pg r s χ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  constructor
  · rintro ⟨b, V, i1, i2, i3, σ, hc, hχ⟩
    exact ⟨_, fun PP => ⟨b PP, V PP, i1 PP, i2 PP, i3 PP, σ PP, hc PP, fun _ => rfl⟩, hχ⟩
  · rintro ⟨θ, hθ, hχ⟩
    choose b V i1 i2 i3 σ hc ht using hθ
    exact ⟨b, V, i1, i2, i3, σ, hc, fun g => (hχ g).trans (Finset.prod_congr rfl fun PP _ => ht PP (g PP))⟩

theorem sum_eq_lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (i : Fintype P.H) :
    ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K) = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum P χ := by
  obtain rfl : i = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH P := Subsingleton.elim _ _
  rfl

theorem genericMultOne_iff : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector
  refine forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun Pg =>
    forall_congr' fun r => forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun χ =>
    imp_congr (isIndCuspChar_iff Pg r s χ) ?_
  rw [← sum_eq_lvlSum (P0 Pg r ψ) χ]

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem eps_eq_lvlIdem (H : Subgroup G) (ψ : H →* Kˣ) :
    Formalism.MainNotions.PrimeDegreeVariant.eps (⟨H, ψ⟩ : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) = lvlIdem H ψ := by
  classical
  unfold Formalism.MainNotions.PrimeDegreeVariant.eps lvlIdem
  rw [Finset.smul_sum]
  symm
  refine Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    have : x ∉ H := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [this]
  · intro h
    simp [map_inv]

variable {W : Type} [AddCommGroup W] [Module K W]

theorem asAlgebraHom_lvlIdem (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) [Fintype H] :
    τ.asAlgebraHom (lvlIdem H ψ) = (Nat.card H : K)⁻¹ • ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) := by
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr (by congr!) fun h _ => ?_
  rw [Representation.asAlgebraHom_single, smul_smul, map_inv]

theorem isIdempotentElem_lvlIdem [CharZero K] (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) :
    IsIdempotentElem (τ.asAlgebraHom (lvlIdem H ψ)) := by
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [IsIdempotentElem, asAlgebraHom_lvlIdem, ← hT, smul_mul_smul_comm, h2, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

theorem finrank_eq_one_iff [CharZero K] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G)
    (ψ : H →* Kˣ) [Fintype H] :
    Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem H ψ))) = 1 ↔
      ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) = (Nat.card H : K) := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have h := (LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_lvlIdem τ H ψ)).trace
  have e : LinearMap.trace K W (τ.asAlgebraHom (lvlIdem H ψ)) =
      (Nat.card H : K)⁻¹ * ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [asAlgebraHom_lvlIdem, map_smul, map_sum, smul_eq_mul]
    simp [mul_comm]
  rw [← Nat.cast_eq_one (R := K), ← h, e, inv_mul_eq_one₀ hc, eq_comm]

end Idem

end GlobalTheory.CuspidalIdempotentCharacters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame
section
set_option autoImplicit false

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.CechPer

theorem sum_symm_smul_wedge_eq_zero {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (ω : Fin g → Ω[B⁄ℂ]) (S : Fin g → Fin g → B) (hS : ∀ a b, S a b = S b a) :
    ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) = 0 := by
  set X := ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) with hX
  have h1 : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    rw [hX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [wedge_swap (ω c) (ω b), hS c b, smul_neg]
  have h2 : (2 : B) • X = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h1
  have h3 : algebraMap ℂ B (2⁻¹) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ B) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc X = (algebraMap ℂ B (2⁻¹) * 2) • X := by rw [h3, one_smul]
    _ = 0 := by rw [mul_smul, h2, smul_zero]

theorem dOne_eq_sum_of_frame {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ])
    (hc : ∀ a b x, d a (d b x) = d b (d a x))
    (hf : ∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) (ξ : Ω[B⁄ℂ]) :
    dOne ℂ B ξ = ∑ b, ∑ c, d b ((d c).liftKaehlerDifferential ξ) • wedge ℂ B (ω b) (ω c) := by
  induction ξ using ind1 with
  | h0 => simp
  | ha x y hx hy =>
    rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_add (f := _), map_add (f := _), add_smul]
  | h x y =>
    have hD : ∀ z : B, D ℂ B z = ∑ a, d a z • ω a := fun z ↦ by
      simpa only [Derivation.liftKaehlerDifferential_comp_D] using hf (D ℂ B z)
    have h0 := sum_symm_smul_wedge_eq_zero ω (fun b c ↦ x * d b (d c y))
      (fun a b ↦ by rw [hc a b])
    have h1 : wedge ℂ B (D ℂ B x) (D ℂ B y) =
        ∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c) := by
      rw [hD x, hD y, LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [map_smul, LinearMap.map_smul₂, mul_smul]
    rw [dOne_smul_D, h1, ← zero_add (∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c)), ← h0,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, add_smul]

theorem dOne_eq_zero_of_frame_of_symm : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  intro B _ _ g d ω hc hd hf k hk
  have hl : ∀ c, (d c).liftKaehlerDifferential (∑ a, k a • ω a) = k c := fun c ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hd]
  rw [dOne_eq_sum_of_frame d ω hc hf]
  simp only [hl]
  exact sum_symm_smul_wedge_eq_zero ω (fun b c ↦ d b (k c)) hk

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.CMSize

theorem mulStable_one_add {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 + w) := by
  intro x hx
  rw [add_mul, one_mul]
  exact add_mem hx (h x hx)

theorem mulStable_one_sub {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 - w) := by
  intro x hx
  rw [sub_mul, one_mul]
  exact sub_mem hx (h x hx)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  intro l hl lam d L Ω P M hd hd4 hw hΩ hM hP hMP
  have hlp : l.Prime := hl.out
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero _))
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hs0 : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact (Real.sqrt_pos.mpr this).ne'
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hwdef
  have hre : w.re = 0 := by simp [hwdef]
  have him : w.im = Real.sqrt d := by simp [hwdef]
  have him0 : w.im ≠ 0 := by rw [him]; exact hs0
  have hw2 : w ^ 2 = -(d : ℂ) := by
    have h1 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
      rw [← Complex.ofReal_mul, hs]; simp
    rw [hwdef, mul_pow, Complex.I_sq, sq, h1]; ring
  have hn0 : Complex.normSq w = (d : ℕ) := by
    rw [Complex.normSq_apply, hre, him, hs]; simp
  have hn1 : Complex.normSq (1 + w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hn2 : Complex.normSq (1 - w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hsz := (_root_.GlobalTheory.SzRules.main l lam).1
  have hp : Sz l lam 0 (12 * (L.weierstrassP P / Ω ^ 2)) := by
    refine hsz (M ^ 2) _ (fun h => hM (hlp.dvd_of_dvd_pow h)) ?_
    have := ((_root_.GlobalTheory.WpFam.LatTorsVal.main L w Ω M hw him0 hΩ hM0).1 P hMP).1
    convert this using 1
    push_cast; ring
  have key : ∀ (α : ℂ) (n : ℕ), MulStable L α → Complex.normSq α = n → ¬ l ∣ n →
      Sz l lam 0 ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) -
        (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)) := by
    intro α n hα hn hln
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hln (dvd_zero _))
    refine hsz ((M * n) ^ 2) _ (fun h => ?_) ?_
    · rcases (Nat.Prime.dvd_mul hlp).1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hM h
      · exact hln h
    · have := _root_.GlobalTheory.IsogFormula.main L α w Ω P M n hw him0 hΩ hα hn hn0 hM0 hP hMP
      rwa [Nat.cast_pow]
  by_cases hld : l = d
  · subst hld
    rw [if_neg (by omega), if_pos rfl]
    have hnd : ¬ l ∣ 1 + l := by
      intro h
      have : l ∣ 1 := (Nat.dvd_add_left (dvd_refl l)).1 h
      exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
    have h1 := key (1 + w) (1 + l) (mulStable_one_add hw) hn1 hnd
    refine _root_.GlobalTheory.SzRamified.main l lam w _ _ hd4 hw2 hp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  · rw [if_neg hld]
    by_cases h3 : l = 3 ∧ d % 3 = 1
    · obtain ⟨rfl, h3⟩ := h3
      rw [if_neg (by omega)]
      have hnd : ¬ 3 ∣ 1 + d := by omega
      have h1 := key (1 + w) (1 + d) (mulStable_one_add hw) hn1 hnd
      have h2 := key (1 - w) (1 + d) (mulStable_one_sub hw) hn2 hnd
      refine _root_.GlobalTheory.ArithThreeInert.main lam d w _ (L.weierstrassP P / Ω ^ 2) h3 hw2 ?_ ?_
      · simpa only [Nat.cast_add, Nat.cast_one] using h1
      · simpa only [Nat.cast_add, Nat.cast_one] using h2
    · have hnd : ¬ l ∣ d := fun h => hld ((Nat.prime_dvd_prime_iff_eq hlp hd).1 h)
      have h1 := key w d hw hn0 hnd
      refine _root_.GlobalTheory.SzMult.main l lam d _ _ hd hd4 hld hp ?_ ?_
      · convert h1 using 1
        rw [hw2]; ring
      · rintro rfl
        have : ¬ d % 3 = 1 := fun h => h3 ⟨rfl, h⟩
        omega

end GlobalTheory.CMSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (exact GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (intros; apply GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique  <;> assumption)
end

