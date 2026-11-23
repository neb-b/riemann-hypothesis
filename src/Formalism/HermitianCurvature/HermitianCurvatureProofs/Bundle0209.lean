module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0001
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0205
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrdLoc
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {k r : ℕ}

def gam (k r : ℕ) (a : Fin r) (x : Fin r → ℂ) : ℂ := ((‖x a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem gaugeF_eq (k r : ℕ) : gaugeF k r = fun x => ∏ a : Fin r, gam k r a x := by
  funext x
  unfold gaugeF Formalism.FourierDecayAlt.Q.resG
  simp only [smul_eq_mul, mul_one, gam, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [if_pos (by simp)]

theorem gam_smooth (a : Fin r) : ContDiffOn ℝ ∞ (gam k r a) (OmX r) := by
  intro x hx
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x
      (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt
  have h2 := Complex.ofRealCLM.contDiff.contDiffAt.comp x (h1.pow (Mdim k r a - 1))
  exact h2.contDiffWithinAt

theorem gaugeF_smooth : ContDiffOn ℝ ∞ (gaugeF k r) (OmX r) := by
  rw [gaugeF_eq]
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gaugeF_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : gaugeF k r c ≠ 0 := by
  rw [gaugeF_eq]
  exact Finset.prod_ne_zero_iff.mpr fun a _ =>
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem fderiv_zero_of_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : (Fin r → ℂ) → F}
    {x v : Fin r → ℂ} (hd : DifferentiableAt ℝ h x) (hc : ∀ t : ℝ, h (x + t • v) = h x) :
    fderiv ℝ h x v = 0 := by
  have hf : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h x v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf (by simp)
  have h2 : HasDerivAt (fun t : ℝ => h (x + t • v)) 0 0 := by
    simp_rw [hc]
    exact hasDerivAt_const _ _
  exact h1.unique h2

def gamO (k r : ℕ) (i : Fin r) (x : Fin r → ℂ) : ℂ := ∏ a ∈ Finset.univ.erase i, gam k r a x

theorem gamO_smooth (i : Fin r) : ContDiffOn ℝ ∞ (gamO k r i) (OmX r) := by
  unfold gamO
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gamO_line (i : Fin r) (x : Fin r → ℂ) (w : ℂ) (t : ℝ) :
    gamO k r i (x + t • (Pi.single i w : Fin r → ℂ)) = gamO k r i x := by
  unfold gamO
  refine Finset.prod_congr rfl fun a ha => ?_
  have hai : a ≠ i := Finset.ne_of_mem_erase ha
  simp only [gam, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, smul_zero, add_zero]

theorem gauge_split (i : Fin r) (x : Fin r → ℂ) : gaugeF k r x = gam k r i x * gamO k r i x := by
  rw [gaugeF_eq, gamO]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

private theorem wbar_smul_lemma {m : ℕ} (l : Fin m) (c : (Fin m → ℂ) → ℂ) (φ : (Fin m → ℂ) → X)
    (x : Fin m → ℂ) (hc : DifferentiableAt ℝ c x) (hφ : DifferentiableAt ℝ φ x) :
    wirtBar l (fun y => c y • φ y) x = c x • wirtBar l φ x + wirtBar l c x • φ x := by
  unfold Formalism.QuantumDeterminants.wirtBar
  have e : (fun y => c y • φ y) = c • φ := rfl
  rw [e, fderiv_smul hc hφ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem pbOp_gauge (i : Fin r) (f : (Fin r → ℂ) → X) (hf : f ∈ WSm r X) :
    pbOp i (fun x => gaugeF k r x • f x) =
      fun x => gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x) := by
  funext x
  show pbOp i (fun x => gaugeF k r x • f x) x =
    gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x)
  by_cases hx : x ∈ OmX r
  · have hO : IsOpen (OmX r) := by
      have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
        ext y
        simp [OmX]
      rw [e]
      exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
    have hfd : DifferentiableAt ℝ f x :=
      (hf.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hgi : DifferentiableAt ℝ (gam k r i) x := Formalism.FourierDecayAlt.P.Qx6.diff_gamma i _ hx
    have hgO : DifferentiableAt ℝ (gamO k r i) x :=
      ((gamO_smooth i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hsplit : (fun y => gaugeF k r y • f y) = fun y => gam k r i y • (gamO k r i y • f y) := by
      funext y
      rw [gauge_split, mul_smul]

    have hwO : wirtBar i (gamO k r i) x = 0 := by
      unfold Formalism.QuantumDeterminants.wirtBar
      rw [fderiv_zero_of_const hgO (gamO_line i x 1), fderiv_zero_of_const hgO (gamO_line i x Complex.I)]
      simp
    have hpg := Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma i hx (Mdim k r i - 1)
    unfold pbOp at hpg
    rw [if_pos hx] at hpg
    have key : star (x i) * wirtBar i (gam k r i) x =
        ((Mdim k r i - 1 : ℕ) : ℂ) / 2 * gam k r i x := by
      rw [← smul_eq_mul]
      exact hpg
    unfold pbOp
    rw [if_pos hx, if_pos hx, hsplit, wbar_smul_lemma i (gam k r i) (fun y => gamO k r i y • f y) x hgi (hgO.smul hfd),
      wbar_smul_lemma i _ _ x hgO hfd, hwO, gauge_split]
    simp only [smul_add, zero_smul, add_zero, smul_smul]
    rw [← mul_assoc (star (x i)) (wirtBar i (gam k r i) x), key]
    congr 1 <;> congr 1 <;> ring
  · unfold pbOp
    rw [if_neg hx, if_neg hx, hf.2 x hx]
    simp

theorem loc (Φ : (Fin r → ℂ) → X) (U : Set (Fin r → ℂ)) (c : Fin r → ℂ) (hU : IsOpen U) (hUO : U ⊆ OmX r)
    (hc : c ∈ U) (hΨ : ContDiffOn ℝ ∞ (fun c' => gaugeF k r c' • Φ c') U) :
    ∃ φ : (Fin r → ℂ) → X, φ ∈ WSm r X ∧ Φ =ᶠ[𝓝 c] φ ∧
      (fun c' => gaugeF k r c' • Φ c') =ᶠ[𝓝 c] (fun c' => gaugeF k r c' • φ c') := by
  have hO : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
      ext y
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc

  let χ : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hχ0 : ∀ z, z ∉ Metric.closedBall c (ε / 2) → χ z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support χ := by
      rw [χ.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    simpa [Function.mem_support] using h1
  let φ : (Fin r → ℂ) → X := fun y => χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
  have hev : Φ =ᶠ[𝓝 c] φ := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4))
      fun y hy => ?_
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (by linarith) hy)
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show Φ y = χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
    rw [h1, one_smul, inv_smul_smul₀ (gaugeF_ne (hUO hyU))]
  have hsm : ∀ y ∈ OmX r, ContDiffAt ℝ ∞ φ y := by
    intro y hyO
    by_cases hyU : y ∈ U
    · have hg := (gaugeF_smooth (k := k)).contDiffAt (hO.mem_nhds hyO)
      have hgi := hg.inv (gaugeF_ne hyO)
      have hΨ' := hΨ.contDiffAt (hU.mem_nhds hyU)
      exact χ.contDiff.contDiffAt.smul (hgi.smul hΨ')
    · have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hyU (hcl h)
      refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyc)
        fun z hz => ?_
      show χ z • ((gaugeF k r z)⁻¹ • (gaugeF k r z • Φ z)) = 0
      rw [hχ0 z hz, zero_smul]
  refine ⟨φ, ?_, hev, hev.mono fun y hy => congrArg (gaugeF k r y • ·) hy⟩
  show ContDiffOn ℝ ∞ φ (OmX r) ∧ ∀ x, x ∉ OmX r → φ x = 0
  refine ⟨fun y hy => (hsm y hy).contDiffWithinAt, fun y hy => ?_⟩
  have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hy (hUO (hcl h))
  show χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y)) = 0
  rw [hχ0 y hyc, zero_smul]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantShiftCoefficient
section
open MvPolynomial Finset

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem detShift_prod_coeff {σ ι : Type*} [Fintype ι] (h c : ι → MvPolynomial σ ℂ)
    (hh : ∀ i, (h i).IsHomogeneous 1) (hc : ∀ i, (c i).IsHomogeneous 0)
    (d : σ →₀ ℕ) (hd : d.degree = Fintype.card ι) :
    AddMonoidAlgebra.coeff (∏ i, (h i + c i)) d = AddMonoidAlgebra.coeff (∏ i, h i) d := by
  classical
  rw [Finset.prod_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · simp
  · intro S _ hS
    have hH : ((∏ i ∈ S, h i) * ∏ i ∈ univ \ S, c i).IsHomogeneous S.card := by
      have := (IsHomogeneous.prod S h (fun _ => 1) (fun i _ => hh i)).mul
        (IsHomogeneous.prod (univ \ S) c (fun _ => 0) (fun i _ => hc i))
      simpa using this
    apply hH.coeff_eq_zero
    rw [hd]
    intro hcard
    exact hS (Finset.eq_univ_of_card S hcard.symm)
  · intro hn
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hn

def detShiftSub : Fin 2 → Polynomial ℂ := ![Polynomial.X, -1]

theorem detShift_aeval_monomial (d : Fin 2 →₀ ℕ) (a : ℂ) :
    aeval detShiftSub (monomial d a) = Polynomial.C (a * (-1) ^ d 1) * Polynomial.X ^ d 0 := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [detShiftSub, Polynomial.algebraMap_eq, map_mul, map_pow, map_neg]
  ring

theorem detShift_aeval_coeff (Q : MvPolynomial (Fin 2) ℂ) (t j : ℕ) (hj : j ≤ t)
    (hQ : Q.IsHomogeneous t) :
    (aeval detShiftSub Q).coeff (t - j) =
      (-1) ^ j * AddMonoidAlgebra.coeff Q (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) := by
  classical
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  have hD0 : D 0 = t - j := by simp [hD]
  have hD1 : D 1 = j := by simp [hD]
  have hterm : ∀ d : Fin 2 →₀ ℕ, (aeval detShiftSub (monomial d (AddMonoidAlgebra.coeff Q d))).coeff (t - j) =
      if t - j = d 0 then AddMonoidAlgebra.coeff Q d * (-1) ^ d 1 else 0 := by
    intro d
    rw [detShift_aeval_monomial, Polynomial.coeff_C_mul_X_pow]
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single D]
  · rw [hterm, hD0, hD1, if_pos rfl, mul_comm]
  · intro d hd hne
    rw [hterm]
    split_ifs with h0
    · exfalso
      have hdeg : d.degree = t := by
        by_contra hne'
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero hne')
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      apply hne
      ext i
      fin_cases i
      · simp [hD0, ← h0]
      · simp only [Fin.mk_one, Fin.isValue, hD1]
        omega
    · rfl
  · intro hn
    rw [hterm, notMem_support_iff.mp hn]
    simp

theorem detShift_factor {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ) =
      ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) +
        (if σ i = i then -C ((i : ℕ) : ℂ) else 0) := by
  split_ifs <;> ring

theorem detShift_hom {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · rw [mul_comm]
    exact isHomogeneous_C_mul_X _ _

theorem detShift_const {t : ℕ} (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then -C ((i : ℕ) : ℂ) else 0) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 0 := by
  split_ifs
  · exact (isHomogeneous_C _ _).neg
  · exact isHomogeneous_zero _ _ _

theorem detShift_subst {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) :
    aeval detShiftSub (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i))) = M.charpoly := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.charpoly, Matrix.det_apply', map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : σ i = i
  · rw [h]
    simp [detShiftSub, Matrix.charmatrix_apply_eq, Polynomial.algebraMap_eq]
    ring
  · simp [detShiftSub, h, Polynomial.algebraMap_eq]

theorem determinant_shift_coefficient : DetShiftCoeff := by
  intro t M j hj
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  set Q : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) with hQdef
  have hdeg : D.degree = t := by
    rw [hD, map_add (f := _), Finsupp.degree_single, Finsupp.degree_single]
    omega
  have hQ : Q.IsHomogeneous t := by
    apply IsHomogeneous.sum
    intro σ _
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ)]
    simpa using (isHomogeneous_C (Fin 2) (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (univ : Finset (Fin t)) _ (fun _ => 1) (fun i _ => detShift_hom M σ i))
  have hPQ : AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i))) D =
      AddMonoidAlgebra.coeff Q D := by
    rw [hQdef, coeff_sum, coeff_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ), coeff_C_mul, coeff_C_mul]
    congr 1
    simp_rw [detShift_factor M σ]
    exact detShift_prod_coeff _ _ (detShift_hom M σ) (detShift_const σ) D (by simp [hdeg])
  rw [hPQ]
  have hC := detShift_aeval_coeff Q t j hj hQ
  rw [hQdef, detShift_subst] at hC
  rw [hC, ← hQdef, ← mul_assoc, ← mul_pow, show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

theorem haarSmul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) : B.IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_lmulM a).aemeasurable, h.left a ha]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_rmulF a).aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcT) (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => c⁻¹ • ν) h0
    simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hcT] using this

section norm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem massW_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero

theorem massW'_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero

theorem massW_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  exact measure_ne_top _ _

theorem massW'_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  exact measure_ne_top _ _

def normS (Bs : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r Wp Wq :=
  { Bs with
    μW := (Bs.μW Set.univ)⁻¹ • Bs.μW
    μW' := (Bs.μW' Set.univ)⁻¹ • Bs.μW'
    μN := D.muN k r
    haarW := haarSmul Bs.haarW (ENNReal.inv_ne_zero.2 (massW_ne_top Bs)) (ENNReal.inv_ne_top.2 (massW_ne_zero Bs))
    haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar r
    haarW' := haarSmul Bs.haarW' (ENNReal.inv_ne_zero.2 (massW'_ne_top Bs))
      (ENNReal.inv_ne_top.2 (massW'_ne_zero Bs)) }

theorem normS_μW_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW Set.univ = 1 := by
  show ((Bs.μW Set.univ)⁻¹ • Bs.μW) Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW_ne_zero Bs) (massW_ne_top Bs)]

theorem normS_μW'_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW' Set.univ = 1 := by
  show ((Bs.μW' Set.univ)⁻¹ • Bs.μW') Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW'_ne_zero Bs) (massW'_ne_top Bs)]

end norm

theorem towerAt : Formalism.FourierDecayAlt.P.PTie.TowerAt := by
  intro k r Wp Wq _ _ _ _ Bs
  obtain ⟨T, hT, hN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq (normS Bs) (normS_μW_univ_eq_one Bs) (normS_μW'_univ_eq_one Bs) rfl
  exact ⟨T, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, hN⟩

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem herm_mulVec' {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frameVec_facts (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hF : D.IsBaseFrame Bs ν' m₀) :
    inWb k r (m₀ *ᵥ ν') ∧ herm (Hpk k r) (m₀ *ᵥ ν') Bs.z = 0 ∧ herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by
  obtain ⟨hw, hz, hn, hm, hmz⟩ := hF
  have hU : m₀ᴴ * Hpk k r * m₀ = Hpk k r := hm.1
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.inWb_mulVec hm hw, ?_, by rw [herm_mulVec' hU]; exact hn⟩
  have h0 : herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ Bs.z') = 0 := by rw [herm_mulVec' hU]; exact hz
  rw [hmz] at h0
  set c : ℂ := ((√(Tz k r Bs.z' / Tz k r Bs.z) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr (div_pos Bs.T'_pos Bs.T_pos)).ne'
  have e : herm (Hpk k r) (m₀ *ᵥ ν') (c • Bs.z) = star c * herm (Hpk k r) (m₀ *ᵥ ν') Bs.z := by
    unfold herm
    rw [star_smul, smul_dotProduct, smul_eq_mul]
  rw [e] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (star_eq_zero.mp h) hc0
  · exact h

theorem frame_of (Bs : B.RealPlaceData k r Wp Wq) : ∃ (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ := by
  obtain ⟨Fb, hBw, hBo, hBz⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists Bs.z'_mem Bs.T'_pos
  set T : ℝ := Tz k r Bs.z with hTdef
  set T' : ℝ := Tz k r Bs.z' with hT'def
  have hT : 0 < T := Bs.T_pos
  have hT' : 0 < T' := Bs.T'_pos
  set c : ℝ := √(T' / T) with hc
  have hcc : c * c = T' / T := Real.mul_self_sqrt (div_pos hT' hT).le
  have hcw : inWb k r ((c : ℂ) • Bs.z) := Formalism.FourierDecayAlt.P.Qx8.inWb_smul Bs.z_mem _
  have hz' : herm (Hpk k r) Bs.z' Bs.z' = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_self']; push_cast; rfl
  have hcz : herm (Hpk k r) ((c : ℂ) • Bs.z) ((c : ℂ) • Bs.z) = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_smul_left', Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Qx8.herm_self']
    have hs : star (c : ℂ) = c := Complex.conj_ofReal c
    rw [hs, ← hTdef]
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have e1 : (c : ℂ) * (c : ℂ) = (T' : ℂ) / (T : ℂ) := by
      rw [← Complex.ofReal_mul, hcc]; push_cast; rfl
    rw [show (c : ℂ) * ((c : ℂ) * -(T : ℂ)) = -((c : ℂ) * (c : ℂ)) * (T : ℂ) by ring, e1]
    push_cast
    field_simp
  obtain ⟨m, hm, hmz, -⟩ := Formalism.FourierDecayAlt.P.Qx8.move Bs.z'_mem hcw (-T') (by linarith) hz' hcz
  refine ⟨Fb ⟨0, by have := Bs.k_pos; omega⟩, m, hBw _, hBz _ _ (List.mem_singleton_self _), ?_, hm, hmz⟩
  rw [hBo, ite_eq_left rfl]

end frame

end Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

namespace Formalism.FourierDecayAlt.P

theorem exists_normalized_tower : Formalism.FourierDecayAlt.P.PTie.TowerAt := HaarMassHermitianCurvature.towerAt

end Formalism.FourierDecayAlt.P
end
end

