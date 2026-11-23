module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.StabilizerSplittingOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.NilpotentOrthogonalComplement

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

namespace C2x7

variable {k r : ℕ}

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma N_sub_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, one_mem_UW z, n, hn, by simp⟩

lemma UW_sub_S {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

end C2x7

open C2x5 C2x6 C2x7

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem one_parameter_differentiable : Formalism.FourierDecayAlt.Qr.OneParamDiff := by
  intro W _ _ _ φ h0 hadd hc
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := fun s t => hadd s t
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖φ s - 1‖ < 1 / 2 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have := H s (by rwa [Real.dist_eq, sub_zero])
    rwa [dist_eq_norm, h0] at this
  set h : ℝ := δ / 2 with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  set M : W →L[ℂ] W := ∫ s in (0 : ℝ)..h, φ s with hM
  have hbound : ‖M - h • (1 : W →L[ℂ] W)‖ ≤ 1 / 2 * |h - 0| := by
    have e : M - h • (1 : W →L[ℂ] W) = ∫ s in (0 : ℝ)..h, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 h) intervalIntegrable_const, intervalIntegral.integral_const,
        sub_zero]
    rw [e]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hpos.le] at hs
    refine (hball s ?_).le
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set tt : W →L[ℂ] W := 1 - h⁻¹ • M with htt
  have hnorm : ‖tt‖ < 1 := by
    have e : tt = h⁻¹ • (h • (1 : W →L[ℂ] W) - M) := by
      rw [htt, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc h⁻¹ * ‖M - h • (1 : W →L[ℂ] W)‖ ≤ h⁻¹ * (1 / 2 * |h - 0|) := by gcongr
      _ = 1 / 2 := by
        rw [sub_zero, abs_of_pos hpos, ← mul_assoc, mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ < 1 := by norm_num
  let u0 := Units.oneSub tt hnorm
  have hu0 : (u0 : W →L[ℂ] W) = h⁻¹ • M := by
    show 1 - tt = h⁻¹ • M
    rw [htt, sub_sub_cancel]
  set G : ℝ → W →L[ℂ] W := fun t => (∫ s in (0 : ℝ)..t + h, φ s) - ∫ s in (0 : ℝ)..t, φ s with hG
  have hφM : ∀ t, φ t * M = G t := by
    intro t
    have e1 := (ContinuousLinearMap.mul ℂ (W →L[ℂ] W) (φ t)).intervalIntegral_comp_comm (hint 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at e1
    rw [hM, ← e1]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + h)) (hint 0 t)]
    rw [show (fun s => φ t * φ s) = fun s => φ (t + s) from funext fun s => (hmul t s).symm,
      intervalIntegral.integral_comp_add_left φ t, add_zero]
  have hφ : φ = fun t => (h⁻¹ • G t) * (↑u0⁻¹ : W →L[ℂ] W) := by
    funext t
    rw [← hφM t, ← mul_smul_comm, ← hu0, Units.mul_inv_cancel_right]
  have hF : ∀ x, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, φ s) (φ x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨(h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W), fun t => ?_⟩
  have hGd : HasDerivAt G (φ (t + h) - φ t) t := ((hF (t + h)).comp_add_const t h).sub (hF t)
  let R : (W →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
    (((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip (↑u0⁻¹ : W →L[ℂ] W)).restrictScalars ℝ)
  have hd := R.hasFDerivAt.comp_hasDerivAt t (hGd.const_smul h⁻¹)
  have e : ∀ x, φ x = (⇑R ∘ (h⁻¹ • G)) x := by
    intro x
    rw [hφ]
    rfl
  have e2 : φ t ∘SL ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = R (h⁻¹ • (φ (t + h) - φ t)) := by
    show φ t * ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = (h⁻¹ • (φ (t + h) - φ t)) * (↑u0⁻¹ : W →L[ℂ] W)
    rw [hmul t h, show φ t * φ h - φ t = φ t * (φ h - 1) by rw [mul_sub, mul_one], ← mul_smul_comm, mul_assoc]
  rw [e2]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall e)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finsetSum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finsetSum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _

lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
section
theorem Formalism.FourierDecayAlt.P.stabilizer_split : Formalism.FourierDecayAlt.C2.C1ii :=
  PI.StabSplit.stabilizer_splitting_of_parts PI.StabSplit.fixed_point_subgroup PI.StabSplit.stabilizer_subgroup_flag
    PI.StabSplit.unipotent_nilpotent_radical PI.StabSplit.nilpotent_orthogonal_complement
end

