module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AdjointMemCapSpSubA
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem adjoint_mem_CapSp_subA : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (T : V₂ →L[ℂ] V₁) (μ : Fin n → ℂ), IsRepW (n + 1) r z π₁ → IsRepW (n + 1) r z π₂ → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₁ h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₂ h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → (∀ h ∈ UWset (n + 1) r z, h *ᵥ B (Fin.last n) = B (Fin.last n) → T.comp (π₂ h) = (π₁ h).comp T) → ∀ v ∈ CapSp (subA (EB π₁ B)) μ, ContinuousLinearMap.adjoint T v ∈ CapSp (subA (EB π₂ B)) μ := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ B T μ h₁ h₂ hu₁ hu₂ hB hT v hv
  have hB' : IsFrameOf (n + 1) r [z, B (Fin.last n)] (fun a : Fin n => B a.castSucc) := by
    refine ⟨fun a => hB.1 _, fun a b => ?_, fun a x hx => ?_⟩
    · rw [hB.2.1]
      simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact hB.2.2 _ x (by simp [hx])
      · rw [hx, hB.2.1, if_neg (Fin.castSucc_lt_last a).ne]
  have hlie := GlobalTheory.intertwiner_EB_of_stabiliser V₂ V₁ (n + 1) r n z (B (Fin.last n)) π₂ π₁ T
    (fun a : Fin n => B a.castSucc) h₂ h₁ hB' (fun h hh he w => by
      have := congrArg (fun S : V₂ →L[ℂ] V₁ => S w) (hT h hh he)
      simpa using this)
  have hlie' : ∀ (a b : Fin n) (w : V₂),
      T (EB π₂ B a.castSucc b.castSucc w) = EB π₁ B a.castSucc b.castSucc (T w) := hlie
  have hadj : ∀ (a b : Fin n) (w : V₁),
      (ContinuousLinearMap.adjoint T).toLinearMap (subA (EB π₁ B) a b w) =
        subA (EB π₂ B) a b ((ContinuousLinearMap.adjoint T).toLinearMap w) := by
    intro a b w
    apply ext_inner_right ℂ
    intro y
    show inner ℂ (ContinuousLinearMap.adjoint T (EB π₁ B a.castSucc b.castSucc w)) y =
      inner ℂ (EB π₂ B a.castSucc b.castSucc (ContinuousLinearMap.adjoint T w)) y
    rw [ContinuousLinearMap.adjoint_inner_left,
      Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₁.1 h₁.2 hu₁ hB, Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₂.1 h₂.2 hu₂ hB,
      ContinuousLinearMap.adjoint_inner_left, hlie']
  rw [mem_CapSp] at hv ⊢
  intro w
  have hq := qminor_intertwine V₂ V₁ n n (subA (EB π₂ B)) (subA (EB π₁ B))
    (ContinuousLinearMap.adjoint T).toLinearMap hadj id id w v
  have hq' : ContinuousLinearMap.adjoint T (qdet (subA (EB π₁ B)) w v) =
      qdet (subA (EB π₂ B)) w (ContinuousLinearMap.adjoint T v) := hq
  rw [← hq', hv w, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCayleySideBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomentPointwise

theorem sum_sq_eq_trace {n : Type} [Fintype n] (A : Matrix n n ℂ) :
    ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_sq_conj {n : Type} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ j, ‖(Q * X * Q⁻¹) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h1
  apply Complex.ofReal_injective
  rw [sum_sq_eq_trace, sum_sq_eq_trace, hinv]
  have : (Q * X * Qᴴ)ᴴ * (Q * X * Qᴴ) = Q * (Xᴴ * X * Qᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exp_mem {k r : ℕ} {X : Mx k r} (hX : PI.UpqRep.InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ GG k r := by
  refine CCRuleCW.exp_mem_UH (Formalism.QuantumDeterminants.Hpk k r) _ ?_
  have hL : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem pointwise : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l Q E hR hS hl hQ hE g hg a w
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).1
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨hact, -, -, hcomp⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu mu mu R R R hR hR hR
  obtain ⟨X, hX, hXn, hXt⟩ := _root_.GlobalTheory.UnipotentElement.exists_element k r z hz hT g hg a
  obtain ⟨-, -, hexp⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q E hQ.1.1 hE
  obtain ⟨ladd, lsmul, leq, lcont⟩ := hl
  have hla : 0 ≤ lenA k r z g a.castSucc := Metric.infDist_nonneg
  have hla1 : 0 ≤ lenA k r z g a.succ := Metric.infDist_nonneg
  rcases hla.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  set L := lenA k r z g a.succ with hL
  have badd : ∀ v ∈ R.sm, ∀ v' ∈ R.sm, l (R.σ g (v + v')) = l (R.σ g v) + l (R.σ g v') := by
    intro v hv v' hv'
    rw [map_add (f := _)]; exact ladd _ (hsm g hg v hv) _ (hsm g hg v' hv')
  have bsmul : ∀ (c : ℂ), ∀ v ∈ R.sm, l (R.σ g (c • v)) = c • l (R.σ g v) := by
    intro c v hv
    rw [map_smul]; exact lsmul _ _ (hsm g hg v hv)
  have hder := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp (fun v => l (R.σ g v)) badd bsmul
    (hcomp Wp _ l (hact g hg) lcont) w w.2).2 X hX
  have hfun : (fun t : ℝ => l (R.σ g (R.σ (NormedSpace.exp ((t : ℂ) • X)) w))) =
      fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w) := by
    funext t
    obtain ⟨m, hm, hgm, hψ⟩ := hXt t
    rw [← hmul g hg _ (exp_mem hX t), hgm, hmul m hm.1 g hg, ← hψ]
    have := leq 1 (one_mem_UW k r z) m hm _ (hsm g hg w w.2)
    rw [Matrix.one_mul, hπ1] at this
    exact this
  have hd2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w))
      ((-(2 * (L : ℂ)) * Complex.I) • l (R.σ g w)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(2 * (L : ℂ) * (t : ℂ)) * Complex.I) (-(2 * (L : ℂ)) * Complex.I) 0 := by
      have := (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (2 * (L : ℂ))).neg).mul_const Complex.I
      simpa using this
    have h2 := h1.cexp.smul_const (l (R.σ g w))
    simpa using h2
  rw [hfun] at hder
  have heq := hd2.unique hder
  let B : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l (R.σ g v)
      map_add' := fun v v' => badd v v.2 v' v'.2
      map_smul' := fun c v => bsmul c v v.2 }
  have hsum : l (R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X w)) =
      ∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (Q * X * Q⁻¹) p.1 p.2 • l (R.σ g (E p.1 p.2 w)) := by
    have h1 : B (∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w) = ∑ c, ∑ e, (Q * X * Q⁻¹) c e • B (E c e w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type, hexp X hX w]
    refine Eq.trans ?_ h1
    show _ = l (R.σ g ((∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w : R.smSub) : R.H))
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have key := Formalism.HermitianLatticeCounting.P.majorant_cauchy_schwarz_holds Wp (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (fun p => (Q * X * Q⁻¹) p.1 p.2) (fun p => l (R.σ g (E p.1 p.2 w))) (l (R.σ g w))
    (-(2 * (L : ℂ)) * Complex.I) 1 _ L hpos (by simp [abs_of_nonneg hla1]) (heq.trans hsum)
    (by rw [Fintype.sum_prod_type, sum_sq_conj Q X hQ.2]; exact hXn)
  rw [Fintype.sum_prod_type, one_mul] at key
  exact key

end GlobalTheory.MomentPointwise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentityStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_formal_degree_identity : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  first | exact @GlobalTheory.BesselPhi.Ph_coeff | exact GlobalTheory.BesselPhi.Ph_coeff | (intros; apply GlobalTheory.BesselPhi.Ph_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormulaStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ dd : ℝ, (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → ∀ v ∈ R.TK, ∀ ξ : Wp, (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re ∧ 0 < dd ∧ ∀ w ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v ξ) = ENNReal.ofReal (‖w‖ ^ 2 * (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re / dd) := by
  first | exact @GlobalTheory.BesselNorm.norm_identity | exact GlobalTheory.BesselNorm.norm_identity | (intros; apply GlobalTheory.BesselNorm.norm_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapVanishingStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselConv.be_conv | exact GlobalTheory.BesselConv.be_conv | (intros; apply GlobalTheory.BesselConv.be_conv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPair
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

namespace CoefDecay

private theorem pair_bound (H : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDS ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h) (hok : GapOK k r h)
    (x y : R.H) (hx : x ∈ R.TK) (hy : y ∈ R.TK) :
    ∃ c : ℝ, ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪x, R.σ g y⟫_ℂ‖ ≤ c := by
  obtain ⟨C, Ws, -, hb⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx
  have hys : y ∈ R.sm := (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩
  have pg := GlobalTheory.BesselDecay.gN_pos' hg
  have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
    rw [← Real.rpow_add pg]; simp
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
  refine (mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)
  rw [mul_left_comm, h3, mul_one]

private theorem coef_bound : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ m : ℕ, ∃ c : ℝ, ∀ a b : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → (∀ Y ∈ b, B.unitLie k r Y) → a.length + b.length ≤ m → ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ‖ ≤ c := by
  intro H k r ε mu h R hR hgap hok x hx y hy m
  obtain ⟨M, xs, hxs, hxa⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR x hx m
  obtain ⟨N, ys, hys, hyb⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR y hy m
  choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)
  refine ⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩
  obtain ⟨co, hco, ea⟩ := hxa a ha (by omega)
  obtain ⟨co', hco', eb⟩ := hyb b hb (by omega)
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ea, eb, map_sum, sum_inner]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)
  rw [map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have n0 := norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ
  calc _ ≤ 1 * (1 * ‖⟪xs i, R.σ g (ys j)⟫_ℂ‖) := by
        gcongr
        · exact hco i
        · exact hco' j
    _ = _ := by ring

end CoefDecay

theorem isCoef_ckOn_inCC : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.CoeffDeriv.coeff_dLR hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := CoefDecay.coef_bound hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetFrameIndep
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

theorem capelli_det_frame_indep : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B B' : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsFrameOf k r [z] B → IsFrameOf k r [z] B' → ∀ w : ℂ, qdet (EB π B) w = qdet (EB π B') w :=
  fun _ _ _ _ _ _ _ _ _ _ hz hT hπ hB hB' w => Formalism.FourierDecayAlt.P.QrCap.capChange hz hT hπ hB hB' w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeighted
section
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

theorem algTens_cayley : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
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
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIsTypeOfParamEq
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

theorem exists_isometry_of_isType_of_param_eq :
    ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (u₁ u₂ : ℕ → ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π₁ u₁ → IsType (n + 1) r z π₂ u₂ → (∀ i ∈ Finset.Icc 1 (n + 1), u₁ i = u₂ i) → ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ h ∈ UWset (n + 1) r z, ∀ v, φ (π₁ h v) = π₂ h (φ v) := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ u₁ u₂ hz hT ht₁ ht₂ hu
  obtain ⟨hnt₁, hrep₁, hcont₁, hn₁, hirr₁, hcap₁⟩ := ht₁
  obtain ⟨hnt₂, hrep₂, hcont₂, hn₂, hirr₂, hcap₂⟩ := ht₂
  have hR₁ : IsRepW (n + 1) r z π₁ := ⟨hrep₁, hcont₁⟩
  have hR₂ : IsRepW (n + 1) r z π₂ := ⟨hrep₂, hcont₂⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), IsFrameOf (n + 1) r [z] B :=
    Qx8.frame_exists hz hT
  obtain ⟨g₁, q₁⟩ := frame_general_linear V₁ (n + 1) r (n + 1) z π₁ B hR₁ hB
  obtain ⟨g₂, q₂⟩ := frame_general_linear V₂ (n + 1) r (n + 1) z π₂ B hR₂ hB
  have i₁ : Irr (EB π₁ B) :=
    ⟨hnt₁, fun S hS => hirr₁ S (lie_stabilizer V₁ (n + 1) r z π₁ B hz hT hR₁ hB S hS)⟩
  have i₂ : Irr (EB π₂ B) :=
    ⟨hnt₂, fun S hS => hirr₂ S (lie_stabilizer V₂ (n + 1) r z π₂ B hz hT hR₂ hB S hS)⟩
  let m : Fin (n + 1) → ℂ := fun j => (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2
  have hc : ∀ w : ℂ, (∏ i ∈ Finset.Icc 1 (n + 1), (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 + (u₁ i : ℂ))) =
      cpol m w := by
    intro w
    rw [FrameExtension.prod_Icc_fin]
    unfold cpol
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [m]
    ring
  have c₁ : ∀ w v, qdet (EB π₁ B) w v = cpol m w • v := by
    intro w v
    rw [← q₁ w v, hcap₁ B hB w v, hc]
  have c₂ : ∀ w v, qdet (EB π₂ B) w v = cpol m w • v := by
    intro w v
    rw [← q₂ w v, hcap₂ B hB w v, ← hc]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by rw [hu i hi])
  obtain ⟨T, hTE⟩ := exists_linearEquiv_of_irreducible_capelli V₁ V₂ (n + 1) _ _ m g₁ g₂ i₁ i₂ c₁ c₂
  have hG := intertwiner_group_of_EB V₁ V₂ (n + 1) r z π₁ π₂ (T : V₁ →ₗ[ℂ] V₂) B hz hT hR₁ hR₂ hB hTE
  obtain ⟨φ, hφ⟩ := exists_isometry_of_intertwiner_of_irreducible V₁ V₂ (UWset (n + 1) r z)
    (fun h => π₁ h.1) (fun h => π₂ h.1) T (fun h v => hn₁ h.1 h.2 v) (fun h v => hn₂ h.1 h.2 v)
    (fun S hS => hirr₁ S (fun h hh v hv => hS ⟨h, hh⟩ v hv)) (fun h v => hG h.1 h.2 v)
  exact ⟨φ, fun h hh v => hφ ⟨h, hh⟩ v⟩

end GlobalTheory
end

