module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0285
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConstMin

variable {n : ℕ}

private lemma hs_eq_re_trace' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = ((X * Xᴴ).trace).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_unitary_sub_one {u : Matrix (Fin n) (Fin n) ℂ} (hu : uᴴ * u = 1) :
    Formalism.REAL.hs (u - 1) = 2 * ((1 : Matrix (Fin n) (Fin n) ℂ).trace).re - 2 * (u.trace).re := by
  have h2 : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  rw [hs_eq_re_trace', conjTranspose_sub, conjTranspose_one]
  have e : (u - 1) * (uᴴ - 1) = 1 - u - uᴴ + 1 := by
    rw [sub_mul, mul_sub, mul_sub, h2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem re_trace_eq_zero_of_max (X u : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • X) * u).trace).re ≤ (u.trace).re) : ((X * u).trace).re = 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let φ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin n) ℝ ℂ)
  have hφ : ∀ M, φ M = (M.trace).re := fun M => rfl
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * u)
      (NormedSpace.exp ((0 : ℝ) • X) * X * u) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).mul_const u
  have hf : HasDerivAt (fun t : ℝ => φ (NormedSpace.exp (t • X) * u))
      (φ (NormedSpace.exp ((0 : ℝ) • X) * X * u)) 0 :=
    φ.hasFDerivAt.comp_hasDerivAt 0 hd
  have hmax : IsLocalMax (fun t : ℝ => φ (NormedSpace.exp (t • X) * u)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [hφ, zero_smul, NormedSpace.exp_zero, Matrix.one_mul]
    have := h t
    rwa [GlobalTheory.IwTangent.coe_smul_eq] at this
  have h0 := hmax.hasDerivAt_eq_zero hf
  simpa [hφ, NormedSpace.exp_zero] using h0

theorem uMat_mul' {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem maxK_mul {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) (hh : h ∈ maxK ε) : g * h ∈ maxK ε := by
  have hg' : (uMat g)ᴴ * uMat g = 1 := hg
  have hh' : (uMat h)ᴴ * uMat h = 1 := hh
  show (uMat (g * h))ᴴ * uMat (g * h) = 1
  rw [uMat_mul', conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
    Matrix.one_mul, hh']

theorem exists_nearest : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  intro n ε S d E hcut hSK hE k hk
  obtain ⟨H, hHS, hSc⟩ := IsCut.subgroup hcut
  have hmemS : ∀ g, g ∈ S ↔ g ∈ H := fun g => by rw [← hHS]; rfl
  have hcpt : IsCompact S := (isCompact_maxK ε).of_isClosed_subset hSc hSK
  have hne : S.Nonempty := ⟨1, (hmemS 1).2 H.one_mem⟩
  have hcont : Continuous fun l : Formalism.REAL.UJ ε => nrm (uMat (l * k) - 1) :=
    (continuous_nrm_uMat ε).comp (continuous_mul_const k)
  obtain ⟨l, hlS, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  refine ⟨l, hlS, ?_, fun l' hl' => hmin hl'⟩
  set w := uMat (l * k) with hw
  have hwK : l * k ∈ maxK ε := maxK_mul (hSK hlS) hk
  have hwU : wᴴ * w = 1 := hwK
  funext i
  have hflow := (GlobalTheory.IwTangent.lie_algebra_of_isCut n ε S d E hcut).1 (E i)
    (Submodule.subset_span ⟨i, rfl⟩)
  have hle : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • E i) * w).trace).re ≤ (w.trace).re := by
    intro t
    obtain ⟨g, hgS, hg⟩ := hflow t
    have hgl : g * l ∈ S := (hmemS _).2 (H.mul_mem ((hmemS _).1 hgS) ((hmemS _).1 hlS))
    have hv : uMat (g * l * k) = NormedSpace.exp ((t : ℂ) • E i) * w := by
      rw [mul_assoc, uMat_mul', hg]
    have hvK : (uMat (g * l * k))ᴴ * uMat (g * l * k) = 1 := maxK_mul (hSK hgl) hk
    have hn : nrm (w - 1) ≤ nrm (uMat (g * l * k) - 1) := hmin hgl
    have hsq : Formalism.REAL.hs (w - 1) ≤ Formalism.REAL.hs (uMat (g * l * k) - 1) := by
      rw [← nrm_sq, ← nrm_sq]
      exact pow_le_pow_left₀ (nrm_nonneg _) hn 2
    rw [hs_unitary_sub_one hwU, hs_unitary_sub_one hvK, hv] at hsq
    linarith
  have hz : ((E i * w).trace).re = 0 := re_trace_eq_zero_of_max (E i) w hle
  have htr : ((E i).trace).re = 0 := by
    have h1 := congrArg (fun M => (M.trace).re) (hE i)
    simp only [trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_neg, Complex.neg_re] at h1
    linarith
  have hcomm : ((w * E i).trace).re = ((E i * w).trace).re := by rw [trace_mul_comm]
  show ((( w - 1) * (E i)ᴴ).trace).re = 0
  rw [hE i, sub_mul, Matrix.mul_neg, Matrix.mul_neg, Matrix.one_mul, trace_sub, trace_neg, trace_neg,
    Complex.sub_re, Complex.neg_re, Complex.neg_re, hcomm, hz, htr]
  simp

end GlobalTheory.IwConstMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := _root_.GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR
  haveI := _root_.GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendFreeTupleGramHermitianFrame
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.FrameExtend

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hR_sub_sum_right {m : ℕ} (x w : Fin n → R ⊗[F] E) (c : Fin m → R ⊗[F] E)
    (u : Fin m → Fin n → R ⊗[F] E) :
    hR R σ J x (w - ∑ a, c a • u a) = hR R σ J x w - ∑ a, c a * hR R σ J x (u a) := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Alg


open GlobalTheory.FrameGram in
theorem extend_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP y hy hgram
  have hinv : ∀ x, σ (σ x) = x := conj_invol hσ
  obtain ⟨_, hGh, _, hG0, _⟩ := std_frame_gram F E σ hσ n J hJ r P T hP
  have hPs := hP
  obtain ⟨_, hff0, hef, _, hfz, _, _⟩ := hPs
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := PI.VolStabS.isReduced_tens_field F E (Fv F v)
  have : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let s := sigR (Fv F v) σ
  have hsw : ∀ x w, s (hR (Fv F v) σ J x w) = hR (Fv F v) σ J w x :=
    PI.VolStabS.hR_herm (Fv F v) σ hinv J hJ.1
  have hss : ∀ x, s (s x) = x := PI.VolStabS.sigR_invol (Fv F v) σ hinv

  let Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun i => Matrix.vecMul (fun l => s (y i l)) (JR (F := F) (Fv F v) J)
  have hZh : ∀ i w, hR (Fv F v) σ J (y i) w = ∑ k, Z i k * w k := by
    intro i w
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hZ : LinearIndependent (Fv F v ⊗[F] E) Z := by
    have hJu : IsUnit (JR (F := F) (Fv F v) J).det := by
      have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
      rw [RingHom.mapMatrix_apply] at e
      show IsUnit (J.map (inclR (Fv F v))).det
      rw [← e]
      exact (isUnit_iff_ne_zero.2 hJ.2).map _
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let w : Fin n → Fv F v ⊗[F] E := fun l => ∑ i, g i * s (y i l)
    have hv0 : Matrix.vecMul w (JR (F := F) (Fv F v) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : w = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Fv F v) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • y i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, map_sum, map_mul, hss, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hy _ hX0 i
    have e2 := congrArg s this
    simp only [hss, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := PI.VolStabS.exists_leftInv_of_linIndep Z hZ

  let f' : Fin r → Fin n → Fv F v ⊗[F] E := fun b k => q k b.castSucc
  have hyf' : ∀ i b, hR (Fv F v) σ J (y i) (f' b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    rw [hZh]
    exact hq i b.castSucc
  have hyy : ∀ i j, hR (Fv F v) σ J (y i) (y j) =
      inclR (Fv F v) (if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) := by
    intro i j
    have := congrFun (congrFun hgram i) j
    simp only [Matrix.map_apply, hG0] at this
    exact this
  have hyy0 : ∀ i (a : Fin r), hR (Fv F v) σ J (y i) (y a.castSucc) = 0 := by
    intro i a
    rw [hyy]
    simp [Fin.castSucc_ne_last]
  let h2 : Fv F v ⊗[F] E := algebraMap F (Fv F v ⊗[F] E) (1 / 2)
  have hh : h2 + h2 = 1 := by
    rw [← map_add (f := _), show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : s h2 = h2 := (Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ).commutes _
  let c : Fin r → Fin r → Fv F v ⊗[F] E := fun a b => h2 * hR (Fv F v) σ J (f' a) (f' b)
  let f : Fin r → Fin n → Fv F v ⊗[F] E := fun b => f' b - ∑ a, c a b • y a.castSucc
  have hyf : ∀ i b, hR (Fv F v) σ J (y i) (f b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [f]
    rw [GlobalTheory.FrameExtend.hR_sub_sum_right, hyf']
    simp [hyy0]
  have hfy : ∀ b i, hR (Fv F v) σ J (f b) (y i) = if i = b.castSucc then 1 else 0 := by
    intro b i
    rw [← hsw, hyf]
    split_ifs <;> simp
  have hf'y : ∀ b (d : Fin r), hR (Fv F v) σ J (f' b) (y d.castSucc) = if d = b then 1 else 0 := by
    intro b d
    rw [← hsw, hyf']
    split_ifs with h1 h2 h2 <;> simp_all [Fin.castSucc_inj]
  have hff : ∀ a b, hR (Fv F v) σ J (f a) (f b) = 0 := by
    intro a b
    have e1 : hR (Fv F v) σ J (f a) (f b) = hR (Fv F v) σ J (f a) (f' b) - c a b := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      have := fun d => hfy a (Fin.castSucc d)
      simp only [f] at this
      simp [this, Fin.castSucc_inj]
    have e2 : hR (Fv F v) σ J (f' b) (f a) = hR (Fv F v) σ J (f' b) (f' a) - c b a := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      simp [hf'y]
    have e3 : hR (Fv F v) σ J (f a) (f' b) = hR (Fv F v) σ J (f' a) (f' b) - h2 * hR (Fv F v) σ J (f' a) (f' b) := by
      rw [← hsw, e2, map_sub, hsw]
      simp only [c, map_mul, hsh, hsw]
    rw [e1, e3]
    simp only [c]
    linear_combination (-(hR (Fv F v) σ J (f' a) (f' b))) * hh
  refine ⟨f, ?_⟩
  have hTL : ∀ i (b : Fin r), gramE σ J (tupH P) (Fin.castAdd r i) (Fin.natAdd (r + 1) b) =
      if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [gramE, tupH, Fin.append_left, Fin.append_right, F0]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, ← hE_swap hinv hJ.1 P.z (P.f b), hfz, map_zero]
      exact (if_neg (Fin.castSucc_ne_last b).symm).symm
    · rw [Fin.snoc_castSucc, hef]
      simp only [Fin.castSucc_inj]
  funext i j
  simp only [Matrix.map_apply]
  show hR (Fv F v) σ J (Fin.append y f i) (Fin.append y f j) = _
  refine Fin.addCases (fun i => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · rw [Fin.append_left, Fin.append_left, hyy, ← hG0]
    simp [gramE, tupH, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right, hyf, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_left, hfy, ← hGh, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_right, hff]
    simp [gramE, tupH, Fin.append_right, hff0]

end GlobalTheory.FrameExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryMapFlagSpacesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces : ∀ (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F G → (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧ (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  first | exact @GlobalTheory.adapt_map_flag | exact GlobalTheory.adapt_map_flag | (intros; apply GlobalTheory.adapt_map_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitary
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PhiEmbed

theorem baseChange_injective₂ {D : D7} (p : PlF D) : Function.Injective (baseChange₂ D p) := by
  intro x y hxy
  refine (VS D).frame.ext_elem fun i => ?_
  have := congrFun hxy i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (D.s.atP p).ιE.injective this

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩⟩


set_option maxHeartbeats 1000000 in
theorem phi_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨hext, hUW, -, -⟩ := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hRel
  choose e he using fun (g : GV D) (p : PlF D) => (hext g p).exists
  have ext_one : ∀ p, Ext p (1 : GV D) (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := fun p x => rfl
  have ext_mul : ∀ p (a b : GV D) ga gb, Ext p a ga → Ext p b gb → Ext p (a * b) (ga * gb) := by
    intro p a b ga gb ha hb x
    show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
    rw [hb, ha]
  let φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0) :=
    { toFun := fun h p => ⟨e h p, hUW h h.2 p _ (he h p)⟩
      map_one' := by
        funext p
        apply Subtype.ext
        exact (hext 1 p).unique (he _ p) (ext_one p)
      map_mul' := by
        intro a b
        funext p
        apply Subtype.ext
        exact (hext _ p).unique (he _ p) (ext_mul p _ _ _ _ (he a p) (he b p)) }
  refine ⟨φ, ?_, fun h p => he h p⟩
  intro a b hab
  obtain ⟨p⟩ := exists_place D
  have h1 : e a p = e b p := congrArg Subtype.val (congrFun hab p)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply baseChange_injective₂ p
  rw [← he a p x, ← he b p x, h1]

end GlobalTheory.PhiEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAe
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem gmap_isLattice_rat {D : D7} (g : GV D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.IsLattice.of_fg D.host.E (hΛ.fg.map _)

theorem gmap_isFullLattice_rat {D : D7} (g : GV D) (Λ : LV D)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  refine { toIsLattice := gmap_isLattice_rat g Λ hΛ.toIsLattice, span_eq_top := ?_ }
  change Submodule.span D.host.E (g.toLinearMap '' (Λ : Set (VS D).V)) = ⊤
  rw [Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem ext_fix_lattice_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ h
  obtain ⟨-, -, hlat, -⟩ := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hR
  have hfin := ((_root_.GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λ₀) Λ₀ (gmap_isFullLattice_rat _ _ hΛ₀) hΛ₀).1
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro heq
  apply hp
  apply Subgroup.subset_closure
  show LocNG.img _ _ = _
  rw [← hlat (h : GV D) p _ Λ₀ (hφ h p)]
  exact heq

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsComplHermitianOrthogonalOfTotallyPositiveStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), (∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) → IsCompl U (orth S U) := by
  first | exact @GlobalTheory.isCompl_orth_of_definite | exact GlobalTheory.isCompl_orth_of_definite | (intros; apply GlobalTheory.isCompl_orth_of_definite <;> assumption)
end

