module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSmul
section
noncomputable section

open MeasureTheory Filter Topology Set GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem shapeM_mono {n : ℕ} (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : ShapeM ε d ≤ ShapeM ε d' :=
  Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩

theorem hasTrace_add' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {S T : U →L[ℂ] U} {a b : ℂ} (hS : HasTrace S a) (hT : HasTrace T b) : HasTrace (S + T) (a + b) :=
  ⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩

theorem hasTrace_smul' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {T : U →L[ℂ] U} {a : ℂ} (c : ℂ) (hT : HasTrace T a) : HasTrace (c • T) (c * a) :=
  ⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩

theorem toM_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem trace_adBas (hSh : StShape) (hBD : StBasDeriv) (hUF : UFin) (hRS : RangeShape) (hTS : TraceSum)
    (hCD : ConjDeriv) {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U))
    (hπ : IsUnitaryRep π) (hirr : IsTopIrreducible π) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n)
    (hZ : LieU ε Z) (hH : IsCutFn H) :
    HasTrace (repOp π μ fun g => adBas ε Z H P (toM g)) 0 := by
  have := GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ
  have hZG : inG ε Z := (_root_.GlobalTheory.pcLieEntry n ε Z).2 hZ
  obtain ⟨hxc, hxinv⟩ := GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG
  obtain ⟨hadS, hder⟩ := hBD n ε Z H P hZ hH
  have hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2) := Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩
  obtain ⟨-, -, hac, hacs⟩ := hSh n ε _ _ hadS
  obtain ⟨-, -, hbc, hbcs⟩ := hSh n ε _ _ hbS
  obtain ⟨L, hLf, hLmem, hLd⟩ := hUF n ε U π hπ hirr (P.totalDegree + 2)
  have := hLf
  obtain ⟨-, hTr⟩ := hRS n ε μ U π hπ _ _ hadS
  obtain ⟨-, hAr⟩ := hRS n ε μ U π hπ _ _ hbS
  set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad
  set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb
  set T := repOp π μ fad with hT
  set A := repOp π μ fb with hA
  set e := stdOrthonormalBasis ℂ L with he
  set x : ℝ → UJ ε := fun t => expG ε Z t with hx
  have hx0 : x 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have := Formalism.REAL.toM_expG ε Z 0 hZG
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this
    exact this
  have hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) =
      NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z) := fun s g => by
    rw [toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]
  have key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ := fun y v u => by
    rw [hπ.inner_apply_left, inv_inv]
  set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw
  have hwc : Continuous w := continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)

  have hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ := by
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ := fun j _ =>
      (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right
    simp only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]
    rw [integral_finsetSum _ hint]

  have hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ =
      ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ := by
    intro t
    set y := x t
    have h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ =
        ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ := by
      intro j
      rw [key y, hA, hπ.inner_repOp hbc hbcs]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      congr 1
      rw [map_mul, map_mul]
      show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ
      rw [key y]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ :=
      fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport
        hbcs.mul_right
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]
    have e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) =
        fun g => fb g * w (y * g * y⁻¹) := funext fun g => by simp only [hw, Finset.mul_sum]
    rw [e2]
    have e3 := integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y
    have e4 := integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹
    rw [← e4, ← e3]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    congr 2
    · group
    · group

  have h0 : π (x 0) = 1 := by rw [hx0, map_one]
  have hCD' := hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0
    (fun t v u => by
      rw [hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply])
    (fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)
    (fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)
  have hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹
      (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ :=
    funext hid
  rw [hfun] at hCD'

  have hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)) :=
    (isCompact_Icc.prod hacs.isCompact).image (by fun_prop)
  obtain ⟨χ, h1, -, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)
  obtain ⟨M, hM⟩ := hacs.exists_bound_of_continuous hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖ := by
    intro u hu g
    rw [norm_mul]
    by_cases h : fad ((x u)⁻¹ * g * x u) = 0
    · rw [h, norm_zero, zero_mul]
      positivity
    · have hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad) :=
        ⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩
      have h2 : (χ g : ℂ) = 1 := by simp [h1 hg]
      rw [h2, norm_one, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hχc : Continuous fun g => (χ g : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ := by
    refine (((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.mul_left ?_
    exact (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm
  have hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g :=
    fun f hf u => (hf.comp (by fun_prop)).mul hwc
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g)
    (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun u => (hcontF fb hbc u).aestronglyMeasurable)
    (by
      simp only [hx0, inv_one, one_mul, mul_one]
      exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)
    (hcontF fad hac 0).aestronglyMeasurable
    (.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint
    (.of_forall fun g u _ => by
      have e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) =
          fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g :=
        funext fun v => by simp only [hfb, hconj]
      rw [e5]
      have e6 : fad ((x u)⁻¹ * g * x u) =
          adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z)) := by
        simp only [hfad, hconj]
      rw [e6]
      exact (hder (toM g) u).mul_const (w g))
  have hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0 := hint.2.unique hCD'
  simp only [hx0, inv_one, one_mul, mul_one] at hzero
  have hTL : ∀ u, T u ∈ L := fun u => hLmem _ (hTr u).1
  have := hTS U L T hTL
  rwa [hsum, hzero] at this

theorem stTrAd_of : StShape → StBasDeriv → UFin → RangeShape → TraceSum → ConjDeriv → StTrAd := by
  intro hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ
  suffices h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2
  induction hφ using Submodule.span_induction with
  | mem φ hmem =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hmem
    exact ⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩
  | zero =>
    refine ⟨⟨0, zero_mem _⟩, ?_⟩
    have h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0 := fun v => by
      simp only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]
      exact ⟨integrable_zero _ _ _, trivial⟩
    rw [h0.repOp_eq]
    exact ⟨isTraceClass_zero, trace_zero⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨⟨d₁, hd₁⟩, ht₁⟩ := h₁
    obtain ⟨⟨d₂, hd₂⟩, ht₂⟩ := h₂
    refine ⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩
    have o₁ := (hRS n ε μ U π hπ d₁ φ₁ hd₁).1
    have o₂ := (hRS n ε μ U π hπ d₂ φ₂ hd₂).1
    have hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g))
        (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.add_apply, add_smul]
      · rw [ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]
        simp only [Pi.add_apply, add_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_add' ht₁ ht₂
  | smul c φ _ h =>
    obtain ⟨⟨d, hd⟩, ht⟩ := h
    refine ⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩
    have o := (hRS n ε μ U π hπ d φ hd).1
    have hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      · rw [ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_smul' c ht

end GlobalTheory.PsCo.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MuProps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem atEmb_emb (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = Pi.single w z := by
  unfold atEmb; simp [InfinitePlace.mk_embedding]

theorem chiInf_expU_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (z : ℂ) :
    ((chiInf μ (expU (Pi.single v z)) : ℂˣ) : ℂ) =
      Complex.exp ((e v : ℂ) / 2 * z + (-(e v : ℂ) / 2) * starRingEnd ℂ z) := by
  rw [h.2.2.2.2, Finset.prod_eq_single v]
  · change (Complex.exp ((Pi.single v z : Cinf E) v) / ((‖Complex.exp ((Pi.single v z : Cinf E) v)‖ : ℝ) : ℂ)) ^ e v = _
    rw [Pi.single_eq_same, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    have := Complex.add_conj z
    push_cast at this
    linear_combination ((e v : ℂ) / 2) * this
  · intro u _ hu
    change (Complex.exp ((Pi.single v z : Cinf E) u) / ((‖Complex.exp ((Pi.single v z : Cinf E) u)‖ : ℝ) : ℂ)) ^ e u = 1
    rw [Pi.single_eq_of_ne hu]
    simp
  · simp

theorem expo_emb {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ v.embedding = (e v : ℂ) / 2 :=
  expo_eq_of_exp μ v.embedding _ (-(e v : ℂ) / 2) fun z => by
    rw [atEmb_emb]; exact chiInf_expU_single h v z

theorem expo_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  expo_eq_of_exp μ _ _ ((e v : ℂ) / 2) fun z => by
    rw [atEmb_conj, atEmb_emb, chiInf_expU_single h v]
    congr 1
    simp only [Complex.conj_conj]
    ring

theorem dchi_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (w : ℂ) :
    dchi μ (Pi.single v w) = (w.im : ℂ) * dchi μ (Pi.single v Complex.I) := by
  have h1 := expo_emb h v
  have h2 := expo_conj h v
  simp only [expo, atEmb_conj, atEmb_emb, map_one, Complex.conj_I, Pi.single_neg, map_neg] at h1 h2
  have hd1 : dchi μ (Pi.single v 1) = 0 := by linear_combination h1 + h2
  rw [← atEmb_emb, atEmb_eq, map_add (f := _), map_smul, map_smul, atEmb_emb, atEmb_emb, hd1]
  rw [smul_zero, zero_add, Complex.real_smul]

theorem dchi_neg_star {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (z : Cinf E) :
    dchi μ (-star z) = dchi μ z := by
  conv_lhs => rw [← Finset.univ_sum_single (-star z)]
  conv_rhs => rw [← Finset.univ_sum_single z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dchi_single h v, dchi_single h v (z v), Pi.neg_apply, Pi.star_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

theorem finId_conjFin (u : (Af E)ˣ) :
    finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u) =
      Units.map (conjAd E).toMonoidHom (finId E u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = (infEq E) (starRingEnd (Cinf E) ((infEq E).symm ((1 : InfiniteAdeleRing E) - 0 + 0)))
    simp
  · change (1 : Af E) - 1 + conjFin (IsCMField.complexConj E).toRingEquiv (u : Af E) =
      conjFin (IsCMField.complexConj E).toRingEquiv ((1 : Af E) - 1 + (u : Af E))
    simp

theorem mu_mul_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (x : Neutral.B1.Ideles E) :
    μ.1 x * μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x) = 1 := by
  rw [← map_mul, ← GlobalTheory.GalOfCusp.ideleMap_ideleNorm, h.2.1]
  have := congrArg (fun c : HChar E => c.1 x) (GlobalTheory.GalOfCusp.compNorm_quadChar E)
  exact this

theorem thetaInv {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (a : ℕ) : ThetaInv a μ := by
  refine CG.thetaInv_of (fun u => ?_) (dchi_neg_star h)
  rw [map_inv, finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq, map_inv]
  have := mu_mul_conj h (finId E u)
  exact inv_eq_of_mul_eq_one_left this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → (∀ a, ThetaInv a μ) ∧ (∀ v : InfinitePlace E, expo μ v.embedding = (e v : ℂ) / 2) ∧ ∀ v : InfinitePlace E, expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  fun _ _ _ _ _ _ _ h => ⟨thetaInv h, expo_emb h, expo_conj h⟩

end GlobalTheory.BCT.MuProps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem levOp_id_mem_inf_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (F : G → ℂ) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x)
    (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M) (v : V) (hv : v ∈ M ⊓ fixed ρ K') :
    levOp ρ K K' F LinearMap.id v ∈ M ⊓ fixed ρ K' := by
  obtain ⟨hvM, hvK⟩ := Submodule.mem_inf.1 hv
  have hfix : ∀ k ∈ K', ρ k v = v := fun k hk => by simpa using hvK ⟨k, hk⟩
  set φ : G ⧸ K' → V →ₗ[ℂ] V := fun q => F q.out • (ρ q.out ∘ₗ LinearMap.id) with hφ
  unfold levOp
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hs : (Function.support φ).Finite
  · have hs' : (Function.support fun q => φ q v).Finite :=
      hs.subset (fun q hq h => hq (by simp [h]))
    have happ : (∑ᶠ q, φ q) v = ∑ᶠ q, φ q v := map_finsum (LinearMap.applyₗ v) hs
    rw [happ]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [finsum_eq_sum _ hs']
      exact Submodule.sum_mem _ fun q _ => M.smul_mem _ (hM _ _ hvM)
    · intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_finsum (ρ (k : G)) hs']
      have key : ∀ q : G ⧸ K', ρ (k : G) (φ q v) = φ ((k : G) • q) v := by
        intro q
        have hq : ((((k : G) • q).out : G) : G ⧸ K') = ((k : G) * q.out : G) := by
          rw [QuotientGroup.out_eq']
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hk2 : ((k : G) * q.out)⁻¹ * ((k : G) • q).out ∈ K' := QuotientGroup.eq.1 hq.symm
        obtain ⟨c, hc, hg'⟩ : ∃ c ∈ K', ((k : G) • q).out = (k : G) * q.out * c := ⟨_, hk2, by group⟩
        simp only [hφ, LinearMap.smul_apply, LinearMap.comp_id, map_smul]
        rw [hg', (hF _ hc _).2, (hF _ k.2 _).1, map_mul, Module.End.mul_apply, hfix _ hc, map_mul,
          Module.End.mul_apply]
      rw [finsum_congr key]
      exact finsum_comp_equiv (MulAction.toPerm (k : G)) (f := fun q => φ q v)
  · rw [finsum_of_infinite_support hs]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_mul_left_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (k * x) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (a.1 * y)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem a.2 hy), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : a.1 * y ∉ UL n w := fun h => hy (by simpa using mul_mem (inv_mem a.2) h)
    rw [dite_eq_right this, dite_eq_right hy]

theorem toSub_mul_right_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (x * k) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (y * a.1)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem hy a.2), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : y * a.1 ∉ UL n w := fun h => hy (by simpa using mul_mem h (inv_mem a.2))
    rw [dite_eq_right this, dite_eq_right hy]

theorem mem_globLev_iff (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, ∃ a ∈ K' w, (a : GLw n w) = cLoc w k.1 := by
  simp [globLev, Subgroup.mem_iInf]

theorem globFn_inv (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, ∀ k ∈ K' w, ∀ x, f w (k * x) = f w x ∧ f w (x * k) = f w x) :
    ∀ k ∈ globLev S K', ∀ x, globFn S f (k * x) = globFn S f x ∧ globFn S f (x * k) = globFn S f x := by
  intro k hk x
  rw [mem_globLev_iff] at hk
  constructor
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_left_eq (f w) (fun k hk x => (hf w k hk x).1) a ha _
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_right_eq (f w) (fun k hk x => (hf w k hk x).2) a ha _

end GlobalTheory.BCT


open GlobalTheory.BCT in
theorem GlobalTheory.BCT.hop_mem_inf_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  intro E _ _ _ n S _ K' _ f hf π hπ v hv
  exact levOp_id_mem_inf_fixed (RF E n) _ _ _ (globFn_inv S K' f fun w => (hf.1 w).2) π
    (fun g v hv => hπ.stable _ v hv) v hv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.RealWeilF

theorem map_conjTranspose_of_herm {n : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  rw [← hcm, hJ]

theorem im_ne_zero_of_skew (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) : (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm, hσ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have : τ ξ₀ = 0 := Complex.ext hre him
  exact h0 ((map_eq_zero τ).1 this)

theorem hermitianFormRealCoordinateBlock_hermitian_det {nS nT : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
    (tau : InfinitePlace F → (E →+* ℂ)) :
    (HMF JS JT ξ₀ tau)ᴴ = HMF JS JT ξ₀ tau ∧ (HMF JS JT ξ₀ tau).det ≠ 0 := by
  classical
  have hdS : ∀ w, IsUnit (JS.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JS
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hS.2))
  have hdT : ∀ w, IsUnit (JT.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JT
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hT.2))
  have hc : ∀ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w => by
    have := im_ne_zero_of_skew σ hcm h0 hσ (tau w)
    exact_mod_cast mul_ne_zero two_ne_zero this
  constructor
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, map_conjTranspose_of_herm σ hcm hT.1]
      simp
    · rw [conjTranspose_nonsing_inv, map_conjTranspose_of_herm σ hcm hS.1]
  · have : HMF JS JT ξ₀ tau * GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (tau w))⁻¹)
        (fun w => JS.map (tau w)) = 1 := by
      unfold HMF
      rw [GlobalTheory.RealWeil.blk_mul, ← GlobalTheory.RealWeil.blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc w), one_smul,
          mul_nonsing_inv _ (hdT w)]
      · rw [mul_nonsing_inv _ (hdS w)]
    exact (isUnit_det_of_right_inverse this).ne_zero

end GlobalTheory.RealWeilF

theorem GlobalTheory.RealWeilF.HMF_herm_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_centralizer_regular_twistedCentraliser : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  first | (exact @GlobalTheory.CarryCent.map_centralizer_carry) | (exact GlobalTheory.CarryCent.map_centralizer_carry) | (intros; apply GlobalTheory.CarryCent.map_centralizer_carry  <;> assumption)
end

