module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CompPetOrth

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)

theorem framesOn_disjoint {Z Z' : Comp Xo c} (h : Z ≠ Z') : Disjoint (framesOn U Z) (framesOn U Z') := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hz⟩ ⟨_, hz'⟩
  have s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) (hz s₀) (hz' s₀)

def sqN (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) : AutQ V → ENNReal :=
  fun q => ‖ptN la (rdU U f) (dict q.out)‖ₑ ^ (2 : ℝ)

theorem ptN_rdU_of_not_dom (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z.2 ∉ (U.X z.1).dom) : ptN la (rdU U f) z = 0 := by
  have h0 : rdU U f z.1 z.2 = 0 := by simp [rdU, hz]
  simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]

theorem sqN_support (la : ∀ k, Wt (U.X k).Ψ r) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (sqN U V dict la f) ⊆ classesOver V dict (framesOn U Z) := by
  intro q hq
  by_contra hn
  apply hq
  have h0 : ptN la (rdU U f) (dict q.out) = 0 := by
    simp only [ptN, Data.pnorm, rdU_eq_zero U hf hn, norm_zero, zero_mul]
  simp [sqN, h0]

theorem petAt_sq (x : ℝ) (μ : Measure (AutQ V)) (G : WTZ D.host.E) (f : Rul Xo c) :
    petAt U x V dict μ G f ^ 2 = lieFacZ Dw x G ^ 2 * (∫⁻ q, sqN U V dict (modelWt U G) f q ∂μ).toReal := by
  unfold petAt petE
  rw [eLpNorm'_eq_lintegral_eNorm,
    ← ENNReal.toReal_rpow, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num [sqN]

theorem petE_rdU_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : petE V dict μ la (rdU U f) ≠ ⊤ := by
  have h : ∀ q : AutQ V, ‖ptN la (rdU U f) (dict q.out)‖ₑ ≤ supE U.X la (rdU U f) := fun q => by
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _)]
    by_cases hd : (dict q.out).2 ∈ (U.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd⟩⟩
    · rw [ptN_rdU_of_not_dom U la f hd, ENNReal.ofReal_zero]
      exact bot_le
  have hle : petE V dict μ la (rdU U f) ≤ eLpNorm' (fun _ : AutQ V => supE U.X la (rdU U f)) 2 μ :=
    eLpNorm'_mono_eNorm_ae (by norm_num) (Filter.Eventually.of_forall h)
  apply ne_top_of_le_ne_top (supE_ne_top U.X la hP)
  refine hle.trans ?_
  rw [eLpNorm'_const _ (by norm_num), eNorm_eq_self, measure_univ]
  simp

theorem lint_sqN_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : ∫⁻ q, sqN U V dict la f q ∂μ ≠ ⊤ := by
  have h := petE_rdU_ne_top U V dict μ la hP
  rw [petE, eLpNorm'_eq_lintegral_eNorm] at h
  intro ht
  apply h
  simp only [sqN] at ht
  norm_num at ht ⊢
  rw [ht]

theorem lint_sqN_sum [Fintype (Comp Xo c)] (μ : Measure (AutQ V))
    (hm : ∀ Z : Comp Xo c, NullMeasurableSet (classesOver V dict (framesOn U Z)) μ) (la : ∀ k, Wt (U.X k).Ψ r)
    (f : Comp Xo c → Rul Xo c) (hf : ∀ Z, f Z ∈ suppOn Z) :
    ∫⁻ q, sqN U V dict la (∑ Z, f Z) q ∂μ = ∑ Z, ∫⁻ q, sqN U V dict la (f Z) q ∂μ := by
  have hdisj : Pairwise (Function.onFun Disjoint fun Z => classesOver V dict (framesOn U Z)) :=
    fun Z Z' h => Set.disjoint_left.2 fun q h1 h2 => Set.disjoint_left.1 (framesOn_disjoint U h) h1 h2
  have hpt : ∀ Z, ∀ q ∈ classesOver V dict (framesOn U Z),
      sqN U V dict la (∑ Z, f Z) q = sqN U V dict la (f Z) q := by
    intro Z q hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = rdU U (f Z) (dict q.out).1 (dict q.out).2 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single Z]
      · intro Z' _ hZ'
        exact rdU_eq_zero U (hf Z') fun h => Set.disjoint_left.1 (framesOn_disjoint U hZ') h hq
      · intro h; exact absurd (Finset.mem_univ Z) h
    simp only [sqN, ptN, Data.pnorm, e]
  have hsupp : Function.support (sqN U V dict la (∑ Z, f Z)) ⊆ ⋃ Z, classesOver V dict (framesOn U Z) := by
    intro q hq
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    apply hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      exact Finset.sum_eq_zero fun Z _ => rdU_eq_zero U (hf Z) (hn Z)
    have h0 : ptN la (rdU U (∑ Z', f Z')) (dict q.out) = 0 := by
      simp only [ptN, Data.pnorm, e, norm_zero, zero_mul]
    simp only [sqN, h0]
    simp
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_iUnion₀ hm (fun Z Z' h => (hdisj h).aedisjoint),
    tsum_fintype]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [← setLIntegral_eq_of_support_subset (sqN_support U V dict la (hf Z))]
  exact lintegral_congr_ae ((ae_restrict_mem₀ (hm Z)).mono fun q hq => hpt Z q hq)

theorem petAt_muOn_sq (x : ℝ) (G : WTZ D.host.E) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    (muQ1 V (classesOver V dict (framesOn U Z))).toReal * petAt U x V dict (muOn U V dict Z) G f ^ 2 =
      petAt U x V dict (muQ1 V) G f ^ 2 := by
  rw [petAt_sq, petAt_sq]
  unfold muOn muPart ProbabilityTheory.cond
  have key := setLIntegral_eq_of_support_subset (μ := muQ1 V) (sqN_support U V dict (modelWt U G) hf)
  rw [lintegral_smul_measure, key]
  by_cases h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0
  · have hI : ∫⁻ q, sqN U V dict (modelWt U G) f q ∂muQ1 V = 0 := by
      rw [← key, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    simp [h0, hI]
  · have ha : (muQ1 V (classesOver V dict (framesOn U Z))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp

theorem petAt_idem_le (x : ℝ) (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (G : WTZ D.host.E) (Z : Comp Xo c)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X (modelWt U G)) :
    petAt U x V dict μ G (GlobalTheory.FlatLine.idem Z * f) ≤ petAt U x V dict μ G f := by
  unfold petAt
  refine mul_le_mul_of_nonneg_left ?_ (lieFacZ_pos _ _).le
  refine ENNReal.toReal_mono (petE_rdU_ne_top U V dict μ _ hP) ?_
  unfold petE
  refine eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
  simp only [ptN, Data.pnorm]
  refine mul_le_mul_of_nonneg_right ?_ (pnorm_fac_nonneg _ _ _)
  rw [GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  have he : IsIdempotentElem (rdU U (GlobalTheory.FlatLine.idem Z) (dict q.out).1 (dict q.out).2) := by
    have := congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)) (dict q.out).1)
      (dict q.out).2
    rw [GlobalTheory.FlatLine.idem_mul_idem] at this
    exact this.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h <;> rw [h] <;> simp

end One

theorem orthogonal_mass_idem : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  intro D H Dw l Xo c r U V dict hc G
  haveI := CompFin.finite_comp Xo c
  letI : Fintype (Comp Xo c) := Fintype.ofFinite _
  have hm : ∀ (σ : c.F →+* ℂ) (Z : Comp Xo c), NullMeasurableSet
      (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z)) (muQ1 (V (goodOf c σ))) :=
    fun σ Z => GlobalTheory.ClassesMeas.nullMeasurableSet_classesOver_framesOn D H Dw l Xo c r U V dict hc _
      (goodEmb_goodOf c σ) Z
  refine ⟨fun σ => ⟨fun f => ?_, fun Z f => ?_⟩, fun Z σ => ⟨ENNReal.toReal_nonneg, ?_⟩, fun Z σ f => ?_⟩
  · rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [normRes, petW]
    rw [petAt_sq, lint_sqN_sum _ _ _ _ (hm σ) _ _ fun Z => (Submodule.mem_inf.1 (f Z).2).2,
      ENNReal.toReal_sum fun Z _ => lint_sqN_ne_top _ _ _ _ _
        ((mem_cuspW.1 (Submodule.mem_inf.1 (f Z).2).1).2 _ (goodEmb_goodOf c σ)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun Z _ => (petAt_sq _ _ _ _ _ _ _).symm
  · simp only [normRes, normOn, petW, petOn, mass]
    exact (petAt_muOn_sq _ _ _ _ _ (Submodule.mem_inf.1 f.2).2).symm
  · simp only [mass]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · simp only [petW]
    exact petAt_idem_le _ _ _ _ _ _ _ ((mem_cuspW.1 f.2).2 _ (goodEmb_goodOf c σ))

end GlobalTheory.CompPetOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.MBLow.coords_integral_of_closed_indep :
  ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first
  | exact @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | (apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients ..)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CoreSlope

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem coreAt_of (C : ℝ) (hg : GramAt p i) (hm : MeasAt p i C) (hr : RatAt p i) : CoreAt p i (2 * C) := by
  obtain ⟨ι, hι, hli, himg⟩ := _root_.GlobalTheory.CovTop.SupImage.exists_emb_image_latW _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hTC : IsTotallyComplex p.T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hc : ∀ σ x, nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := fun σ x => by
    simp only [nrmK]
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hfg : (latTypeK p.fw p.F.lv2 i).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hg.2.2.2.2.1
    exact Submodule.FG.of_le_of_isNoetherian (T := latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n)) inf_le_left
  have hN : ∀ σ' x, nrmR p.R.toRealDat i σ' (ι x) ≤ Real.exp (C * unitE p) * nrmK p.fw i (σ'.comp (algebraMap p.T.Q.c.F D.what₂.LL)) x := by
    intro σ' x
    obtain ⟨c, hc0, hcl, hcf⟩ := hm σ'
    obtain ⟨h, hx⟩ := hι x
    rw [hx, hcf ⟨x, h⟩]
    have hce : c ≤ Real.exp (C * unitE p) := by
      calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
        _ ≤ Real.exp (C * unitE p) := Real.exp_le_exp.2 ((le_abs_self _).trans hcl)
    exact mul_le_mul_of_nonneg_right hce (petAt_nonneg _ _ _ _ _ _ _)
  have hS : latType p.R.toRealDat p.F.lv2 i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latTypeK p.fw p.F.lv2 i : Set (VK p.fw i))) := by
    rw [hr]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ (ι '' (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i))) := by
        rw [himg]; exact hy1
      obtain ⟨x, hx, rfl⟩ := hy1'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      show (x : p.T.R _) ∈ Submodule.span _ (typeK p.fw p.F.lv2 i)
      obtain ⟨h, hx'⟩ := hι x
      exact Submodule.subset_span ⟨h, hx' ▸ hy2⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(show ι x ∈ ((p.R.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) by rw [← himg]; exact ⟨x, hx1, rfl⟩), ?_⟩
      have hsp : Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i) ≤
          ((spType p.R.toRealDat p.F.lv2 i).comap ι).map (VK p.fw i).subtype := by
        rw [Submodule.span_le]
        rintro f ⟨h, hf⟩
        have hfV : f ∈ VK p.fw i := by rw [VK, cuspW_wtZ]; exact h
        refine ⟨⟨f, hfV⟩, ?_, rfl⟩
        obtain ⟨h', e⟩ := hι ⟨f, hfV⟩
        show ι ⟨f, hfV⟩ ∈ spType p.R.toRealDat p.F.lv2 i
        rw [e]
        exact hf
      obtain ⟨z, hz, hzx⟩ := hsp hx2
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
  have h0 : latTypeK p.fw p.F.lv2 i ≠ ⊥ := by
    intro h0
    apply hg.2.2.1
    rw [eq_bot_iff]
    refine (latGood_le _ _ _).trans ?_
    rw [hS, h0]
    simp
  have key := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    (nrmK p.fw i) (nrmR p.R.toRealDat i) ι (latTypeK p.fw p.F.lv2 i) (C * unitE p) hg.2.2.2.1 hg.1 hc hli hfg h0 hN
  unfold CoreAt muCore
  rw [hS]
  linarith

theorem coreLe_of_gram_meas_rat : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  intro hg hm hr
  unfold Gram Meas GlobalTheory.CovTop.Rat CoreLe Lifts at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩

end GlobalTheory.CoreSlope
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.JetGeo

open ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

section Val
variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem valR_app (x : Sp A ⟶ Y) (q : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valR x (q ⁻¹ᵁ W) ((q.app W).hom f) = valR (x ≫ q) W f := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)
  · rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx
  · have hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W := hx
    unfold valR
    rw [dite_eq_right hx, dite_eq_right hx']

theorem valR_res' (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U) (e' : U ≤ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ V
  · exact GlobalTheory.ZH.CrdCalc.valR_res x e h f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun hU => h (hU.trans (x.preimage_mono e'))
    unfold valR
    rw [dite_eq_right h, dite_eq_right h']

theorem valR_pullGen (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (x : Sp A ⟶ Z) (j : K → L.ι) :
    valR x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val =
      valR (x ≫ h) (LB.wchart L φ j) (c.s j).val := by
  have e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  change valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _
  rw [valR_res' x e e']
  exact valR_app x h _ _

end Val

theorem ex_zero {B : NumB ℂ} {g : ℕ} (d : AB B g) : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ex_sum {B : NumB ℂ} {g : ℕ} (d : AB B g) {J : Type} (s : Finset J) (v : J → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem thφ_pt (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod]
  have h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i =
      ν.eA (d.ex (![x, y, z] i)) := by
    intro i; fin_cases i <;> simp [x3]
  simp_rw [h3, ← map_prod, ← ex_sum]

end Pts

theorem jet_geo : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  intro R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy
  classical

  have hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R := R) ℂ).hom := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext; simp
    simp only [TE, Over.mk_hom, redE, spMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ
  let P3 : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ G3 D.P.A) := fun z =>
    lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))
  let q : DegPre.BF D ℂ ⟶ G3 D.P.A :=
    lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))
  let h := (lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))
  have hb : ρ ≫ gm.b = ν.eA (d.ex 0) := by
    rw [ex_zero, map_one]
    ext1
    show redE ℂ ≫ gm.b.left = _
    rw [← hp.1, ho.1]
    rfl
  have hred : ρ ≫ h = P3 0 := by
    simp only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b ≫ q = h := by
    simp only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]
  have hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left := by
    intro z
    rw [ptB, ← Over.comp_left]
    congr 1
    simp only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left :=
    fun z I => thφ_pt ν d x y z I
  let j0 : thK.{0} → D.P.L.ι := fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left
  let W0 := LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0
  refine ⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩
  ·
    have hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0 := by
      funext I
      rw [Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred,
        e3]
    refine Eq.trans ?_ (valR_app _ q.left W0 _).symm
    rw [← Over.comp_left, hq]
    unfold vE DegPre.cubAtT
    refine (valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_
    rw [Category.id_comp]
    have key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val := by
      rintro _ _ rfl; rfl
    exact key _ _ hj
  · intro p _
    change (ptB ν d 0 ≫ q.left).base p ∈ W0
    rw [hpt]
    refine Set.mem_iInter.2 fun I => ?_
    have := ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)
    rw [e3] at this
    change ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)
    rw [e3]
    exact this
  · intro z hz
    refine ⟨fun I p _ => ?_, ?_⟩
    · have hm : (ptB ν d z ≫ q.left).base p ∈ W0 := hz (Set.mem_univ p)
      rw [hpt] at hm
      have := LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm
      rw [← e3 z I]
      exact this
    · change valR (ptB ν d z) _ _ = valR _ _ _
      refine (valR_app (ptB ν d z) q.left W0 _).trans ?_
      rw [hpt]

end GlobalTheory.MBLow.JetGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
end

