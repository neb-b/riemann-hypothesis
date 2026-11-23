module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0009

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffMatrixMul
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mul_M2 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.1 * p.2) := by
  refine contDiff_of_entries fun a b => ?_
  have : (fun p : M2 n × M2 n => (p.1 * p.2) a b) = fun p => ∑ c, p.1 a c * p.2 c b := by
    funext p; rfl
  rw [this]
  exact ContDiff.sum fun c _ => ((contDiff_entry a c).comp contDiff_fst).mul ((contDiff_entry c b).comp contDiff_snd)

theorem tw_contDiff (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (tw m e μK β) := by
  have hk : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) (univ ×ˢ univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.2 * p.1) := contDiff_mul_M2.comp (contDiff_snd.prodMk contDiff_fst)
    exact (Complex.ofRealCLM.contDiff.comp (hβ.comp h1)).contDiffOn
  have hv : Continuous (fun k : KR n => (mR (k : GR n))ᴴ) := continuous_kR.matrix_conjTranspose
  have hh : Continuous (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀ fun k => Vac.spherical_section_ne_zero detU1 m 0 e _
  have := PCD.contDiffOn_integral' (F := M2 n) (X := KR n) isOpen_univ μK
    (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) hk (fun k : KR n => (mR (k : GR n))ᴴ) hv
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) hh
    (fun x _ => ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ u hu => absurd (mem_univ u) hu⟩)
  rw [contDiffOn_univ] at this
  have e' : tw m e μK β = fun X => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ • ((β ((mR (k : GR n))ᴴ * X) : ℝ) : ℂ) ∂μK := by
    funext X; rfl
  rw [e']
  exact this

def kk (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (p : M2 n × M2 n) : ℂ := tw m e μK β (p.1⁻¹ * p.2)

theorem kk_contDiffOn (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiffOn ℝ ∞ (kk m e μK β) (Inv n ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => (p.1⁻¹, p.2)) (Inv n ×ˢ univ) :=
    (contDiffOn_inv.comp contDiffOn_fst fun (p : M2 n × M2 n) (hp : p ∈ Inv n ×ˢ univ) => hp.1).prodMk contDiffOn_snd
  exact (tw_contDiff m e μK hβ).comp_contDiffOn (contDiff_mul_M2.comp_contDiffOn h1)

theorem kk_supp (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβs : HasCompactSupport β) :
    ∀ x ∈ Inv n, ∃ W ∈ 𝓝 x, ∃ C : Set (GR n), IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, kk m e μK β (x', mR u) = 0 := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp isOpen_Inv x hx
  have hFD : FiniteDimensional ℝ (M2 n) := inferInstanceAs (FiniteDimensional ℝ (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  have hPS : ProperSpace (M2 n) := FiniteDimensional.proper ℝ (M2 n)
  set B := Metric.closedBall x (r / 2)
  have hB : IsCompact B := isCompact_closedBall x (r / 2)
  have hBI : B ⊆ Inv n := fun y hy => hrs (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (half_lt_self hr))
  set T := (fun p : M2 n × M2 n => p.1 * p.2) '' (B ×ˢ kSet (tsupport β))
  have hT : IsCompact T := (hB.prod (isCompact_kSet hβs)).image contDiff_mul_M2.continuous
  refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (half_pos hr), (mR : GR n → M2 n) ⁻¹' T,
    isCompact_preimage_mR hT, fun x' hx' u hu => ?_⟩
  unfold kk
  refine tw_eq_zero m e μK β fun hmem => hu ?_
  refine ⟨(x', x'⁻¹ * mR u), ⟨hx', hmem⟩, ?_⟩
  show x' * (x'⁻¹ * mR u) = mR u
  have hdet : IsUnit x'.det := isUnit_iff_ne_zero.mpr (hBI hx')
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousMatrixLowerRightBlock
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CrxMa

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem continuous_matrix_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_matrix_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_cayley_first_block : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).add continuous_matrix_lower_right_block

theorem continuous_cayley_second_block : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).neg.add continuous_matrix_lower_right_block

theorem isOpen_OmZ (hFz : FzHol) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  isOpen_setK (hFz n 0 0).1 Kg ι hι

theorem gset_sub_OmZ (hFz : FzHol) {Kg : Type} (ι : Kg → M2 n) (hιG : ∀ k, InG (ι k)) :
    GSet n ⊆ {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  fun _g hg k => (hFz n 0 0).2.1 (inG_mul (hιG k) hg)

theorem continuousOn_vacuum_at_zero (hFz : FzHol) (m : ℕ) : ContinuousOn (fun x : M2 n => fz m 0 0 x) (DomZ n) := by
  intro x hx
  have hA := (hFz n m 0).2.2 ((0 : ℂ), x) ⟨Set.mem_univ _, hx⟩
  have hmk : Continuous fun y : M2 n => ((0 : ℂ), y) := by fun_prop
  exact (hA.continuousAt.comp hmk.continuousAt).continuousWithinAt

theorem continuous_rhoP (hFz : FzHol) (m : ℕ) {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m 0 Y) := by
  unfold rhoP
  have hfz : Continuous fun k => fz m 0 0 (ι k) :=
    (continuousOn_vacuum_at_zero hFz m).comp_continuous hι (fun k => (hFz n m 0).2.1 (hιG k))
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    have e : (fun k => (u2 (ι k))⁻¹) = fun k => (u2 (ι k)).det⁻¹ • (u2 (ι k)).adjugate := by
      funext k; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    have hd := (continuous_cayley_second_block.comp hι).matrix_det
    exact (hd.inv₀ (fun k => det_second_cayley_block_ne_zero (hιG k))).smul ((continuous_cayley_second_block.comp hι).matrix_adjugate)
  exact (hfz.mul (((hinv.matrix_mul continuous_const).matrix_mul (continuous_cayley_first_block.comp hι)).matrix_trace)).star

theorem contDiffOn_PhiZ (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, Fd m (ι k * x) * c k ∂μ) {x : M2 n | ∀ k, ι k * x ∈ DomZ n} := by
  have hF : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := (hFd n m).1.of_le le_top
  exact (PositivityTheory.Rg.Sw.LVs.holInt n Kg μ _ (fun k x => Fd m (ι k * x) * c k) (isOpen_OmZ hFz Kg ι hι)
    (fun N => continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n 0 0).1 hF Kg ι hι c hc N)
    (fun k => (hF.comp (contDiff_mulLeft (ι k)).contDiffOn
      (fun x (hx : x ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}) => hx k)).mul contDiffOn_const)).1

theorem fubini_gen (F : M2 n → ℂ) (U : Set (M2 n)) (hF : ContinuousOn F U) (hGU : GSet n ⊆ U)
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ) (a b : M2 n) (ha : InG a) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t =
      ∫ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) ∂μ := by
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set Fp : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => F (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 * ρ z.1 with hFpdef
  have hFc : Continuous Fp :=
    ((hF.comp_continuous hmap (fun z => hGU (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hρ.comp continuous_fst)
  have hFs : HasCompactSupport Fp := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport Fp) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFpdef, h0]
  have hFi : Integrable Fp (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) = ∫ t, Fp (k, t) := by
    intro k; rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hFpdef, Matrix.one_mul]; ring
  have e2 : ∀ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t = ∫ k, Fp (k, t) ∂μ := by
    intro t; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFpdef, Matrix.mul_assoc]; ring
  simp_rw [e1, e2]
  exact (integral_integral_swap (f := fun k x => Fp (k, x)) hFi).symm

theorem stepA_Z (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg]
    [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg)
    [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (hneg : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), IsSingTest ψ → InG a →
      InG b → InG x → deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) (a b : M2 n) (ha : InG a) (hb : InG b) :
    detD (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) = 0 := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hΩo := isOpen_OmZ hFz Kg ι hι
  have hGΩ := gset_sub_OmZ hFz ι hιG
  have hρ := continuous_rhoP hFz m ι hι hιG Y
  have hΦ := contDiffOn_PhiZ hFd hFz m Kg μ ι hι _ hρ
  have hpre : IsOpen {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} :=
    hΩo.preimage (contDiff_nU_sandwich a b).continuous
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈
      {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} := by
    show a * nU 0 * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}
    have : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, Matrix.fromBlocks_one]
    rw [this, mul_one]; exact hGΩ (inG_mul ha hb)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  refine singToDiff n (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) r hr
    (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
  intro ψ hψ
  have h1 := hneg Y ψ a b 1 hψ ha hb inG_one
  rw [(hFd n m).2 Kg μ ι hι hK (rhoP ι m 0 Y) ψ a b 1 hρ hψ.1 hψ.2.1 ha hb inG_one] at h1
  rw [← h1]
  have hFc : ContinuousOn (Fd (n := n) m) (DomZ n) := (hFd n m).1.continuousOn
  exact fubini_gen (Fd m) (DomZ n) hFc (hFz n 0 0).2.1 Kg μ ι hι hιG _ hρ a b ha hb ψ hψ

end PositivityTheory.Rg.Sw.HSt.CrxMa
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivEqFderivPair
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem deriv_eq_fderiv_pair (U : ℂ × V → ℂ) (z0 : ℂ) (w : V) (hU : DifferentiableAt ℂ U (z0, w)) :
    deriv (fun z => U (z, w)) z0 = fderiv ℂ U (z0, w) (1, 0) := by
  have hl : HasDerivAt (fun z : ℂ => (z, w)) ((1 : ℂ), (0 : V)) z0 := (hasDerivAt_id z0).prodMk (hasDerivAt_const z0 w)
  exact (hU.hasFDerivAt.comp_hasDerivAt z0 hl).deriv

theorem iFD_slice (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (z : ℂ) (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v = iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hU' : ContDiffOn ℂ ∞ (fun p : ℂ × V => U ((z, 0) + p)) (Set.univ ×ˢ D) :=
    hU.comp (contDiff_const.add contDiff_id).contDiffOn (fun p hp => ⟨trivial, by simpa using hp.2⟩)
  have hpre : (ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D) = D := by
    ext w
    simp
  have hfun : (fun w => U (z, w)) = (fun p : ℂ × V => U ((z, 0) + p)) ∘ (ContinuousLinearMap.inr ℂ ℂ V) := by
    funext w
    simp
  have hgw : ContinuousLinearMap.inr ℂ ℂ V w0 ∈ (Set.univ ×ˢ D : Set (ℂ × V)) := ⟨trivial, hw0⟩
  have hD' : IsOpen ((ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D)) := by rw [hpre]; exact hD
  rw [hfun, ← iteratedFDerivWithin_of_isOpen k hD' (by rw [hpre]; exact hw0),
    (ContinuousLinearMap.inr ℂ ℂ V).iteratedFDerivWithin_comp_right hU' hs.uniqueDiffOn hD'.uniqueDiffOn hgw
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen k hs hgw, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]
  simp

private theorem natCast_le_infty_withTop (a : ℕ) : ((a : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem inv_mul_mul_mul_eq_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (S : Set E)
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) (e : E) (k : ℕ) :
    ∀ y ∈ S, iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) y = fderiv ℂ (iteratedFDeriv ℂ k f) y e := by
  induction k with
  | zero =>
    intro y hy
    have hd : DifferentiableAt ℂ f y :=
      (hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp
  | succ k ih =>
    intro y hy
    have hev : iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) =ᶠ[nhds y]
        fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e :=
      Filter.eventually_of_mem (hS.mem_nhds hy) ih
    have hg : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
      (hf.contDiffAt (hS.mem_nhds hy)).iteratedFDeriv_right (by
        have h : ((2 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
        exact_mod_cast h)
    have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
      hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    have hdg : DifferentiableAt ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have happ : fderiv ℂ (fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e) y =
        (ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).comp (fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y) :=
      ((ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).hasFDerivAt.comp y
        hdg.hasFDerivAt).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, happ,
      iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp [hsym (m 0) e]

theorem iFD_deriv_comm (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => deriv (fun z => U (z, w)) 0) w0 v =
      deriv (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) 0 := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hdiffU : ∀ p ∈ (Set.univ ×ˢ D : Set (ℂ × V)), DifferentiableAt ℂ U p := fun p hp =>
    (hU.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have hU1 : ContDiffOn ℂ ∞ (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) (Set.univ ×ˢ D) :=
    (hU.fderiv_of_isOpen hs (m := ∞) (by exact le_of_eq (by rfl))).clm_apply contDiffOn_const
  have hL : (fun w => deriv (fun z => U (z, w)) 0) =ᶠ[nhds w0] fun w => fderiv ℂ U (0, w) ((1 : ℂ), (0 : V)) :=
    Filter.eventually_of_mem (hD.mem_nhds hw0) fun w hw => deriv_eq_fderiv_pair U 0 w (hdiffU (0, w) ⟨trivial, hw⟩)
  rw [((Filter.EventuallyEq.iteratedFDeriv ℂ hL k).eq_of_nhds),
    iFD_slice (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) D hD hU1 0 w0 hw0 k v]
  have hR : (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) =
      fun z => iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) :=
    funext fun z => iFD_slice U D hD hU z w0 hw0 k v
  have hdI : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, w0) :=
    ((hU.contDiffAt (hs.mem_nhds ⟨trivial, hw0⟩)).iteratedFDeriv_right (m := 1) (by
      have h : ((1 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
      exact_mod_cast h)).differentiableAt one_ne_zero
  have hdΦ : DifferentiableAt ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp _ hdI
  rw [hR, deriv_eq_fderiv_pair _ 0 w0 hdΦ, inv_mul_mul_mul_eq_mul U _ hs hU _ k (0, w0) ⟨trivial, hw0⟩]
  have h2 : fderiv ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).comp
        (fderiv ℂ (iteratedFDeriv ℂ k U) (0, w0)) :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).hasFDerivAt.comp
      (0, w0) hdI.hasFDerivAt).fderiv
  rw [h2]
  simp

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetFirstCayleyBlockNeGroup
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  rw [← Matrix.fromBlocks_toBlocks x] at hx'
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hx'
  simp at hx'
  obtain ⟨h1, h2, h3, h4⟩ := hx'
  have hu : u1 x = Complex.I • x.toBlocks₂₁ + x.toBlocks₂₂ := rfl
  rw [hu]
  set A := x.toBlocks₁₁
  set B := x.toBlocks₁₂
  set C := x.toBlocks₂₁
  set D := x.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h1)
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = Dᴴ * A + -1 := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h4)
  have key : (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [e1, e2, e3, e4]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  intro h0
  obtain ⟨v, hv, huv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have hs : star v ᵥ* (Complex.I • C + D)ᴴ = 0 := by
    rw [← Matrix.star_mulVec, huv, star_zero]
  have hz : star v ⬝ᵥ (((Complex.I • A + B)ᴴ * (Complex.I • C + D)
      - (Complex.I • C + D)ᴴ * (Complex.I • A + B)) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv,
      Matrix.mulVec_zero, dotProduct_zero, Matrix.dotProduct_mulVec, hs, zero_dotProduct, sub_zero]
  rw [key, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hz
  have h2I : (-2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  open ComplexOrder in
  exact hv (dotProduct_star_self_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left h2I))

end PositivityTheory.Rg.Sw.HSt.L3
end
end

