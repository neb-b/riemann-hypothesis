module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.EventuallyUnit
section
noncomputable section

open MeasureTheory Matrix Filter Topology Polynomial

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem eventually_unit (y : M2 n) (hy : InG y) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (y * nbar t).toBlocks₂₁.det := by
  set C := y.toBlocks₂₁ with hC
  set D := y.toBlocks₂₂ with hD
  let M : Matrix (Fin n) (Fin n) ℂ[X] := C.map Polynomial.C + (Polynomial.X : ℂ[X]) • D.map Polynomial.C
  have hev : ∀ z : ℂ, (M.det).eval z = (C + z • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    have h1 := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero] at h1
    have hu : u1 y = Complex.I • C + D := rfl
    have hmat : C + (-Complex.I) • D = (-Complex.I) • u1 y := by
      rw [hu, smul_add, smul_smul]
      simp
    rw [hmat, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (det_first_cayley_block_ne_group y hy)) h1.symm
  have hfin : {t : ℝ | (M.det).eval (t : ℂ) = 0}.Finite := by
    refine ((M.det.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact ht
  have hS : IsClosed ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnhds : ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    hS.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ht ht0
  rw [nbar_block, ← hev]
  exact isUnit_iff_ne_zero.2 (fun h => ht ⟨h, ht0⟩)

private theorem inG_mul' {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

private theorem inG_nU_herm' (s : Fin n → Fin n → ℝ) : InG (nU (herm s)) := by
  have hh : (herm s)ᴴ = herm s := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add (f := _), map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hh]

theorem vanish_all (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  let G : ℝ → (Fin n → Fin n → ℝ) → ℂ := fun t s => fz m e 0 (y * nbar t * nU (herm s) * b) * ψ s
  let X : ℝ × (Fin n → Fin n → ℝ) → M2 n := fun p => y * nbar p.1 * nU (herm p.2) * b
  have hIn : ∀ p, InG (X p) := fun p =>
    inG_mul' (inG_mul' (inG_mul' hy (inG_nbar p.1)) (inG_nU_herm' p.2)) hb
  have h1 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nbar (n := n) p.1 := by
    unfold nbar
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const) continuous_const
  have h2 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nU (herm p.2) := by
    unfold nU
    refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
    unfold herm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fun_prop
  have hX : Continuous X :=
    ((continuous_const.matrix_mul h1).matrix_mul h2).matrix_mul continuous_const
  have hU : Continuous fun p => u1 (X p) := by
    unfold u1
    refine (Continuous.const_smul ?_ Complex.I).add ?_ <;>
      exact continuous_pi fun i => continuous_pi fun j => hX.matrix_elem _ _
  have hcont : Continuous (Function.uncurry G) := by
    have hG : Function.uncurry G = fun p => (X p).det ^ e * (u1 (X p)).det ^ (-(m : ℤ)) * ψ p.2 := by
      funext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, X, fz_zero]
    rw [hG]
    exact ((hX.matrix_det.zpow₀ e fun p => Or.inl (det_ne_of_inG _ (hIn p))).mul
      (hU.matrix_det.zpow₀ _ fun p => Or.inl (det_first_cayley_block_ne_group _ (hIn p)))).mul (hψ.1.comp continuous_snd)
  have hK : IsCompact (tsupport ψ) := hψ.2.1
  have hInt : ∀ t, ∫ s, G t s = ∫ s in tsupport ψ, G t s := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun s hs => by simp [G, image_eq_zero_of_notMem_tsupport hs])).symm
  have hc : Continuous fun t => ∫ s in tsupport ψ, G t s :=
    continuous_parametric_integral_of_continuous hcont hK
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ s in tsupport ψ, G t s = 0 := by
    filter_upwards [eventually_unit y hy] with t ht
    rw [← hInt]
    exact vanish_inv hmn e (y * nbar t) b (inG_mul' hy (inG_nbar t)) hb ht ψ hψ
  have hlim : Tendsto (fun t => ∫ s in tsupport ψ, G t s) (𝓝[≠] 0) (𝓝 (∫ s in tsupport ψ, G 0 s)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : ∫ s in tsupport ψ, G 0 s = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  have hn0 : nbar (n := n) 0 = 1 := by simp [nbar]
  have := (hInt 0).trans h0
  simpa [G, hn0] using this

end PositivityTheory.Rg.Sw.HSt.L3
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KerInt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
  {β : M2 n → ℝ} (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)

def Psi (β : M2 n → ℝ) (h : GR n → ℂ) (x : M2 n) : ℂ := ∫ u, h u • kk m e μK β (x, mR u) ∂ν

def Lk (β : M2 n → ℝ) (Z x₀ : M2 n) (u : GR n) : ℂ :=
  fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z1 Z) +
    Complex.I * fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z2 Z)

include hβ hβs in
theorem good (h : GR n → ℂ) (hh : Continuous h) :
    PCD.Good (Inv n) (fun x u => h u • kk m e μK β (x, mR u)) :=
  PCD.good_of_joint isOpen_Inv _ (kk_contDiffOn m e μK hβ) (fun u : GR n => mR u) PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR h hh
    (kk_supp m e μK hβs)

include hβ hβs in
theorem psi_contDiffOn (h : GR n → ℂ) (hh : Continuous h) : ContDiffOn ℝ ∞ (Psi m e ν μK β h) (Inv n) :=
  PCD.contDiffOn_integral isOpen_Inv ν (good m e μK hβ hβs h hh)

include hβ in
theorem kk_diff {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (u : GR n) :
    DifferentiableAt ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := by
  have hsl : ContDiffOn ℝ ∞ (fun x' => kk m e μK β (x', mR u)) (Inv n) :=
    (kk_contDiffOn m e μK hβ).comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  exact (hsl.differentiableOn (by simp) x₀ hx₀).differentiableAt (isOpen_Inv.mem_nhds hx₀)

include hβ hβs in
theorem rC_psi (h : GR n → ℂ) (hh : Continuous h) (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    rC Z (Psi m e ν μK β h) x₀ = ∫ u, h u * Lk m e μK β Z x₀ u ∂ν := by
  have hG := good m e μK hβ hβs h hh
  have hF := hG.hasFDerivAt isOpen_Inv ν hx₀
  have hI := (hG.dK isOpen_Inv).integrable ν hx₀
  have hfd : ∀ u, fderiv ℝ (fun x => h u • kk m e μK β (x, mR u)) x₀ =
      h u • fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := fun u =>
    fderiv_const_smul (kk_diff m e μK hβ hx₀ u) (h u)
  rw [show Psi m e ν μK β h = fun x => ∫ u, h u • kk m e μK β (x, mR u) ∂ν from rfl]
  rw [rC_of_diff hF.differentiableAt]
  erw [hF.fderiv, ContinuousLinearMap.integral_apply hI, ContinuousLinearMap.integral_apply hI]
  have i1 := hI.apply_continuousLinearMap (x₀ * Z1 Z)
  have i2 := hI.apply_continuousLinearMap (x₀ * Z2 Z)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  erw [hfd u]
  change h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z1 Z) +
    Complex.I * (h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z2 Z)) = _
  simp only [Lk, smul_eq_mul]
  ring

include hβ in
theorem slice_fderiv {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (v : M2 n) :
    fderiv ℝ (fun x' => kk m e μK β (x', v)) x₀ = (fderiv ℝ (kk m e μK β) (x₀, v)).comp (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hd : DifferentiableAt ℝ (kk m e μK β) (x₀, v) :=
    ((kk_contDiffOn m e μK hβ).differentiableOn (by simp) _ ⟨hx₀, mem_univ _⟩).differentiableAt
      (hS.mem_nhds ⟨hx₀, mem_univ _⟩)
  have hi : HasFDerivAt (fun x' : M2 n => (x', v)) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) x₀ :=
    (hasFDerivAt_id x₀).prodMk (hasFDerivAt_const v x₀)
  exact (hd.hasFDerivAt.comp x₀ hi).fderiv

include hβ in
theorem Lk_cont (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) : Continuous (Lk m e μK β Z x₀) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hc : ContinuousOn (fun p => fderiv ℝ (kk m e μK β) p) (Inv n ×ˢ univ) :=
    (kk_contDiffOn m e μK hβ).continuousOn_fderiv_of_isOpen hS (by simp)
  have hc' : Continuous fun u : GR n => fderiv ℝ (kk m e μK β) (x₀, mR u) :=
    hc.comp_continuous (continuous_const.prodMk PositivityTheory.Rg.Sw.HSt.GRH.continuous_mR) fun u => ⟨hx₀, mem_univ _⟩
  have e1 : Lk m e μK β Z x₀ = fun u => fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z1 Z)) +
      Complex.I * fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z2 Z)) := by
    funext u
    simp only [Lk, slice_fderiv m e μK hβ hx₀, ContinuousLinearMap.comp_apply]
  rw [e1]
  exact (hc'.clm_apply continuous_const).add (continuous_const.mul (hc'.clm_apply continuous_const))

omit [μK.IsHaarMeasure] in
include hβs in
theorem Lk_zero (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    ∃ C : Set (GR n), IsCompact C ∧ ∀ u ∉ C, Lk m e μK β Z x₀ u = 0 := by
  obtain ⟨W, hW, C, hC, hz⟩ := kk_supp m e μK hβs x₀ hx₀
  refine ⟨C, hC, fun u hu => ?_⟩
  have h0 : (fun x' => kk m e μK β (x', mR u)) =ᶠ[𝓝 x₀] fun _ => 0 := by
    filter_upwards [hW] with x' hx' using hz x' hx' u hu
  simp [Lk, h0.fderiv_eq]

end

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

