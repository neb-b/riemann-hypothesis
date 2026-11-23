module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfTwLie
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private def invSub (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.SInv φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, by
    change IsOpen {k | finRep E a k (0 : Sm E a) = 0}
    simpa only [map_zero, Set.ofPred_true] using
      (isOpen_univ : IsOpen (Set.univ : Set (GL (Fin a) (Af E))))⟩
  add_mem' := by
    intro φ ψ h h'
    refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g),
      fun t g => congrArg₂ (· + ·) (h.centre t g) (h'.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    have h2 : IsOpen {k | finRep E a k ψ = ψ} := h'.level
    refine open_stab (finRep E a) _ (h1.inter h2) ⟨by simp, by simp⟩ ?_
    rintro k ⟨e1, e2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) e1 e2)
  smul_mem' := by
    intro c φ h
    refine ⟨fun γ g => congrArg (c • ·) (h.left γ g), fun t g => congrArg (c • ·) (h.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    refine open_stab (finRep E a) _ h1 (by simp) ?_
    intro k e1
    exact (map_smul _ _ _).trans (congrArg (c • ·) e1)

theorem UpperTheory.V.Lit.Geo.Pf.twLie :
    UpperTheory.V.Lit.Geo.Pf.TwLie := by
  intro E _ _ _ a Ξ r χ hχ X x hx
  let N : Submodule ℂ (Sm E a) := (invSub E a).comap (mulChi a χ).toLinearMap
  have hiff : ∀ y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ), Pf.TwInv χ y ↔ y ∈ tens Ξ.d N := fun y => by
    rw [mem_tens]; rfl
  rw [hiff] at hx
  rw [hiff, hiff]
  have hA : smA Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    have h0 : cmp j x ∈ N := mem_tens.1 hx j
    have h1 : lie E a X (cmp j x) + ((r * ell E a X : ℝ) : ℂ) • cmp j x ∈ N := by
      change Pf.SInv (mulChi a χ _)
      rw [← hχ.2]
      exact (Pf.invLie E a _ h0).2 X
    exact (N.add_mem_iff_left (N.smul_mem _ h0)).1 h1
  have hB : smB Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem mul_bd (x y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖∑ k, x i k * y k j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun k _ => ?_).trans (by simp))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL x i) k).trans (norm_le_pi_norm (toL x) i)
  · exact (norm_le_pi_norm (toL y k) j).trans (norm_le_pi_norm (toL y) k)

private theorem star_bd (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (star x)‖ ≤ ‖toL x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖star (x j i)‖ ≤ _
  rw [norm_star]
  exact (norm_le_pi_norm (toL x j) i).trans (norm_le_pi_norm (toL x) j)

private theorem sand_bd {C : ℝ} (h : GL (Fin a) (Cinf E)) (hC : ‖toL h.val‖ ≤ C) (v : HV E a) :
    ‖sand h v‖ ≤ (a * a * C * C) * ‖v‖ := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans hC
  change ‖toL (h.val * Matrix.of v.1 * star h.val)‖ ≤ _
  have h1 : ‖toL (h.val * Matrix.of v.1)‖ ≤ a * (C * ‖v‖) :=
    (mul_bd _ _).trans (by
      change (a : ℝ) * (‖toL h.val‖ * ‖v‖) ≤ _
      gcongr)
  calc _ ≤ _ := mul_bd _ _
    _ ≤ a * ((a * (C * ‖v‖)) * C) := by
      gcongr
      exact (star_bd _).trans hC
    _ = _ := by ring

private theorem exists_cpt (C : ℝ) : ∃ K : Set (Lie E a), IsCompact K ∧ K ⊆ invSet E a ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → toL h.val ∈ K := by
  have hc : IsClosed {z : Lie E a × Lie E a | toL (Matrix.of z.1 * Matrix.of z.2) = toL 1} := by
    refine isClosed_eq ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun z : Lie E a × Lie E a => ∑ k, z.1 i k * z.2 k j
    fun_prop
  refine ⟨Prod.fst '' ((Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C) ∩ _),
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hc).image continuous_fst, ?_, ?_⟩
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    have e : Matrix.of z.1 * Matrix.of z.2 = 1 := hz
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)
  · intro h h1 h2
    exact ⟨(toL h.val, toL (h⁻¹).val), ⟨⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩,
      congrArg toL h.mul_inv⟩, rfl⟩

private theorem mat_bd (Ξ : AlgRep E a) (C : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖ := by
  obtain ⟨K, hK, hs, hm⟩ := exists_cpt (E := E) (a := a) C
  have hb : ∀ i j, ∃ b : ℝ, ∀ x ∈ K, ‖extGL (fun y => Ξ.mat y i j) x‖ ≤ b := fun i j =>
    hK.exists_bound_of_continuousOn ((matSmooth E a Ξ i j).1.continuousOn.mono hs)
  choose b hb using hb
  have h0 : 0 ≤ ∑ i, ∑ j, |b i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ i, ∑ j, |b i j|, h0, fun h h1 h2 y => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  change ‖∑ j, Ξ.mat h i j * y j‖ ≤ _
  calc _ ≤ ∑ j, |b i j| * ‖y‖ := by
        refine norm_sum_le_of_le _ fun j _ => (norm_mul_le _ _).trans
          (mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) (abs_nonneg _))
        have := hb i j _ (hm h h1 h2)
        rw [extGL_val] at this
        exact this.trans (le_abs_self _)
    _ = (∑ j, |b i j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |b i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

end

theorem UpperTheory.V.Lit.Geo.matBd :
    MatBd := by
  intro E _ _ _ a Ξ C
  obtain ⟨B, hB, h⟩ := mat_bd Ξ C
  refine ⟨max B (a * a * C * C), le_max_of_le_left hB, fun g h1 h2 => ⟨fun y => (h g h1 h2 y).trans ?_,
    fun v => (sand_bd g h1 v).trans ?_, fun v => (sand_bd g⁻¹ h2 v).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBasic
section
open UpperTheory.V.Lit.Geo

private theorem UpperTheory.V.Lit.Geo.euler_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (hd : DifferentiableAt ℝ W p) (hh : ∀ t : ℝ, 0 < t → W (t • p) = t • W p) (t : ℝ) :
    fderiv ℝ (flow W t) p p = flow W t p := by
  have hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1 :=
    hp1.comp_hasDerivAt (1 : ℝ) hr
  have h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1 := by
    have hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const (W p)
    rw [one_smul] at hl
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hh s hs
  have heul : fderiv ℝ W p p = W p := by
    have := h1.unique h2
    rwa [one_smul] at this
  have hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)
  rw [hf.fderiv]
  simp [flow, heul]

theorem UpperTheory.V.Lit.Geo.pbBasic :
    PbBasic := by
  intro V F _ _ _ _ _ _ Y hY W hW hh q
  have hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p := fun p hp =>
    (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p := fun p hp t =>
    euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t
  refine ⟨fun w hw => ?_, fun w _ hw => ?_⟩
  · intro p hp v i hi
    rw [pb_apply]
    apply hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i
    simp [hi, he p hp]
  · intro p hp v i hi
    have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0 := by
      intro t ht
      rw [hk_apply]
      apply hw (flow W t p) (hW.2 p hp t ht) _ i.succ
      simp [hi, he p hp]
    show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0
    by_cases hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1
    · have hc := (ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint
      simp only [ContinuousAlternatingMap.apply_apply] at hc
      rw [← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht
    · rw [intervalIntegral.integral_undef hint]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
section
noncomputable section

open UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

theorem pbD : PbD := by
  intro V' V F _ _ _ _ _ _ _ _ q H w p hH hw
  have hr : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  refine ⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩
  apply altSmooth V' V' F q (pb H w) p
  intro v
  have h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p := hw.comp p hH
  have h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p := fun i =>
    (hH.fderiv_right hinf).clm_apply contDiffAt_const
  have h3 := applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2
  simpa [pb, Function.comp_def] using h3

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullProdDer
section
noncomputable section

open ContinuousAlternatingMap

namespace UpperTheory.V.Lit.Geo

private theorem line_der {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin q]→L[ℝ] F) (h : DifferentiableAt ℝ Ω (p, t)) :
    HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
      ((fderiv ℝ Ω (p, t) (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t := by
  have h1 : HasDerivAt (fun r : ℝ => (p, r)) ((0 : V), (1 : ℝ)) t := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
  have h2 : HasDerivAt (fun r : ℝ => Ω (p, r)) (fderiv ℝ Ω (p, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := Ω) h.hasFDerivAt h1
  exact (compContinuousLinearMapCLM (ι := Fin q) (F := F) (ContinuousLinearMap.inl ℝ V ℝ)).hasFDerivAt.comp_hasDerivAt t h2

private theorem hasFDerivAt_slice_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) :
    HasFDerivAt (fun x : V => Ω (x, t))
      ((fderiv ℝ Ω (p, t)).comp ((ContinuousLinearMap.id ℝ V).prod 0)) p := by
  have hs : HasFDerivAt (fun x : V => ((x, t) : V × ℝ)) ((ContinuousLinearMap.id ℝ V).prod 0) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  exact h.hasFDerivAt.comp p hs

private theorem fderiv_slice_apply_eq_fderiv_prod_inl {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) (c : Fin m → V × ℝ) (u : V) :
    fderiv ℝ (fun x : V => Ω (x, t) c) p u = fderiv ℝ Ω (p, t) (u, 0) c := by
  rw [((hasFDerivAt_slice_of_differentiableAt p t Ω h).continuousAlternatingMap_apply_const c).fderiv]
  simp

private theorem removeNth_succ_vecCons' {α : Type*} {n : ℕ} (a : α) (w : Fin (n + 1) → α) (i : Fin (n + 1)) :
    Fin.removeNth i.succ (Matrix.vecCons a w) = Matrix.vecCons a (Fin.removeNth i w) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem prodDer : ProdDer := by
  intro V F _ _ _ _ p t
  refine ⟨fun Ω h => ?_, fun q Ω h => ?_⟩
  · convert line_der p t Ω h using 1
    ext v
    simp [curryLeft_apply_apply, extDeriv_apply h, fderiv_continuousAlternatingMap_apply_const h]
  · have hβ : DifferentiableAt ℝ
        (fun x => ((Ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) p := by
      have hs := (hasFDerivAt_slice_of_differentiableAt p t Ω h).differentiableAt
      exact ((compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ V ℝ)).differentiableAt).comp p
        ((((curryLeftLI (𝕜 := ℝ) (E := V × ℝ) (F := F) (n := q)).toContinuousLinearMap.differentiableAt).comp p
          hs).clm_apply (differentiableAt_const _))
    convert line_der p t Ω h using 1
    ext v
    rw [ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
      extDeriv_apply h, Fin.sum_univ_succ, extDeriv_apply hβ]
    have hc : ∀ i : Fin (q + 1), (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ Fin.removeNth i v) =
        Fin.removeNth i (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ v) := fun i => rfl
    simp only [compContinuousLinearMap_apply, curryLeft_apply_apply, fderiv_slice_apply_eq_fderiv_prod_inl p t Ω h,
      fderiv_continuousAlternatingMap_apply_const h, removeNth_succ_vecCons', hc,
      ContinuousLinearMap.flipAlternating_apply_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Fin.removeNth_zero, Matrix.tail_cons, Fin.tail_cons, Fin.val_succ, Fin.val_zero, pow_zero, one_smul,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Function.comp_apply,
      ContinuousLinearMap.inl_apply]
    abel

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem split_eq (s : {r : ℝ // 0 < r}) :
    splitCentre E a (Real.log s.1 / (a * Module.finrank ℚ E)) = Reduction.centralSection E a s := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [KernelIndexFullLattice.splitEq_holds E a]
  refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]

private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem compact_box (C : ℝ) :
    IsCompact {h : GL (Fin a) (Cinf E) | ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C} := by
  have hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C} := by
    have h := isCompact_closedBall (0 : Lie E a) C
    have e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C} := Set.ext fun _ => mem_closedBall_zero_iff
    rw [e] at h
    exact h
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  refine and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have e' : y = (x⁻¹).val := MulOpposite.op_injective e
  rwa [e'] at hy

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.retrFacts :
    RetrFacts := by
  intro E _ _ _ a
  refine ⟨retr_split, retr_left, fun C => ?_⟩
  have hc : Continuous fun h : GL (Fin a) (Cinf E) =>
      Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E) :=
    ((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log
      fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _
  obtain ⟨T, hT⟩ := (compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]
end

