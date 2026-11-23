module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzSliceContDiffOn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableHf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdAnalytic
section
noncomputable section

open MeasureTheory Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem Fd_analytic (m : ℕ) : AnalyticOnNhd ℂ (Fd (n := n) m) (DomZ n) := by
  letI : TopologicalSpace (M2 n) := (inferInstance : NormedAddCommGroup (M2 n)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hU := (fzHol n m 0).2.2
  intro y hy
  have h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)
  have hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y := analyticAt_const.prod analyticAt_id
  have h2 := h1.comp hl
  refine h2.congr ?_
  filter_upwards [isOpen_domZ.mem_nhds hy] with w hw
  exact (Fd_eq m hw).symm

theorem fdProps : FdProps := by
  intro n m
  refine ⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩
  intro Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef
  have hherm : Continuous (herm (n := n)) := by unfold herm; fun_prop
  have hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hy : Continuous y :=
    (((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul
      continuous_const
  have hyD : ∀ p, y p ∈ DomZ n := fun p =>
    gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)
  set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def
  have hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n) :=
    ((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn
  set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef
  set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def
  set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef
  have hS : IsCompact S := isCompact_univ.prod hψs
  have hzero : ∀ p, p ∉ S → ψ p.2 = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)
  have hFc : ∀ z, Continuous (F z) := fun z =>
    (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy)
      (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))
  have hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2 :=
    (hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk
      (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))
  have hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) →
      Integrable G (μ.prod volume) := by
    intro G hG h0
    refine hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)
    refine closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))
    by_contra h; exact hp (h0 p h)
  have hFi : ∀ z, Integrable (F z) (μ.prod volume) := fun z =>
    hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn
  have hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume) :=
    (integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p z hz => by
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩
      · rw [Set.indicator_of_notMem hp]
        simp [hF'def, hzero p hp])
    hbound_int
    (Filter.Eventually.of_forall fun p z _ => by
      have hd : DifferentiableAt ℂ U (z, y p) :=
        (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)
      have hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z :=
        (hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))
      have h1 := hd.hasFDerivAt.comp_hasDerivAt z hl
      exact (h1.mul_const (ψ p.2)).const_mul (ρ p.1))
  have hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2))
      (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume) := by
    intro G hG
    rw [integral_prod _ hG]
    unfold tOp
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hydef]
    exact (integral_const_mul _ _).symm
  have e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume) := by
    funext z; exact hT (fz m 0 z) (hFi z)
  have e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x := by
    have hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2) := by
      funext p; simp only [hF'def, hU'def, Fd_eq m (hyD p)]; rfl
    rw [hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]
  rw [e1, hderiv.2.deriv, e2]

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperators
section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_at_zero_mul_compact (m : ℕ) (e : ℤ) (x : M2 n) {k : M2 n} (hk : InK k) :
    fz m e 0 (x * k) = fz m e 0 x * fz m e 0 k := by
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  rw [first_cayley_block_mul_compact x hk, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow]
  ring

theorem norm_fz0K (m : ℕ) (e : ℤ) {k : M2 n} (hk : InK k) : star (fz m e 0 k) * fz m e 0 k = 1 := by
  have hk1 : Complex.normSq (det k) = 1 := by
    have h := congrArg Matrix.det hk.2
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      mul_comm, Complex.mul_conj] at h
    exact_mod_cast h
  have hu := normSq_det_u1K hk
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one, map_mul, map_zpow₀, hk1, hu, _root_.one_zpow]
  simp

theorem first_cayley_block_one : u1 (1 : M2 n) = 1 := by
  unfold u1
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp
theorem second_cayley_block_one : u2 (1 : M2 n) = 1 := by
  unfold u2
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)

include hK in
theorem ιK (k : Kg) : InK (ι k) := (hK _).mpr ⟨k, rfl⟩

include hK in
theorem first_cayley_block_inv (k : Kg) : u1 (ι k⁻¹) = (u1 (ι k))⁻¹ := by
  have h : u1 (ι k⁻¹) * u1 (ι k) = 1 := by
    rw [← first_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, first_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem second_cayley_block_inv (k : Kg) : u2 (ι k⁻¹) = (u2 (ι k))⁻¹ := by
  have h : u2 (ι k⁻¹) * u2 (ι k) = 1 := by
    rw [← second_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, second_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem vacuum_at_zero_inv_star (m : ℕ) (e : ℤ) (k : Kg) : fz m e 0 (ι k⁻¹) = star (fz m e 0 (ι k)) := by
  have hk := ιK ι hK k
  have h1 : fz m e 0 (ι k⁻¹) * fz m e 0 (ι k) = 1 := by
    rw [← vacuum_at_zero_mul_compact m e _ hk, ← map_mul, inv_mul_cancel, map_one]
    unfold fz
    simp [first_cayley_block_one]
  have h2 := norm_fz0K m e hk
  have hne : fz m e 0 (ι k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

include hK in
theorem rho_shift (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k1 k : Kg) :
    rhoP ι m e Y (k1⁻¹ * k) = fz m e 0 (ι k1) * rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) k := by
  have ha := ιK ι hK k1
  have hb := ιK ι hK k
  have hdet : IsUnit (u2 (ι k1)).det := Matrix.isUnit_det_of_left_inverse (second_cayley_block_compact_unitary ha)
  unfold rhoP
  rw [map_mul, vacuum_at_zero_mul_compact m e _ hb, vacuum_at_zero_inv_star ι hK m e k1, second_cayley_block_mul_compact _ hb, first_cayley_block_mul_compact _ hb,
    second_cayley_block_inv ι hK k1, first_cayley_block_inv ι hK k1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet]
  simp only [star_mul', star_star, Matrix.mul_assoc]
  ring

theorem Hf_up (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p y : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (z : ℂ) :
    Hf m e ψ a b z (p * y) = lam m e z p * Hf m e ψ a b z y := by
  simp only [Hf]
  rw [← integral_const_mul]
  congr 1; funext t
  rw [show p * y * a * nU (herm t) * b = p * (y * a * nU (herm t) * b) by simp only [Matrix.mul_assoc],
    fz_up hp hp21 (inG_path hy ha hb t)]
  ring


include hK in
theorem tOp_formula (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (k1 : Kg) (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) (p * ι k1) =
      lam m e z p * fz m e 0 (ι k1) * tOp μ ι (rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹)) ψ a b (fz m e z) 1 := by
  unfold tOp
  have hs := integral_mul_left_eq_self (μ := μ) (fun k => rhoP ι m e Y k *
    ∫ t, fz m e z (p * ι k1 * ι k * a * nU (herm t) * b) * ψ t) k1⁻¹
  rw [← hs, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext k
  have hι : ι k1 * ι (k1⁻¹ * k) = ι k := by
    rw [← map_mul, mul_inv_cancel_left]
  have hH := Hf_up m e ψ ha hb hp hp21 (ιK ι hK k).1 z
  unfold Hf at hH
  rw [rho_shift ι hK m e Y k1 k, Matrix.mul_assoc p (ι k1), hι, hH]
  simp only [Matrix.one_mul]
  ring

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SingularTestsKillVacuum
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

theorem lt3 : SingularTestsKillVacuum := by
  intro n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ ha hb hx
  have mulG : ∀ {p q : M2 n}, InG p → InG q → InG (p * q) := by
    intro p q hp hq
    unfold InG at *
    calc (p * q)ᴴ * JJ n * (p * q) = qᴴ * (pᴴ * JJ n * p) * q := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hp, hq]
  have hG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have h : ∀ k, ∫ t, fz m e 0 (x * ι k * a * nU (herm t) * b) * ψ t = 0 := fun k =>
    L3.vanish_all hmn e _ b (mulG (mulG hx (hG k)) ha) hb ψ hψ
  simp only [tOp, h, mul_zero, integral_zero]

end PositivityTheory.Rg.Sw.HSt
end
end

