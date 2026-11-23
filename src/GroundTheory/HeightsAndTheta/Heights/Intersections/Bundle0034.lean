module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreIsolFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FibreIsolFinite

theorem isolated_finite (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ)) :
    {x : Fin N → ℂ | (∀ s ∈ S, eval x s = 0) ∧
      ∀ᶠ y in 𝓝 x, (∀ s ∈ S, eval y s = 0) → y = x}.Finite := by
  classical
  let m : (Fin N → ℂ) → Ideal (MvPolynomial (Fin N) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have h1 : X i - C (x i) ∈ m y := by
      rw [← hxy]
      exact RingHom.mem_ker.mpr (by simp)
    have h2 : y i - x i = 0 := by simpa using RingHom.mem_ker.mp h1
    exact (sub_eq_zero.mp h2).symm
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span S)).preimage
    (fun a _ b _ h => hinj h)).subset ?_
  rintro x ⟨hx, hiso⟩
  have hIm : Ideal.span S ≤ m x := by
    rw [Ideal.span_le]
    exact fun s hs => RingHom.mem_ker.mpr (hx s hs)
  have : (m x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hmq : m x ≤ q := by
    intro f hf
    refine IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof N q f x hq.1.1
      (fun g hg => RingHom.mem_ker.mp (hqm hg)) ?_
    filter_upwards [hiso] with y hy hyq
    rw [hy fun s hs => hyq s (hq.1.2 (Ideal.subset_span hs))]
    exact RingHom.mem_ker.mp hf
  show m x ∈ (Ideal.span S).minimalPrimes
  rwa [le_antisymm hqm hmq] at hq

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem sameOrbit_comp_smul {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hvb : ∀ p, (v p).1 = κ p.1) {z' : (Σ k', ι' k') → ℂ} {u : (Σ k, ι k) → ℂ}
    (h : SameOrbit (fun p => z' (v p)) u) (c : K' → ℂ) (hc : ∀ k', c k' ≠ 0) :
    SameOrbit (fun p => c (v p).1 * z' (v p)) u := by
  obtain ⟨c₀, hc₀, hz⟩ := h
  refine ⟨fun k => c (κ k) * c₀ k, fun k => mul_ne_zero (hc _) (hc₀ k), funext fun p => ?_⟩
  have h1 : z' (v p) = c₀ p.1 * u p := congrFun hz p
  show c (v p).1 * z' (v p) = c (κ p.1) * c₀ p.1 * u p
  rw [hvb p, h1, mul_assoc]

theorem minor_of_sameOrbit {w u : (Σ k, ι k) → ℂ} (h : SameOrbit w u) (j : ∀ k, ι k)
    (p : Σ k, ι k) : w p * u ⟨p.1, j p.1⟩ = w ⟨p.1, j p.1⟩ * u p := by
  obtain ⟨c, -, rfl⟩ := h
  show c p.1 * u p * u ⟨p.1, j p.1⟩ = c p.1 * u ⟨p.1, j p.1⟩ * u p
  ring

theorem sameOrbit_of_minor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hκ : Function.Injective κ) (hvb : ∀ p, (v p).1 = κ p.1)
    (hvr : ∀ q : Σ k', ι' k', q.1 ∈ Set.range κ → q ∈ Set.range v)
    {b : (Σ k', ι' k') → ℂ} (i' : ∀ k', ι' k') (hb : ∀ k', b ⟨k', i' k'⟩ = 1)
    {u : (Σ k, ι k) → ℂ} (j : ∀ k, ι k) (hj : ∀ k, u ⟨k, j k⟩ ≠ 0)
    (hm : ∀ p, b (v p) * u ⟨p.1, j p.1⟩ = b (v ⟨p.1, j p.1⟩) * u p) :
    SameOrbit (fun p => b (v p)) u := by
  have hne : ∀ k, b (v ⟨k, j k⟩) ≠ 0 := by
    intro k h0
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    have h1 := hm ⟨k₀, i₀⟩
    dsimp only at h1
    rw [hp, hb, h0, zero_mul, one_mul] at h1
    exact hj k₀ h1
  refine ⟨fun k => b (v ⟨k, j k⟩) / u ⟨k, j k⟩, fun k => div_ne_zero (hne k) (hj k),
    funext fun p => ?_⟩
  show b (v p) = b (v ⟨p.1, j p.1⟩) / u ⟨p.1, j p.1⟩ * u p
  rw [div_mul_eq_mul_div, ← hm p, mul_div_assoc, div_self (hj _), mul_one]

theorem proof : FibreIsolFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hB hA u
  obtain ⟨hκ, -, hvb, hvr⟩ := hB
  have hP' : IsMultiHomogIdeal P' := hA.2.1.2.1
  by_cases hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0
  swap
  · refine ⟨∅, fun z' hz' ho _ => absurd ?_ hu⟩
    intro k
    obtain ⟨i', hi'⟩ := hz'.1 (κ k)
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    obtain ⟨c, -, hc⟩ := ho
    refine ⟨i₀, fun h0 => hi' ?_⟩
    have h1 : z' (v ⟨k₀, i₀⟩) = c k₀ * u ⟨k₀, i₀⟩ := congrFun hc ⟨k₀, i₀⟩
    rw [hp, h0, mul_zero] at h1
    exact h1
  choose j hj using hu
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty ((Σ k', ι' k') ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩

  let S : (∀ k', ι' k') → Set (MvPolynomial (Fin N) ℂ) := fun i' =>
    {s | (∃ f ∈ P', s = rename e (map (Int.castRingHom ℂ) f)) ∨
      (∃ k', s = X (e ⟨k', i' k'⟩) - 1) ∨
      ∃ p : Σ k, ι k, s = X (e (v p)) * C (u ⟨p.1, j p.1⟩) - X (e (v ⟨p.1, j p.1⟩)) * C (u p)}
  have hS : ∀ i' (y : Fin N → ℂ), (∀ s ∈ S i', eval y s = 0) ↔
      ((∀ f ∈ P', eval (y ∘ e) (map (Int.castRingHom ℂ) f) = 0) ∧ (∀ k', y (e ⟨k', i' k'⟩) = 1) ∧
        ∀ p, y (e (v p)) * u ⟨p.1, j p.1⟩ = y (e (v ⟨p.1, j p.1⟩)) * u p) := by
    intro i' y
    constructor
    · intro h
      refine ⟨fun f hf => ?_, fun k' => ?_, fun p => ?_⟩
      · have h1 := h _ (Or.inl ⟨f, hf, rfl⟩)
        rwa [eval_rename] at h1
      · have h1 := h _ (Or.inr (Or.inl ⟨k', rfl⟩))
        simp only [map_sub, map_one, eval_X] at h1
        exact sub_eq_zero.mp h1
      · have h1 := h _ (Or.inr (Or.inr ⟨p, rfl⟩))
        simp only [map_sub, map_mul, eval_X, eval_C] at h1
        exact sub_eq_zero.mp h1
    · rintro ⟨h1, h2, h3⟩ s (⟨f, hf, rfl⟩ | ⟨k', rfl⟩ | ⟨p, rfl⟩)
      · rw [eval_rename]
        exact h1 f hf
      · simp only [map_sub, map_one, eval_X]
        rw [h2 k', sub_self]
      · simp only [map_sub, map_mul, eval_X, eval_C]
        rw [h3 p, sub_self]
  have hfin := fun i' => isolated_finite N (S i')
  let T : Finset ((Σ k', ι' k') → ℂ) :=
    Finset.univ.biUnion fun i' : (∀ k', ι' k') => (hfin i').toFinset.image fun y => y ∘ e
  refine ⟨T, fun z' hz' ho hiso => ?_⟩
  choose i' hi' using hz'.1
  obtain ⟨ε, hε, hball⟩ := hiso

  let d : K' → ℂ := fun k' => (z' ⟨k', i' k'⟩)⁻¹
  have hd : ∀ k', d k' ≠ 0 := fun k' => inv_ne_zero (hi' k')
  let a : (Σ k', ι' k') → ℂ := fun q => d q.1 * z' q
  have ha1 : ∀ k', a ⟨k', i' k'⟩ = 1 := fun k' => inv_mul_cancel₀ (hi' k')
  have haP : a ∈ mcPts P' := mcPts_smul hP' d hd hz'
  have hao : SameOrbit (fun p => a (v p)) u := sameOrbit_comp_smul hvb ho d hd
  let w₀ : Fin N → ℂ := a ∘ e.symm
  have hw₀ : w₀ ∘ e = a := funext fun q => by simp [w₀]
  have hw₀Z : ∀ s ∈ S i', eval w₀ s = 0 := by
    refine (hS i' w₀).mpr ⟨by rw [hw₀]; exact haP.2, fun k' => ?_, fun p => ?_⟩
    · simpa [w₀] using ha1 k'
    · simpa [w₀] using minor_of_sameOrbit hao j p
  have hw₀iso : ∀ᶠ y in 𝓝 w₀, (∀ s ∈ S i', eval y s = 0) → y = w₀ := by
    let g : (Fin N → ℂ) → (Σ k', ι' k') → ℂ := fun y q => z' ⟨q.1, i' q.1⟩ * y (e q)
    have hg : Continuous g := continuous_pi fun q => continuous_const.mul (continuous_apply _)
    have hgw : g w₀ = z' := funext fun q => by
      show z' ⟨q.1, i' q.1⟩ * (d (e.symm (e q)).1 * z' (e.symm (e q))) = z' q
      rw [Equiv.symm_apply_apply]
      exact mul_inv_cancel_left₀ (hi' q.1) (z' q)
    have hmem : g ⁻¹' Metric.ball z' ε ∈ 𝓝 w₀ :=
      hg.continuousAt.preimage_mem_nhds (by rw [hgw]; exact Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem] with y hy hyS
    obtain ⟨h1, h2, h3⟩ := (hS i' y).mp hyS
    have hbP : y ∘ e ∈ mcPts P' := ⟨fun k' => ⟨i' k', by simp [h2 k']⟩, h1⟩
    have hbo : SameOrbit (fun p => (y ∘ e) (v p)) u :=
      sameOrbit_of_minor (b := y ∘ e) hκ hvb hvr i' (fun k' => h2 k') j hj h3
    have hgP : g y ∈ mcPts P' := mcPts_smul hP' (fun k' => z' ⟨k', i' k'⟩) hi' hbP
    have hgo : SameOrbit (fun p => g y (v p)) u :=
      sameOrbit_comp_smul hvb hbo (fun k' => z' ⟨k', i' k'⟩) hi'
    obtain ⟨c₁, -, hgz⟩ := hball (g y) hgP hgo hy
    have hc1 : ∀ k', c₁ k' = 1 := fun k' => by
      have h : z' ⟨k', i' k'⟩ * y (e ⟨k', i' k'⟩) = c₁ k' * z' ⟨k', i' k'⟩ := congrFun hgz ⟨k', i' k'⟩
      rw [h2 k', mul_one] at h
      exact mul_right_cancel₀ (hi' k') (h.symm.trans (one_mul _).symm)
    funext x
    have h : z' ⟨(e.symm x).1, i' (e.symm x).1⟩ * y (e (e.symm x)) = c₁ (e.symm x).1 * z' (e.symm x) :=
      congrFun hgz (e.symm x)
    rw [hc1, one_mul, Equiv.apply_symm_apply] at h
    show y x = (z' ⟨(e.symm x).1, i' (e.symm x).1⟩)⁻¹ * z' (e.symm x)
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hi' _), one_mul]
  refine ⟨w₀ ∘ e, Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _,
    Finset.mem_image.mpr ⟨w₀, (hfin i').mem_toFinset.mpr ⟨hw₀Z, hw₀iso⟩, rfl⟩⟩, ?_⟩
  rw [hw₀]
  exact ⟨fun k' => z' ⟨k', i' k'⟩, hi', funext fun q => (mul_inv_cancel_left₀ (hi' q.1) (z' q)).symm⟩

end FibreIsolFinite

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian

namespace SemipositiveTwist

set_option linter.unusedSectionVars false

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_noZeroBlock : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

def F (k : K) (y : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))

theorem blk_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    (fun i => z ⟨k, i⟩ : ι k → ℂ) ≠ 0 := by
  obtain ⟨i, hi⟩ := hz k
  exact fun h0 => hi (congrFun h0 i)

theorem rho_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) :=
  (fsMetric (ι := ι k)).pos _ (blk_ne hz k)

theorem rho_eq (k : K) (y : (Σ k, ι k) → ℂ) :
    (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem contDiffAt_F {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by
  have hρ : ContDiffAt ℝ 2 (fsMetric (ι := ι k)).ρ (blk (ι := ι) k z) :=
    ((GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)).contDiffAt
      (isOpen_ne.mem_nhds (blk_ne hz k))).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := hρ.log (rho_pos hz k).ne'
  have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk]
  exact hφ.comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt

theorem levi_F_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by
  have hρ : ContDiffAt ℝ 2 (fsMetric (ι := ι k)).ρ (blk (ι := ι) k z) :=
    ((GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)).contDiffAt
      (isOpen_ne.mem_nhds (blk_ne hz k))).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := hρ.log (rho_pos hz k).ne'
  have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) hφ]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (blk_ne hz k) _

end Blocks

section Levi

variable {J : Type} [Fintype J]

theorem levi_add_sum {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have heq : (fun y => g y + ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => g y' + ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq, ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (hf a) w, ih.2, Finset.sum_insert ha]
    exact ⟨ih.1.add (contDiffAt_const.mul (hf a)), by ring⟩

theorem levi_zero_fun (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => (0 : ℝ)) z w = 0 := by
  simp [ReciprocityTheory.AnForm.levi]

theorem laplacian_line_eq_levi {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by
  have h1 : ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) (fun _ => 0) (Pi.single 0 1) =
      Δ (fun t : ℂ => φ (z + t • v)) 0 / 4 :=
    ReciprocityTheory.AnForm.A.leviOne (fun t : ℂ => φ (z + t • v)) 0
  set L : (Fin 1 → ℂ) →L[ℂ] (J → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight v with hL
  have hτ : AnalyticAt ℂ (fun w => z + L w) (fun _ => 0) :=
    analyticAt_const.add (L.analyticAt _)
  have hτ0 : z + L (fun _ => (0 : ℂ)) = z := by
    simp [hL]
  have hcomp : (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) = φ ∘ fun w => z + L w := by
    funext w
    simp [hL]
  have hD : fderiv ℂ (fun w => z + L w) (fun _ => 0) (Pi.single 0 1) = v := by
    rw [((L.hasFDerivAt).const_add z).fderiv]
    simp [hL]
  have hφ' : ContDiffAt ℝ 2 φ (z + L (fun _ => 0)) := by
    rw [hτ0]
    exact hφ
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp _ hτ hφ', hτ0, hD] at h1
  linarith

end Levi

end SemipositiveTwist


open SemipositiveTwist in
theorem SemiPosTwist.proof (hB : TorusInvLevi.Statement) : SemiPosTwist.Statement := by
  intro K _ ι _ M hM
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (M.h y) + ∑ k, (-(M.a k : ℝ)) * F k y with hu
  have hlogM : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(M.a k : ℝ)) (hlogM z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι := ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι := ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (M.h (fun p => c p.1 * z p)) =
        ∑ k, (M.a k : ℝ) * Real.log ‖c k‖ + Real.log (M.h z) := by
      rw [M.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (M.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (M.h (fun p => c p.1 * z p)) + ∑ k, (-(M.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (M.h z) + ∑ k, (-(M.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_zero_fun] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(M.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (M.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(M.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(M.a k : ℝ)| ≤ ∑ k, |(M.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(M.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (M.a k : ℝ)
    linarith
  set T : HermLine ι := HermLine.sqMetric (fun _ => N) with hT
  have hlogT : ∀ y : (Σ k, ι k) → ℂ, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Real.log (T.h y) = ∑ k, (N : ℝ) * F k y := by
    intro y hy
    have h : T.h y = ∏ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ^ N := by
      simp only [hT, HermLine.sqMetric, rho_eq]
    rw [h, Real.log_prod (fun k _ => pow_ne_zero _ (rho_pos hy k).ne')]
    simp only [Real.log_pow, F]
  refine ⟨T, isSmoothHerm_sqMetric _, ?_, ?_⟩
  · intro z hz v
    have hs := levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => (N : ℝ)) contDiffAt_const (contDiffAt_F hz) v
      Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log (T.h y)) =ᶠ[𝓝 z] fun y => 0 + ∑ k, (N : ℝ) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      rw [hlogT y hy, zero_add]
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v,
      hs.2, levi_zero_fun, zero_add]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (levi_F_nonneg hz k v))
  · intro z hz v
    have hs := levi_add_sum u F (fun k => (M.a k : ℝ) + N) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log ((M.tensor T).h y)) =ᶠ[𝓝 z]
        fun y => u y + ∑ k, ((M.a k : ℝ) + N) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      show Real.log (M.h y * T.h y) = _
      rw [Real.log_mul (M.pos y hy).ne' (T.pos y hy).ne', hlogT y hy, hu]
      simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2]
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, ((M.a k : ℝ) + N) * ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOver
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {n : ℕ}

def ptsOver (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧
    (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) = w}

end Over

def GenericPointsCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ → (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y,
      (ptsOver P' v Ψ w).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreBij
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreBij.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    Set.BijOn (fibreOf κ G) {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'}
      (divSupp (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (baseSubst κ G s))

end

end GroundTheory.Heights₂.Heights.Inter
end

