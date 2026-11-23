module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV

theorem isStepRows_stepCols {N j : ℕ} (i : Fin N) : IsStepRows N j i (stepCols N j i) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  split_ifs at ha ⊢ with h
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.1
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minorIJ_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minorIJ_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem sum_minor_one {N : ℕ} (a : Finset (Fin N) → ℂ) (C : Finset (Fin N)) :
    ∑ I, a I * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I C = a C := by
  rw [Finset.sum_eq_single C (fun I _ h => by rw [minorIJ_one_ne h, mul_zero])
    (fun h => absurd (Finset.mem_univ C) h), minorIJ_one_same, mul_one]

theorem sum_minor_mul {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h) (m : μ) :
    ∑ I, a₁ m I * minorIJ (S * h) I (stepCols N j i) = c * ∑ I, a₂ m I * minorIJ h I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj
  have off' : ∀ I', ¬ IsStepRows N j i I' → minorIJ h I' (stepCols N j i) = 0 := fun I' hI =>
    (off h I' hh hI).resolve_right (stepCols_ne_empty i)
  simp only [cb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [← mul_assoc, ← hS m I' hI, Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => by ring
  · simp [off' I' hI]

theorem coef_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} [Fintype μ] (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (b : μ → ℂ) (S S' : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (hd : IsBlockDiag j S') (hSS : S * S' = 1) (hb : ∑ m, b m * a₁ m (stepCols N j i) = 1) : c ≠ 0 := by
  intro hc
  have h0 : ∀ m, a₁ m (stepCols N j i) = 0 := fun m => by
    have e1 := sum_minor_mul hj i a₁ a₂ S c hS S' hd m
    rw [hSS, hc, zero_mul, sum_minor_one (a₁ m)] at e1
    exact e1
  simp [h0] at hb

theorem map_inv_eq {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} (T : Matrix (Fin N) (Fin N) Ω)
    (hd : T.det ≠ 0) : T⁻¹.map φ = (T.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero φ) (map_one φ)

theorem map_rel {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} {μ : Type}
    (u₁ u₂ : μ → Finset (Fin N) → Ω) (T₁ T₂ : Matrix (Fin N) (Fin N) Ω) (h₁ : T₁.det ≠ 0) (ρ : Ω)
    (P : Finset (Fin N) → Prop)
    (h : ∀ m I', P I' → ∑ I, u₁ m I * minorIJ (T₁⁻¹ * T₂) I I' = ρ * u₂ m I') :
    ∀ m I', P I' → ∑ I, φ (u₁ m I) * minorIJ ((T₁.map φ)⁻¹ * T₂.map φ) I I' = φ ρ * φ (u₂ m I') :=
  fun m I' hI' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_inv_eq φ T₁ h₁, ← Matrix.map_mul, ← map_mul, ← h m I' hI', map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, minorIJ_map]

section Values

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂]
  {x₂ : (Σ k, ι₂ k) → Ω₂} {zb : (Σ k, ι₂ k) → ℂ}

theorem reg_values (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} (i : Fin N) {μ : Type} [Fintype μ]
    (U₁ U₂ : μ → Finset (Fin N) → Ω₂) (V : μ → Ω₂) (A : Matrix (Fin N) (Fin N) Ω₂) (r : Ω₂)
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j i I₀)
    (hU₁ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₁ m I)) (hU₂ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₂ m I))
    (hV : ∀ m, RegAt x₂ (mCoordIdeal zb) (V m)) (hA : ∀ a b, RegAt x₂ (mCoordIdeal zb) (A a b))
    (hrel : ∀ m I', IsStepRows N j i I' → ∑ I, U₁ m I * minorIJ A I I' = r * U₂ m I')
    (hinv : ∑ m, V m * U₂ m I₀ = 1) :
    RegAt x₂ (mCoordIdeal zb) r ∧ ∀ m I', IsStepRows N j i I' →
      ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' = valAt x₂ r zb * valAt x₂ (U₂ m I') zb := by
  have hsum : ∀ m I', RegAt x₂ (mCoordIdeal zb) (∑ I, U₁ m I * minorIJ A I I') ∧
      valAt x₂ (∑ I, U₁ m I * minorIJ A I I') zb =
        ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' := fun m I' => by
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun I => U₁ m I * minorIJ A I I') fun I _ =>
      ValRing.regAt_mul (hU₁ m I) (reg_minor hz hA I I').1
    refine ⟨h1, h2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(reg_mul hz (hU₁ m I) (reg_minor hz hA I I').1).2, (reg_minor hz hA I I').2]
  have hr : RegAt x₂ (mCoordIdeal zb) r := by
    have e : r = ∑ m, V m * ∑ I, U₁ m I * minorIJ A I I₀ := by
      simp only [hrel _ I₀ hI₀]
      calc r = r * ∑ m, V m * U₂ m I₀ := by rw [hinv, mul_one]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
    exact (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hV m) (hsum m I₀).1).1
  refine ⟨hr, fun m I' hI' => ?_⟩
  rw [← (hsum m I').2, hrel m I' hI']
  exact (reg_mul hz hr (hU₂ m I')).2

theorem valAt_one' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (1 : Ω₂) zb = 1 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.2.1

theorem valAt_zero' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (0 : Ω₂) zb = 0 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.1

theorem valMat_one (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N : ℕ} :
    valMat x₂ zb (1 : Matrix (Fin N) (Fin N) Ω₂) = 1 := by
  ext a b
  show valAt x₂ ((1 : Matrix (Fin N) (Fin N) Ω₂) a b) zb = _
  by_cases e : a = b
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, valAt_one' hz]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, valAt_zero' hz]

theorem valMat_blockDiag (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} {A : Matrix (Fin N) (Fin N) Ω₂}
    (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x₂ zb A) := fun a b h => by
  show valAt x₂ (A a b) zb = 0
  rw [hA a b h, valAt_zero' hz]

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K₂ _ ι₂ _ Ω₂ _ x₂ φ zb F₁ F₂ hz hF₁ hF₂ hc₁ hc₂ p k hp hu hS
  obtain ⟨ρ, -, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.plucker_change_of_frame K ι Φ y Ψ N j M F₁ F₂ hF₁ hF₂ hc₁ hc₂ p k hp
  have hd₁ := (hF₁.1 p.1).2
  have hd₂ := (hF₂.1 p.1).2
  have hstep : IsStepRows N j p.2 (stepCols N j p.2) := isStepRows_stepCols p.2
  have hinv : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F →
      ∑ m : ι k, φ (F.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F.u ⟨k, m⟩ (stepCols N j p.2)) = 1 := fun F hF => by
    have e := hF.2.2.1 p k hp _ _ hstep hstep
    rw [if_pos rfl] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one φ, ← e, map_sum]
    exact Finset.sum_congr rfl fun m _ => (map_mul φ _ _).symm
  have hrel := map_rel φ (fun (m : ι k) I => F₁.u ⟨k, m⟩ I) (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) _ _ hd₁ ρ
    (IsStepRows N j p.2) hρ
  obtain ⟨hr, hval⟩ := reg_values hz p.2 (fun (m : ι k) I => φ (F₁.u ⟨k, m⟩ I))
    (fun (m : ι k) I => φ (F₂.u ⟨k, m⟩ I)) (fun m : ι k => φ (F₂.u' (stepCols N j p.2) ⟨k, m⟩)) _ (φ ρ) _ hstep
    (fun m I => (hu m I).1) (fun m I => (hu m I).2.1) (fun m => (hu m _).2.2.2) (fun a b => (hS a b).1) hrel
    (hinv F₂ hF₂)
  refine ⟨valAt x₂ (φ ρ) zb, ?_, fun h hh m => sum_minor_mul M.j_le p.2 _ _ _ _ hval h hh m⟩
  have hu₂ : IsUnit (F₂.T p.1).det := isUnit_iff_ne_zero.2 hd₂
  have hu₁ : IsUnit (F₁.T p.1).det := isUnit_iff_ne_zero.2 hd₁
  have e21 : ((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ = ((F₂.T p.1)⁻¹ * F₁.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₂]
  have e12 : ((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ = ((F₁.T p.1)⁻¹ * F₂.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₁]
  have hprod : (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) = 1 := by
    rw [e12, e21, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₂,
      Matrix.nonsing_inv_mul _ hu₁]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hbd : IsBlockDiag j (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) := by
    rw [e21]
    exact ((((hF₂.1 p.1).1.inv hu₂).mul (hF₁.1 p.1).1).map φ)
  have hSS := (regMat_mul hz (fun a b => (hS a b).1) (fun a b => (hS a b).2)).2
  rw [hprod, valMat_one hz] at hSS
  refine coef_ne_zero M.j_le p.2 _ _ (fun m : ι k => valAt x₂ (φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩)) zb) _ _ _ hval
    (valMat_blockDiag hz hbd) hSS.symm ?_
  have e := (reg_sum hz Finset.univ
    (fun m : ι k => φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F₁.u ⟨k, m⟩ (stepCols N j p.2)))
    fun m _ => ValRing.regAt_mul (hu m _).2.2.1 (hu m _).1).2
  rw [hinv F₁ hF₁, valAt_one' hz] at e
  rw [e]
  exact Finset.sum_congr rfl fun m _ => (reg_mul hz (hu m _).2.2.1 (hu m _).1).2.symm

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZero
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramReal

theorem gram_det_im_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ) :
    (R.gram u).det.im = 0 := by
  have hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a) := fun _ _ => rfl
  have hHm : ∀ i j, star (R.Hm i j) = R.Hm j i := fun i j => R.10.apply j i
  have hH : (R.gram u)ᴴ = R.gram u := by
    ext a b
    rw [Matrix.conjTranspose_apply, hg, hg]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hHm]
    ring
  have hd : star (R.gram u).det = (R.gram u).det := by
    rw [← Matrix.det_conjTranspose, hH]
  exact Complex.conj_eq_iff_im.mp hd

end GlobalTheory.CompanionTheory.Ar.Cusp.GramReal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDet
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange

theorem gram_eq' {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ := by
  have hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a) := fun _ _ => rfl
  ext a b
  rw [hg]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  intro E _ _ _ g Λ _ _ R m u f T hf
  have hfT : Matrix.of f = Tᵀ * Matrix.of u := by
    ext i k
    simp [hf, Matrix.mul_apply, Finset.sum_apply]
  have hc : (Tᵀ.map (starRingEnd ℂ)).det = starRingEnd ℂ T.det := by
    rw [Matrix.transpose_map, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have hn : ((‖T.det‖ ^ 2 : ℝ) : ℂ) = T.det * starRingEnd ℂ T.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq', GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq',
    hfT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show Tᵀ.map (starRingEnd ℂ) * (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * ((Matrix.of u)ᵀ * T) =
      Tᵀ.map (starRingEnd ℂ) * ((Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ) * T by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.det_mul, Matrix.det_mul, hc, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversal
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef

open scoped ComplexOrder

theorem star_form_eq {g : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ} (hH : Hb.IsHermitian)
    (x y : Fin g → ℂ) :
    star (x ⬝ᵥ Hb *ᵥ star y) = y ⬝ᵥ Hb *ᵥ star x := by
  have h1 : ∀ w : Fin g → ℂ, star (x ⬝ᵥ w) = star w ⬝ᵥ star x := by
    intro w
    simp [dotProduct, mul_comm]
  rw [h1, star_mulVec, star_star, hH.eq, dotProduct_mulVec]

theorem gram_form_eq {g k : ℕ} (Hb : Matrix (Fin g) (Fin g) ℂ) (q : Fin k → Fin g → ℂ)
    (l : Fin k → ℂ) :
    star l ⬝ᵥ (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)) *ᵥ l =
      (∑ c, l c • q c) ⬝ᵥ Hb *ᵥ star (∑ c, l c • q c) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  simp only [dotProduct_sum, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem gram_posDef {g k : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ}
    {U : Submodule ℂ (Fin g → ℂ)} {q : Fin k → Fin g → ℂ} (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext c c'
    simp only [conjTranspose_apply, of_apply]
    exact star_form_eq hH (q c) (q c')
  · intro l hl
    rw [gram_form_eq]
    set v : Fin g → ℂ := ∑ c, l c • q c with hv
    have hre : 0 < (v ⬝ᵥ Hb *ᵥ star v).re := by
      refine lt_of_le_of_ne (hpos v).1 fun h0 => hl (hind l ?_)
      exact (hpos v).2 h0.symm
    have him : (v ⬝ᵥ Hb *ᵥ star v).im = 0 :=
      Complex.conj_eq_iff_im.mp (star_form_eq hH v v)
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem gram_det_re_pos (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ)
    (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ) (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re :=
  (Complex.lt_def.mp (gram_posDef hH hpos hind).det_pos).1

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptMorphismCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_morphism_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver | exact GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamAlgebraicIndependentFinrank
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem genFam_degree_over_subfield : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_degree

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamily
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem isGenFam_revInv_ite : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_revgen

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSectionDiagSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isSection_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  refine ⟨fun x => ?_, fun x x' w hw => ?_⟩
  · obtain ⟨⟨F, H, hC⟩, -, -, hsrc, -, hu, -⟩ := hL x
    intro l z hz
    have hz' : z ∈ (RW.A.chart l).target ∩ (RW.A.chart l).symm ⁻¹' (ψ x).source :=
      ⟨hz.1, hsrc hz.2⟩
    have h1 : AnalyticAt ℂ (u x ∘ (RW.A.chart l).symm) z := hu l z hz
    have h2 : AnalyticAt ℂ ((ψ x) ∘ (RW.A.chart l).symm) z := (hC.1 l).1 z hz'
    have h3 : AnalyticAt ℂ (fun w => ((ψ x) ∘ (RW.A.chart l).symm) w (i₀ x)) z :=
      analyticAt_pi_iff.1 h2 (i₀ x)
    exact h1.mul h3
  · have hx : 0 < (potA M τ a k₀).h (RW.lift x w) :=
      (potA M τ a k₀).pos _ (RW.mem x w ((hL x).2.2.2.2.1 hw.1)).1
    have hx' : 0 < (potA M τ a k₀).h (RW.lift x' w) :=
      (potA M τ a k₀).pos _ (RW.mem x' w ((hL x').2.2.2.2.1 hw.2)).1
    have hg := locSec_norm_eq K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x x' (ψ x) (ψ x') (kb x) (kb x') (σ x) (σ x')
      (i₀ x) (i₀ x') (V x) (V x') (u x) (u x') hblk hW (hL x) (hL x') w hw
    have key : ∀ (s h : ℝ), 0 < h → s * Real.exp (-(Real.log h + c)) = s / h * Real.exp (-c) := by
      intro s h hh
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log h), Real.exp_log hh, div_eq_mul_inv, mul_assoc]
    show ‖u x w * ψ x w (i₀ x)‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x w)) + c)) =
      ‖u x' w * ψ x' w (i₀ x')‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x' w)) + c))
    rw [key _ _ hx, key _ _ hx', hg]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

