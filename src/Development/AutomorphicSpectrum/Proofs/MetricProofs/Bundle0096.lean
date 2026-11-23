module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEq
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem x_chart_ne_of_pt (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb))
    (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (by
  have h1 : (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∈ mCoordIdeal M.x := by
    show mConeMap M.x (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 : zb ⟨k, F.c k⟩ = 0 := by simpa using hz.2 _ h1
  show mConeMap zb (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h2, map_zero, zero_mul])

theorem transPt_ratio_base [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (k : K) (h : ∀ p, M.blk p ≠ some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  have e : ∀ m : ι k, transPt Cv ⟨k, m⟩ = y' ⟨(Cv.v ⟨⟨k, h⟩, m⟩).1.1, (Cv.v ⟨⟨k, h⟩, m⟩).2⟩ := fun m => by
    have h1 := transPt_base Cv ⟨⟨k, h⟩, m⟩
    rw [← Cv.x_eq, ← M'.y_base] at h1
    exact h1
  rw [e, e]
  refine IntermediateField.subset_adjoin _ _ ⟨_, _, ?_, rfl⟩
  show (Cv.v ⟨⟨k, h⟩, i⟩).1.1 = (Cv.v ⟨⟨k, h⟩, i₂⟩).1.1
  rw [Cv.block.2.2.1, Cv.block.2.2.1]

theorem transPt_ratio_step [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (hy : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' := by
    rcases e : M'.blk p with _ | k'
    · have h2 := (M.blk_none p).2 ((M'.blk_none p).1 e)
      rw [hp] at h2
      cases h2
    · exact ⟨k', rfl⟩
  obtain ⟨zb, hzb⟩ := GlobalTheory.T.multiprojective_points_nonempty _ _ _ M'.x M'.x_ne
  have hzv := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  obtain ⟨F', hF', hG'⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').2.1 zb hzb
  obtain ⟨F, hF, hG⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.1 _ hzv
  obtain ⟨c, hc, hcs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF
    (fun k => x_chart_ne_of_pt M' hzb hG' k) (fun k => x_chart_ne_of_pt M hzv hG k) p k k' hp hk'
  obtain ⟨c', hc'⟩ := hy k'
  have hreg : ∀ (q : Σ k, ι k) (r : Σ k, ι' k),
      algebraMap M'.Ω Φ' (coE Cv F' F p q r) ∈ blockFnField y' := fun q r =>
    _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField K' ι' Φ' y' Ψ N j M' zb _ hzb
      (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p q r).1
  let S : ι k → Φ' := fun m =>
    ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
  have hS : ∀ m, S m ∈ blockFnField y' := fun m =>
    sum_mem fun m' _ => mul_mem (hreg _ _) (IntermediateField.subset_adjoin _ _ ⟨⟨k', m'⟩, ⟨k', c'⟩, rfl, rfl⟩)
  have e : ∀ m, transPt Cv ⟨k, m⟩ = (c * y' ⟨k', c'⟩) * S m := fun m => by
    rw [hcs m, mul_assoc]
    congr 1
    simp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  rw [e, e, mul_div_mul_left _ _ (mul_ne_zero hc hc')]
  exact div_mem (hS _) (hS _)

end

theorem blockFnField_pair_transPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv _ hy
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨p, q, h, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨inrV p, inrV q, by simp only [inrV, h], rfl⟩
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k | k, i⟩, ⟨k₂ | k₂, i₂⟩, h, rfl⟩
    · obtain rfl : k = k₂ := Sum.inl.inj h
      show transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y'
      by_cases hb : ∀ p, M.blk p ≠ some k
      · exact transPt_ratio_base Cv k hb i i₂
      · exact transPt_ratio_step Cv hy (stepOf M k hb) k (blk_stepOf M k hb) i i₂
    · cases h
    · cases h
    · obtain rfl : k = k₂ := Sum.inr.inj h
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i₂⟩, rfl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := fun h => hq (by
  have hm : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h0 : z q = 0 := by simpa using hz.2 _ hm
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem isValueAt_sum {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) z (v i)) : IsValueAt x (∑ i ∈ S, f i) z (∑ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x z
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ValRing.isValueAt_add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_valAt (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    IsValueAt x s z (valAt x s z) := by
  obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hz hs
  rw [valAt_eq hz hv]
  exact hv

theorem valAt_sum_mul (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (S : Finset α) (f g : α → Ω)
    (hf : ∀ i ∈ S, RegAt x (mCoordIdeal z) (f i)) (hg : ∀ i ∈ S, RegAt x (mCoordIdeal z) (g i)) :
    valAt x (∑ i ∈ S, f i * g i) z = ∑ i ∈ S, valAt x (f i) z * valAt x (g i) z :=
  valAt_eq hz (isValueAt_sum S _ _ fun i hi =>
    isValueAt_mul (isValueAt_valAt hz (hf i hi)) (isValueAt_valAt hz (hg i hi)))

end Values

theorem stepCols_ne {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
      omega
    rw [e] at hm
    simp at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
      omega
    rw [e] at hm
    simp at hm

theorem read_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (A : Finset (Fin N) → κ → ℂ) (B : κ → Finset (Fin N) → ℂ)
    (hAB : ∀ I I', P I → P I' → ∑ m, A I m * B m I' = if I = I' then 1 else 0)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hw : ∀ m, w m = a * ∑ I, B m I * μ I) (I' : Finset (Fin N)) (hI' : P I') :
    ∑ m, A I' m * w m = a * μ I' := by
  have e : ∑ m, A I' m * w m = a * ∑ I, (∑ m, A I' m * B m I) * μ I := by
    simp only [hw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.sum_eq_single I']
  · rw [hAB I' I' hI' hI', if_pos rfl, one_mul]
  · intro I _ hne
    by_cases hI : P I
    · rw [hAB I' I hI' hI, if_neg hne.symm, zero_mul]
    · rw [hμ I hI, mul_zero]
  · simp

theorem move_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (S : Finset (Finset (Fin N))) (hS : ∀ I, I ∈ S ↔ P I) (A : Finset (Fin N) → κ → ℂ)
    (D : Finset (Fin N) → ℂ) (Tm : Finset (Fin N) → Finset (Fin N) → ℂ)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hA : ∀ I', P I' → ∑ m, A I' m * w m = a * μ I') :
    ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m = a * ∑ I, D I * ∑ I', Tm I I' * μ I' := by
  have e : ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m =
      ∑ I, ∑ I' ∈ S, D I * Tm I I' * ∑ m, A I' m * w m := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ S) fun I' _ h => by
    rw [hμ I' fun hp => h ((hS I').2 hp), mul_zero], Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I' h => by rw [hA I' ((hS I').1 h)]; ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hE := fun m m' =>
    _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p ⟨k, m⟩ ⟨k', m'⟩
  have hmin := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul hzb Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base K' ι' Φ' y' Ψ N j M' z₁ _ hz₁ hzb (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind

theorem stepCols_nonempty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem coord_ne {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k}
    (hX : (X q : MRing ι) ∉ mCoordIdeal z) : x q ≠ 0 := by
  intro h
  apply hX
  have h1 : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 := hz.2 _ h1
  have h3 : z q = 0 := by simpa using h2
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h3, map_zero, zero_mul]

theorem valMat_blockDiag {N j : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A : Matrix (Fin N) (Fin N) Ω} (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x z A) := fun a b h => by
  show valAt x (A a b) z = 0
  rw [hA a b h]
  exact map_zero (regVal x hz)

theorem reg_chain {N : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A B C : Matrix (Fin N) (Fin N) Ω} (hB : B.det ≠ 0)
    (h₁ : ∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * B) a b)) (h₂ : ∀ a b, RegAt x (mCoordIdeal z) ((B⁻¹ * C) a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * C) a b)) ∧
      valMat x z (A⁻¹ * C) = valMat x z (A⁻¹ * B) * valMat x z (B⁻¹ * C) := by
  have e : A⁻¹ * C = (A⁻¹ * B) * (B⁻¹ * C) := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hB)]
  rw [e]
  exact regMat_mul hz h₁ h₂

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem minor_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g = minorIJ g I (stepCols N j p.2) := by
  have hi := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have hz : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ g I' (stepCols N j p.2) = 0 := fun I' h =>
    (hi.2.1 g I' hg h).resolve_right (stepCols_nonempty M.j_le p.2).ne_empty
  have hv : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := hF.2.2.1 p k hk I I' hI hI'
    have h2 := (reg_sum hb Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I') fun m _ =>
      ValRing.regAt_mul (hG.2.1 _ _).2 (hG.2.1 _ _).1).2
    rw [h1] at h2
    rw [Finset.sum_congr rfl fun m _ => (reg_mul hb (hG.2.1 _ _).2 (hG.2.1 _ _).1).2.symm, ← h2]
    split_ifs
    · exact map_one (regVal M.x hb)
    · exact map_zero (regVal M.x hb)
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g
      = ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b) *
          minorIJ g I' (stepCols N j p.2) := by
        simp only [plk, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ I', if I = I' then minorIJ g I' (stepCols N j p.2) else 0 := Finset.sum_congr rfl fun I' _ => by
        by_cases h : IsStepRows N j p.2 I'
        · rw [hv I' h]; split_ifs <;> simp
        · rw [hz I' h]; simp
    _ = minorIJ g I (stepCols N j p.2) := by simp

theorem minor_eq_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {g g₂ : Matrix (Fin N) (Fin N) ℂ} (hg : IsBlockDiag j g) (hg₂ : IsBlockDiag j g₂) {μ : ℂ}
    (h : ∀ m : ι k, plk M F b p.2 ⟨k, m⟩ g = μ * plk M F b p.2 ⟨k, m⟩ g₂) (I : Finset (Fin N)) :
    minorIJ g I (stepCols N j p.2) = μ * minorIJ g₂ I (stepCols N j p.2) := by
  by_cases hI : IsStepRows N j p.2 I
  · rw [← minor_of_plk M hb hF hG hk hI hg, ← minor_of_plk M hb hF hG hk hI hg₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h m]; ring
  · have hi := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
    have hne := (stepCols_nonempty M.j_le p.2).ne_empty
    rw [(hi.2.1 g I hg hI).resolve_right hne, (hi.2.1 g₂ I hg₂ hI).resolve_right hne, mul_zero]

end SlopeTestRemainingChoices

theorem plk_moved_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F₁' F₂' F₁ F₂ H₁ H₂ hb hF₁' hF₂' hF₁ hF₂ hG₁' hG₂' hG₁ hG₂
    hH₁ hH₂ hyp p k hk
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hk
  obtain ⟨hbv, hpt⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b hb
  have hi := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have dT₁' := (hF₁'.1 p.1).2
  have dP : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F → ((F.T p.1).map Cv.φ).det ≠ 0 := fun F hF => by
    have e : ((F.T p.1).map Cv.φ).det = Cv.φ (F.T p.1).det := (RingHom.map_det Cv.φ (F.T p.1)).symm
    rw [e]
    exact (map_ne_zero Cv.φ).2 (hF.1 p.1).2
  have r₁₁ := fun a c => Cv.agree b hb F₁' F₁ hF₁' hF₁ hG₁' hG₁ p.1 a c
  have r₁₂ := fun a c => Cv.agree b hb F₁' F₂ hF₁' hF₂ hG₁' hG₂ p.1 a c
  have r₂₁ := fun a c => Cv.agree b hb F₂' F₁ hF₂' hF₁ hG₂' hG₁ p.1 a c
  have r₂₂ := fun a c => Cv.agree b hb F₂' F₂ hF₂' hF₂ hG₂' hG₂ p.1 a c
  have c₁ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₁₁ a c).2) (fun a c => (r₂₁ a c).1)
  have c₂ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₂₁ a c).2) (fun a c => (r₁₁ a c).1)
  have c₃ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) (fun a c => (r₁₂ a c).2)
  have c₄ := reg_chain hb dT₁' (fun a c => (r₁₂ a c).1) (fun a c => (r₁₁ a c).2)
  have c₅ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) c₁.1
  have c₆ := reg_chain hb (dP F₂ hF₂) c₃.1 (fun a c => (r₂₂ a c).1)

  have eid : ∀ A : Matrix (Fin N) (Fin N) M'.Ω, A.map (RingHom.id M'.Ω) = A := fun A => by ext; rfl
  obtain ⟨c', hc'0, hc'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main K' ι' Φ' y' Ψ N j M' (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x
    (RingHom.id _) b F₁' F₂' hb hF₁' hF₂' (fun k => coord_ne hb (hG₁'.1 k)) (fun k => coord_ne hb (hG₂'.1 k)) p k' hk'
    (fun m I => ⟨(hG₁'.2.1 _ _).1, (hG₂'.2.1 _ _).1, (hG₁'.2.1 _ _).2, (hG₂'.2.1 _ _).2⟩)
    (fun a c => by simp only [eid]; exact ⟨c₁.1 a c, c₂.1 a c⟩)
  simp only [eid, RingHom.id_apply] at hc'
  obtain ⟨a, ha0, hA⟩ := hyp p k' hk'
  obtain ⟨S', hS'⟩ : ∃ S', S' = valMat M'.x b ((F₁'.T p.1)⁻¹ * F₂'.T p.1) := ⟨_, rfl⟩
  rw [← hS'] at hc'
  have bdS' : IsBlockDiag j S' := hS' ▸ valMat_blockDiag hb
    (((hF₁'.1 p.1).1.inv (isUnit_iff_ne_zero.2 dT₁')).mul (hF₂'.1 p.1).1)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = c' * a⁻¹ := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := hμd ▸ mul_ne_zero hc'0 (inv_ne_zero ha0)
  have e₁ : ∀ m : ι' k', plk M' F₁' b p.2 ⟨k', m⟩ (S' * H₂ p.1) = μ * plk M' F₁' b p.2 ⟨k', m⟩ (H₁ p.1) := fun m => by
    rw [hA m, hμd, ← mul_assoc, mul_assoc c', inv_mul_cancel₀ ha0, mul_one]
    exact hc' (H₂ p.1) (hH₂ p.1) m
  have e₂ := minor_eq_of_plk M' hb hF₁' hG₁' hk' (bdS'.mul (hH₂ p.1)) (hH₁ p.1) e₁

  obtain ⟨S, hS⟩ : ∃ S, S = valMat M'.x b (((F₁.T p.1).map Cv.φ)⁻¹ * (F₂.T p.1).map Cv.φ) := ⟨_, rfl⟩
  have eT : Cv.trans F₁' F₁ b p.1 * S' = S * Cv.trans F₂' F₂ b p.1 := by
    rw [hS', hS]
    exact c₅.2.symm.trans c₆.2
  have e₃ : ∀ I, minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2) =
      μ⁻¹ * minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := fun I => by
    rw [← Matrix.mul_assoc S, ← eT, Matrix.mul_assoc, hi.1 _ (S' * H₂ p.1), hi.1 _ (H₁ p.1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [e₂ I']
    field_simp

  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main K ι Φ y Ψ N j M (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x Cv.φ b F₁ F₂
    hb hF₁ hF₂ (fun k => coord_ne hbv (hG₁.1 k)) (fun k => coord_ne hbv (hG₂.1 k)) p k hk
    (fun m I => ⟨(hpt _ (hG₁.2.1 _ _).1).1, (hpt _ (hG₂.2.1 _ _).1).1, (hpt _ (hG₁.2.1 _ _).2).1,
      (hpt _ (hG₂.2.1 _ _).2).1⟩)
    (fun a c => ⟨c₃.1 a c, c₄.1 a c⟩)
  rw [← hS] at hc
  have bdT₂ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b F₂' F₂ hb hF₂' hF₂ hG₂' hG₂ p.1).1
  have hval : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ q I,
      valAt M'.x (Cv.φ (F.u q I)) b = valAt M.x (F.u q I) (b ∘ Cv.v) := fun F hG q I => (hpt _ (hG.2.1 q I).1).2
  refine ⟨μ⁻¹ * c, mul_ne_zero (inv_ne_zero hμ) hc0, fun m => ?_⟩
  have h3 := hc (Cv.trans F₂' F₂ b p.1 * H₂ p.1) (bdT₂.mul (hH₂ p.1)) m
  simp only [hval F₁ hG₁, hval F₂ hG₂] at h3
  simp only [plk]
  calc ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2)
      = μ⁻¹ * ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by rw [e₃ I]; ring
    _ = _ := by rw [h3, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversalStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_pos_of_semidefinite_transversal : ∀ (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ) (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ), Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U)) → (∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) → 0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos <;> assumption)
end

