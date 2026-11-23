module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)

section

variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}

theorem sheetDensity_neg (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs <;> simp [neg_mul]

theorem sheetDensity_congr {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hs : IsSheet P Ψ y w hγ.choose := hγ.choose_spec
    rw [h _ hs.2.self_of_nhds.2.1]
  · rfl

end

theorem PtsIntegralProjIndep.proof (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hL hg
  classical
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hSdef
  set g₀ : ((Σ k, ι k) → ℂ) → ℝ := S.piecewise g 0 with hg₀def
  have hg₀m : Measurable g₀ :=
    hg.1.continuousOn.measurable_piecewise continuousOn_const isOpen_blockNonzero.measurableSet
  have hg₀inv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      g₀ (fun p => c p.1 * z p) = g₀ z := by
    intro c z hc
    have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ S ↔ z ∈ S := by
      simp only [hSdef, Set.mem_ofPred_eq, ne_eq, mul_eq_zero, hc, false_or]
    by_cases hz : z ∈ S
    · rw [hg₀def, Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ (hmem.2 hz), hg.2 c z hc]
    · rw [hg₀def, Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ (mt hmem.1 hz)]
      rfl
  have hag : ∀ z ∈ mcPts P, g z = g₀ z := fun z hz =>
    (Set.piecewise_eq_of_mem S _ _ (show z ∈ S from hz.1)).symm
  have hagn : ∀ z ∈ mcPts P, -g z = -g₀ z := fun z hz => by rw [hag z hz]
  have hneg : IsDegZeroSmooth (fun z => -g z) :=
    ⟨hg.1.neg, fun c z hc => by simp only [hg.2 c z hc]⟩
  have hnn : ∀ (Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (u : ((Σ k, ι k) → ℂ) → ℝ) y,
      0 ≤ ptsPosDens P Ψ₀ (pot L) u y := fun Ψ₀ u y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _

  have key : ∀ Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ₀ →
      ptsIntegralAt P Ψ₀ (pot L) g =
        (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) g₀ y)).toReal -
          (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) y)).toReal := by
    intro Ψ₀ h₀
    have hp := hInt K ι P e Ψ₀ L g hP h₀ hL hg
    have hn := hInt K ι P e Ψ₀ L (fun z => -g z) hP h₀ hL hneg
    have e₁ : ptsPosDens P Ψ₀ (pot L) g₀ = ptsPosDens P Ψ₀ (pot L) g := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hag]
    have e₂ : ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) = ptsPosDens P Ψ₀ (pot L) (fun z => -g z) := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hagn]
    have hsplit : ∀ y, (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ₀ y, sheetDensity P Ψ₀ (pot L) g y w) =
        ptsPosDens P Ψ₀ (pot L) g y - ptsPosDens P Ψ₀ (pot L) (fun z => -g z) y := by
      intro y
      have hF := fibreFinite K ι P e Ψ₀ hP h₀ y
      simp only [ptsPosDens, finsum_mem_eq_finite_toFinset_sum _ hF, sheetDensity_neg,
        ← Finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
    unfold ptsIntegralAt
    simp only [hsplit]
    rw [integral_sub hp hn, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ g)) hp.1,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ _)) hn.1, e₁, e₂]
  rw [key Ψ hΨ, key Ψ' hΨ', hPos K ι P e Ψ Ψ' L g₀ hP hΨ hΨ' hL hg₀m hg₀inv,
    hPos K ι P e Ψ Ψ' L (fun z => -g₀ z) hP hΨ hΨ' hL hg₀m.neg fun c z hc => by simp only [hg₀inv c z hc]]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

theorem ptsPosDens_split {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem PtsPosPartProjIndep.proof (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧
    IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Q z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [ptsPosDens, sheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Q z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' →
      (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) →
        IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : IsSimpleSheetPt P B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B →
      (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem PtsSheetSimpleNull.simple_of_count {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y').encard ≤ d) (hy : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by
  have hF : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
      (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y' = (fun a => segre (γ a y')) '' ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y ⊆ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

theorem PtsSheetSimpleNull.proof (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace SegreChartZeroSet

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scaleAll_mem (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by
  have key : ∀ s : Finset K,
      (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert k s hk ih =>
      have h := scaleBlock_mem_zeroLocus P hP k (hc k) ih
      convert h using 1
      funext ⟨j, a⟩
      by_cases hpk : j = k
      · subst j
        simp [scaleBlock, hk]
      · simp [scaleBlock, hpk]
  simpa using key Finset.univ

def liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (f : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  eval₂ (algebraMap ℤ (MvPolynomial (Fin m) ℂ)) (fun p => X (σ.symm (Function.update i p.1 p.2))) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by
  rw [liftPoly, hom_eval₂, eval_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp [chartLift]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P m σ i hP
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0 :=
      fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      rw [← eval_liftPoly]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPoly]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

end SegreChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)
open ComplexSets

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def projChartSet (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def projChartIdeal (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (projChartSet P σ Ψ)

end Chart

def GoodChartModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ ∧
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSheetLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet PBlk)

def SheetLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ),
    IsMultiHomogIdeal P →
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ mcPts P, segre z = h y') ∧ Ψ (h y') = Fin.cons 1 y') →
      ∃ γ, IsSheet P Ψ y (h y) γ

end GroundTheory.Heights₂.Heights
end
end

