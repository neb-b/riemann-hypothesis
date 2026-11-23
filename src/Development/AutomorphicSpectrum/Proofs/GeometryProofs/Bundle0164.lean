module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeComposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DegComp

theorem det_ne_zero_of_injective {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hπ : HoloMap B A π)
    (hinj : Function.Injective π) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : π ((B.chart j).symm y) ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hπ.1)
  have hI : Set.InjOn (A.chart k ∘ π ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) := by
    intro a ha b hb hab
    exact (B.chart j).symm.injOn ha.1 hb.1 (hinj ((A.chart k).injOn ha.2 hb.2 hab))
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn e _ (A.chart k ∘ π ∘ (B.chart j).symm) hU
    (fun w hw => (hπ.2 j k w hw).differentiableAt.differentiableWithinAt) hI y ⟨hy, hk⟩
  intro h0
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero h0
  have hker : LinearMap.ker (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  rw [hker] at hlt
  exact lt_irrefl _ hlt

theorem isDegreeOff_one_of_bijective {e : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X}
    (hπ : HoloMap B A π) (hbij : Function.Bijective π) : IsDegreeOff A B π 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · simpa using isAnalyticSubset_empty B
  · simp
  · intro x _
    obtain ⟨y, rfl⟩ := hbij.2 x
    have hfib : π ⁻¹' {π y} = {y} := by
      ext z
      simp [hbij.1.eq_iff]
    rw [hfib, Set.ncard_singleton]
  · intro j k y hy _ hk
    exact det_ne_zero_of_injective hπ hbij.1 j k hy hk

theorem holoMap_comp_isDegreeOff : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  intro e d X Y Z _ _ _ _ _ _ A B C π h br hπ hbij hh hd
  obtain ⟨g, hgl, hgr, hg⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one A B π hπ
    (isDegreeOff_one_of_bijective hπ hbij)
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, ?_⟩
  obtain ⟨han, hint, hpan, hpint, hfib, hdet⟩ := hd
  have hpre : (π ∘ h) ⁻¹' (π '' br) = h ⁻¹' br := by
    ext z
    simp [hbij.1.mem_set_image]
  have himg : π '' br = g ⁻¹' br := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hgl] using hy
    · intro hx
      exact ⟨g x, hx, hgr x⟩
  let E : Y ≃ₜ X :=
    { toFun := π, invFun := g, left_inv := hgl, right_inv := hgr,
      continuous_toFun := hπ.1, continuous_invFun := hg.1 }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    intro x
    obtain ⟨W, hW, hxW, r, f, hf, hS⟩ := han (g x)
    refine ⟨g ⁻¹' W, hW.preimage hg.1, hxW, r, fun i => f i ∘ g,
      fun i => GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_comp hg (hf i), ?_⟩
    ext y
    simpa using Set.ext_iff.1 hS (g y)
  · change interior (E '' br) = ∅
    rw [← E.image_interior, hint, Set.image_empty]
  · rw [hpre]
    exact hpan
  · rw [hpre]
    exact hpint
  · intro x hx
    have hgx : g x ∉ br := fun hb => hx ⟨g x, hb, hgr x⟩
    have hset : (π ∘ h) ⁻¹' {x} = h ⁻¹' {g x} := by
      ext z
      constructor
      · intro hz
        have hz' : π (h z) = x := hz
        change h z = g x
        rw [← hz', hgl]
      · intro hz
        have hz' : h z = g x := hz
        change π (h z) = x
        rw [hz', hgr]
    rw [hset]
    exact hfib _ hgx
  · intro j k y hy hnot hk
    have hnot' : (C.chart j).symm y ∉ h ⁻¹' br := by rwa [hpre] at hnot
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp]
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact det_ne_zero_of_injective hπ hbij.1 l k hQt hk'
    · rw [hQdef]
      exact hdet j l y hy hnot' hl

end GlobalTheory.CompanionTheory.Ar.DegComp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.UnifDim

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem eq_of_linear_lift {M : Type*} [Group M] {g d : ℕ} (e : (Fin g → ℂ) → M)
    (e' : (Fin d → ℂ) → M) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hon : Function.Surjective e) (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin d → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hk' : ∀ z, e' z = 1 ↔ z ∈ Λ')
    [DiscreteTopology Λ] [DiscreteTopology Λ']
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (hF : ∀ z, e' (F z) = e z) : g = d := by
  have hinj := AnyUnif.injective_of_ker_le_discrete Λ F fun z hz => by
    rw [← hk, ← hF, hz]
    exact (hk' 0).2 Λ'.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete Λ' _ fun w => by
    obtain ⟨z, hz⟩ := hon (e' w)
    refine ⟨⟨w - F z, (hk' _).1 ?_⟩, z, by simp⟩
    have h := he' (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem holOn_ex (u : HolUnif A L g) : HolOn Set.univ u.ex := fun U f => by
  simpa only [Set.mem_univ, true_and] using u.hol U f

theorem compactSpace_points (u : HolUnif A L g) : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have hc : Continuous u.ex :=
    continuous_iff_continuousAt.2 fun z => (holOn_ex u).continuousAt (Set.mem_univ z)
  haveI := u.discrete
  haveI := holUnif_isZLattice u
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (ZSpan.fundamentalDomain_isBounded b).closure
  refine isCompact_univ_iff.1 ((hK.image hc).of_isClosed_subset isClosed_univ fun x _ => ?_)
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
  have hm : ((ZSpan.floor b z : _) : Fin g → ℂ) ∈ u.Λ := by
    have e := Module.Basis.ofZLatticeBasis_span ℝ u.Λ (Module.Free.chooseBasis ℤ u.Λ)
    exact e.le (ZSpan.floor b z).2
  have h := u.ex_add (ZSpan.fract b z) (ZSpan.floor b z)
  rw [(u.ker _).2 hm, _root_.mul_one, ZSpan.fract_apply, sub_add_cancel] at h
  rw [ZSpan.fract_apply]
  exact h.symm

theorem eq_relativeDimension : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ)
    (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  intro A _ L g d u hd
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := htop A
  have := compactSpace_points u
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A d hd 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin d → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => by
    obtain ⟨z, hz⟩ := u.ex_onto x.toMul
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine ⟨Additive.ofMul (u.ex ((n : ℂ)⁻¹ • z)), ?_⟩
    have h1 : n • ((n : ℂ)⁻¹ • z) = z := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    have h2 := holUnif_ex_nsmul_eq_pow u ((n : ℂ)⁻¹ • z) n
    rw [h1, hz] at h2
    rw [← ofMul_pow, ← h2]
    rfl
  have hu := holOn_ex u
  have hu0 : u.ex 0 = 1 := holUnif_ex_zero_eq_one u
  have h1 : φ (u.ex 0) = 0 := by rw [hu0]; exact hφ.map_zero
  have h2 : AnalyticAt ℂ (fun w => φ (u.ex w)) 0 :=
    hu.analyticAt t (Set.mem_univ _) (hu0 ▸ hU1)
  have hG0 : hφ.log (φ (u.ex 0)) = 0 := by
    simp only [h1]
    exact hφ.isLocalCommGroupLaw.log_zero
  have hGa : AnalyticAt ℂ (fun w => hφ.log (φ (u.ex w))) 0 :=
    AnalyticAt.comp (g := hφ.log) (h1 ▸ hφ.isLocalCommGroupLaw.analyticAt_log) h2
  have hGe : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (hφ.exp (hφ.log (φ (u.ex w)))).toMul = u.ex w := by
    have h3 : Tendsto u.ex (𝓝 0) (𝓝 1) := hu0 ▸ (hu.continuousAt (Set.mem_univ 0)).tendsto
    exact h3.eventually hφ.exp_log
  have hF := EndoLinear.fderiv_lifts (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) hφ.periodLattice (fun z => Iff.rfl)
    inferInstance u.ex u.ex_add _ hG0 hGa.differentiableAt hGe
  haveI := u.discrete
  exact eq_of_linear_lift u.ex (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) u.ex_onto u.Λ hφ.periodLattice u.ker
    (fun z => Iff.rfl) (fderiv ℂ (fun w => hφ.log (φ (u.ex w))) 0).toLinearMap hF

end GlobalTheory.CompanionTheory.Ar.UnifDim
end

