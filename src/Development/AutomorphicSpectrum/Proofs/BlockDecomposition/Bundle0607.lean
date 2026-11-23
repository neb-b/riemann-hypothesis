module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelfDualVol
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.GunrVol

theorem selfDualVol : PositivityTheory.SiegelWeilFormula.Gunr.SelfDualVol := by
  intro V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann
  obtain ⟨hH, hinv⟩ := hsd
  haveI := hH
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hfin : μ (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpos : μ (L : Set V) ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1 := ⟨_, rfl⟩
  have hΦin : ∀ x ∈ L, Φ x = 1 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_mem (s := (L : Set V)) hx _
  have hΦout : ∀ x, x ∉ L → Φ x = 0 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_notMem (s := (L : Set V)) hx _
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_one.indicator (by
      intro a ha
      rw [(IsClopen.frontier_eq ⟨hLcl, hLo⟩)] at ha
      exact absurd ha (Set.notMem_empty a))
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc ?_
    intro x hx
    exact hΦout x hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V) := ⟨_, rfl⟩
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y := by
    intro y
    by_cases hy : y ∈ L
    · have h1 : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hann y).2 hy x hx, mul_one]
        · rw [hΦout x hx, zero_mul]
      rw [h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]
      simp [hm]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy]
      have h2 := (hann y).not.2 hy
      push_neg at h2
      obtain ⟨x0, hx0, hne⟩ := h2
      have h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := by
        calc ∫ x, Φ x * χ x y ∂μ = ∫ x, (fun x => Φ x * χ x y) (x0 + x) ∂μ :=
              (integral_add_left_eq_self _ x0).symm
          _ = ∫ x, χ x0 y * (Φ x * χ x y) ∂μ := by
              congr 1
              funext x
              have : Φ (x0 + x) = Φ x := by
                by_cases hx : x ∈ L
                · rw [hΦin _ (L.add_mem hx0 hx), hΦin _ hx]
                · rw [hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]
              simp only [this, hadd]
              ring
          _ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _
      have h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [funext hI]
    exact (integrable_indicator_iff hLm).2 (integrableOn_const hfin)
  have h0 := hinv Φ hΦc hΦs hInt 0
  have hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ)) := by
    funext y
    rw [hI]
    by_cases hy : y ∈ L
    · rw [(hann 0).2 L.zero_mem y hy, mul_one]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]
  rw [hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem] at h0
  have h5 : (m : ℂ) * m = 1 := by
    have := h0
    simp only [setIntegral_const, ← hm, Complex.real_smul] at this
    exact this
  have h6 : m * m = 1 := by exact_mod_cast h5
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  have h7 : m = 1 := by nlinarith
  rw [hm, measureReal_def, ENNReal.toReal_eq_one_iff] at h7
  exact h7

end GlobalTheory.CompanionTheory.GunrVol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIntegralProjectionFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem sameOrbit_of_segre_eq {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {z z' : (Σ k, κ k) → ℂ} (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) (h : segre z = segre z') :
    SameOrbit z z' := by
  classical
  choose a ha using hz
  have hs : ∀ b : ∀ k, κ k, ∏ k, z ⟨k, b k⟩ = ∏ k, z' ⟨k, b k⟩ := fun b => congrFun h b
  have hpa : ∏ k, z ⟨k, a k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha k
  have ha' : ∀ k, z' ⟨k, a k⟩ ≠ 0 := fun k => by
    have h' : ∏ k, z' ⟨k, a k⟩ ≠ 0 := hs a ▸ hpa
    exact Finset.prod_ne_zero_iff.1 h' k (Finset.mem_univ _)
  refine ⟨fun k => z ⟨k, a k⟩ / z' ⟨k, a k⟩, fun k => div_ne_zero (ha k) (ha' k), ?_⟩
  funext p
  rcases p with ⟨k, j⟩
  show z ⟨k, j⟩ = z ⟨k, a k⟩ / z' ⟨k, a k⟩ * z' ⟨k, j⟩
  have split : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, Function.update a k j l⟩ =
      w ⟨k, j⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have split0 : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, a l⟩ =
      w ⟨k, a k⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := fun w =>
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
  have e1 := hs (Function.update a k j)
  rw [split z, split z'] at e1
  have e2 := hs a
  rw [split0 z, split0 z'] at e2
  have hP : ∏ l ∈ Finset.univ.erase k, z ⟨l, a l⟩ ≠ 0 := by
    rw [split0 z] at hpa
    exact right_ne_zero_of_mul hpa
  rw [div_mul_eq_mul_div, eq_div_iff (ha' k)]
  apply mul_right_cancel₀ hP
  linear_combination z' ⟨k, a k⟩ * e1 - z' ⟨k, j⟩ * e2

theorem finsum_fibre_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n)
    [IsClosedImmersion i] (D : ℕ) (Ψ : LinProj n D) (N : Pol n)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1))
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) {ι : Type}
    (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀))
    (hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l)) (hS : ∀ l, S l ⊆ (e l).source)
    (hd : Pairwise (Function.onFun Disjoint S)) (v : Fin D → ℂ)
    (hcov : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, Over i y z ∧ y ∈ ⋃ l, S l)
    (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ)
    (hT : ∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) :
    ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w =
      ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  classical
  set P := ptIdeal (i (genericPoint X)) with hPdef
  let Lv : Set ι := {l | v ∈ (e l) '' S l}
  let f : ι → (((k : Fin (m + 1)) → Bk n k) → ℂ) := fun l => segre (Γ l v)
  have hy : ∀ l ∈ Lv, (e l).symm v ∈ S l ∧ v ∈ (e l).target := by
    rintro l ⟨y, hyS, rfl⟩
    exact ⟨by rw [(e l).left_inv (hS l hyS)]; exact hyS, (e l).map_source (hS l hyS)⟩
  have hpc' : ∀ l ∈ Lv, Over i ((e l).symm v) (Γ l v) ∧ Γ l v ∈ mcPts P ∧
      Ψ (segre (Γ l v)) = Fin.cons 1 v := by
    intro l hl
    obtain ⟨_, _, hp⟩ := hpc l
    obtain ⟨h1, h2, h3, -⟩ := hp v (hy l hl).2
    exact ⟨h1, h2, h3⟩
  have himg : fibre P Ψ v = f '' Lv := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hzv⟩
      obtain ⟨y, hyz, hyS⟩ := hcov z hz hzv
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hyS
      have hys := hS l hl
      have hvt : (e l) y ∈ (e l).target := (e l).map_source hys
      obtain ⟨_, _, hp⟩ := hpc l
      obtain ⟨o1, o2, o3, -⟩ := hp ((e l) y) hvt
      rw [(e l).left_inv hys] at o1
      have hso : SameOrbit z (Γ l ((e l) y)) :=
        (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i y y z _ hyz o1).1 rfl
      have hvv : v = (e l) y := by
        have r1 := ratios_of_proj Ψ hzv
        have r2 := ratios_of_proj Ψ o3
        have r3 := ratios_eq_of_sameOrbit Ψ hso (by rw [o3]; simp)
        rw [← r1, r3, r2]
      refine ⟨l, ⟨y, hl, hvv.symm⟩, ?_⟩
      show segre (Γ l v) = segre z
      rw [hvv]
      obtain ⟨c, hc, hzc⟩ := hso
      have hseg := segre_orbit hzc
      have h1 : (∏ k, c k) = 1 := by
        have h0 := congrArg (fun u => u 0) (congrArg Ψ hseg)
        simp only [map_smul, hzv, o3, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
        exact h0.symm
      rw [hseg, h1, one_smul]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨_, h2, h3⟩ := hpc' l hl
      exact ⟨Γ l v, h2, rfl, h3⟩
  have hinj : Set.InjOn f Lv := by
    intro l hl l' hl' hll
    obtain ⟨o1, o2, -⟩ := hpc' l hl
    obtain ⟨o1', -, -⟩ := hpc' l' hl'
    have hso := sameOrbit_of_segre_eq o2.1 hll
    have hyy := (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i _ _ _ _ o1 o1').2 hso
    by_contra hne
    exact Set.disjoint_left.1 (hd hne) (hy l hl).1 (by rw [hyy]; exact (hy l' hl').1)
  have hfin : (fibre P Ψ v).Finite := ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite _ _ _ _ Ψ hP hΨ v
  have hLfin : Lv.Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj
  rw [himg, finsum_mem_image hinj]
  have hind : ∀ l, ((e l) '' S l).indicator (fun _ => T l) v = Lv.indicator T l := by
    intro l
    by_cases hl : l ∈ Lv
    · have hl' : v ∈ (e l) '' S l := hl
      simp [hl, hl']
    · have hl' : v ∉ (e l) '' S l := hl
      simp [hl, hl']
  simp_rw [hind]
  rw [tsum_eq_finsum (hLfin.subset Set.support_indicator_subset), ← finsum_mem_def]
  exact finsum_mem_congr rfl fun l hl => hT l hl

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength _root_.GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches _root_.GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength

end GlobalTheory.CompanionTheory.Heights.BranchOrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SquareIntegrableSegments

theorem length_le_one_of_partial_products {h : ℕ} (d e f : Fin h → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : ∀ i, 0 < d i) (he : Antitone e) (hf : ∀ i, f i = q ^ (d i * e i))
    (hpart : ∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), f (Fin.rev i) < 1)
    (hfull : ∏ i, f (Fin.rev i) = 1) : h ≤ 1 := by
  by_contra hh
  have h2 : 2 ≤ h := by omega
  have hlog : Real.log q ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hprod : ∀ s : Finset (Fin h), ∏ i ∈ s, f i = q ^ (∑ i ∈ s, d i * e i) := fun s => by
    rw [Real.rpow_sum_of_pos hq0]
    exact Finset.prod_congr rfl fun i _ => hf i
  have htot : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, f i = 1 := by
      rw [← hfull]
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [hprod] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_one] at h3
    exact (mul_eq_zero.1 h3).resolve_right hlog
  obtain ⟨j, hj0, hj⟩ := GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos h d e h2 hd he htot
  have hlt := hpart (Fin.rev j) (by have := j.isLt; rw [Fin.val_rev]; omega)
  have hrw := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h f (Fin.rev j)
  rw [Fin.rev_rev] at hrw
  rw [hrw, hprod] at hlt
  exact absurd hlt (not_lt.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1.le hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isLSeg {Δ : Segment k} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  rw [← hd, Segment.sum_term_fst]

theorem sum_deg_of_listing {h : ℕ} {D : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (hD : Finset.univ.val.map D = 𝔪) : ∑ i, (D i).deg = (𝔪.map Segment.deg).sum := by
  rw [← hD, Multiset.map_map]
  rfl

theorem exists_class (hE : Zc.LSegExists k) (Δ : Segment k) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨π, hd, hc⟩ := hE Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hd,
    hc.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (Representation.Equiv.refl _)⟩

theorem card_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type}
      [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible →
        IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  intro k _ _ _ _ hS hC hE 𝔪 N V _ _ π hN hsm hirr hsq hL
  choose y hy using exists_class hE
  have hdeg : ∀ Δ, (y Δ).1 = Δ.deg := fun Δ => (deg_eq_of_isLSeg (hy Δ)).symm
  have hpos : ∀ Δ, 0 < (y Δ).1 := fun Δ => by
    rw [hdeg]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  choose s hs using fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hpos Δ)
  obtain ⟨h, D, hD, hanti, hno⟩ := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing 𝔪 s Segment.Precedes
    fun a b hab => GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (s a) (s b) (hy a) (hy b) (hs a) (hs b) hab
  let x : Fin h → IrrGL (k := k) := fun i => y (D i)
  have hLF : LFactors 𝔪 x := ⟨D, ⟨hD, hno⟩, fun i => hy (D i)⟩
  have hsum : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨D', ⟨hD', -⟩, hx'⟩, -⟩ := hL
    rw [← hd']
    have e1 : ∑ a, (x a).1 = ∑ a, (D a).deg := Finset.sum_congr rfl fun a _ => hdeg (D a)
    have e2 : ∑ a, (x' a).1 = ∑ a, (D' a).deg :=
      Finset.sum_congr rfl fun a _ => (deg_eq_of_isLSeg (hx' a)).symm
    rw [e1, e2, sum_deg_of_listing hD, sum_deg_of_listing hD']
  have hsumrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hsum]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hsoc := hS 𝔪 h N x hsumrev hLF π hL
  have hposrev : ∀ a, 0 < ((x ∘ Fin.rev) a).1 := fun a => hpos _
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hsumrev π hsm hposrev hsoc
  have hex := hC N π hN hsm hirr hsq h (x ∘ Fin.rev) hsumrev hposrev hjm
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero k
  have hnabs := _root_.GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  choose c hc using fun i => GlobalTheory.T.central_character_exists k (x i) t
  obtain ⟨hpart, hfull⟩ := hex t ht (c ∘ Fin.rev) fun i => hc (Fin.rev i)
  have hle : h ≤ 1 := length_le_one_of_partial_products (fun i => ((x i).1 : ℝ)) (fun i => s (D i))
    (fun i => ‖c i‖) (nabs_pos' k t) hnabs (fun i => by exact_mod_cast hpos (D i)) hanti
    (fun i => hs (D i) t (c i) (hc i)) hpart hfull
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hcard : 𝔪.card = h := by
    rw [← hD]
    simp
  omega

end GlobalTheory.CompanionTheory.SquareIntegrableSegments
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_splitting_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (ι : HA (AF F) σ J →* stabilizer₂ (AF F) σ J) (π : stabilizer₂ (AF F) σ J →* HA (AF F) σ J), Continuous ι ∧ Continuous π ∧ (∀ u, π (ι u) = u) ∧ (∀ u ∈ HFinIn (AF F) σ J, ι u ∈ ratP (AF F) σ J) ∧ (∀ p ∈ ratP (AF F) σ J, π p ∈ HFinIn (AF F) σ J) ∧ (∃ K : Set (stabilizer₂ (AF F) σ J), IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ ratP (AF F) σ J, π γ = 1 ∧ γ * m ∈ K) ∧ (∀ (k : ℕ) (u : HA (AF F) σ J) (a : Fin 1 → Fin k → AF F ⊗[F] E) (Y : Fin k → Fin M → AF F ⊗[F] E), actW (AF F) σ (hypOne J) (ι u : HA (AF F) σ (hypOne J)) (consA a Y) = consA a (actW (AF F) σ J u Y)) ∧ ∀ (k : ℕ) (Y : Fin k → Fin M → E), LinearIndependent E Y → ∃ l : π.ker → Fin 1 → Fin k → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) k) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin k → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y)) = consA (a + l m) (ratTup (AF F) Y) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isCompact_setOf_toL_mem {K : Set (Lie E a)} (hK : IsCompact K) (hs : K ⊆ invSet E a) :
    IsCompact {y : GL (Fin a) (Cinf E) | toL y.val ∈ K} := by
  rw [(GlobalTheory.CuspQuot.isOpenEmbedding_val (E := E) (a := a)).isInducing.isCompact_iff]
  have himg : (Units.val '' {y : GL (Fin a) (Cinf E) | toL y.val ∈ K}) = Matrix.of '' K := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨toL y.val, hy, by ext i j; rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, hu⟩ := hs hx
      refine ⟨u, ?_, hu⟩
      change toL u.val ∈ K
      rw [hu]
      simpa [toL] using hx
  rw [himg]
  exact hK.image (continuous_id : Continuous (fun x : Lie E a => x))

theorem continuous_ker {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) : Continuous (ker U β) := by
  have hpf := GlobalTheory.CuspRep.ContAut.continuous_map_pFin E a
  have hpi := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E a
  have hclopen : IsClopen {v : GA E a | GeneralLinearGroup.map (pFin E) v ∈ U} :=
    (IsClopen.preimage ⟨U.isClosed_of_isOpen hU, hU⟩ hpf)
  have hval : Continuous fun v : GA E a => β (toL (GeneralLinearGroup.map (pInf E) v).val) :=
    hβ.contDiff.continuous.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp hpi)
  classical
  unfold ker
  refine Continuous.if (fun v hv => ?_) hval continuous_const
  rw [hclopen.frontier_eq] at hv
  exact absurd hv (Set.notMem_empty _)

theorem hasCompactSupport_ker {U : Subgroup (GL (Fin a) (Af E))}
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) :
    HasCompactSupport (ker U β) := by
  have hT := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  refine HasCompactSupport.intro (K := (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      infGL E a p.1 * finGL E a p.2) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ tsupport β} ×ˢ
        (U : Set (GL (Fin a) (Af E)))))
    ((hT.prod hUc).image ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd))) fun g hg => ?_
  by_contra h0
  unfold ker at h0
  split_ifs at h0 with hu
  · exact hg ⟨(_, _), ⟨subset_tsupport _ h0, hu⟩, infGL_mul_finGL g⟩
  · exact h0 rfl

theorem continuous_hasCompactSupport_tst : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β →
    Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  intro E _ _ _ a U hU hUc β hβ
  exact ⟨(continuous_ker hU hβ).comp continuous_inv,
    (hasCompactSupport_ker hUc hβ).comp_homeomorph (Homeomorph.inv (GA E a))⟩

end GlobalTheory.CompanionTheory.SmoothRep
end
end

