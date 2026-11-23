module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0114
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppFinTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atH (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

abbrev thW (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev dW (w : Pl E) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w δ₁, locEl b w δ₂)

abbrev dG (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : Gf E a b := (ratF E a δ₁, ratF E b δ₂)

abbrev KK (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Subgroup (Gf E a b) := (Kf E a).prod (Kf E b)


theorem mem_KK_iff (g : Gf E a b) : g ∈ KK E a b ↔ ∀ u : Pl E, atH a b u g ∈ K2 a b u := by
  simp only [KK, Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h u => ⟨h.1 u, h.2 u⟩, fun h => ⟨fun u => (h u).1, fun u => (h u).2⟩⟩

theorem ext_atH {g h : Gf E a b} (H : ∀ u : Pl E, atH a b u g = atH a b u h) : g = h :=
  Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.fst (H u))
    (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.snd (H u))

theorem ae_mem_GL {n : ℕ} (x : GL (Fin n) (Af E)) :
    ∀ᶠ w in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem ae_mem (g : Gf E a b) : ∀ᶠ u in cofinite, atH a b u g ∈ K2 a b u := by
  filter_upwards [ae_mem_GL g.1, ae_mem_GL g.2] with u h1 h2
  exact ⟨h1, h2⟩

theorem exists_GL_of_family {n : ℕ} (z : ∀ u : Pl E, GLw n u) (hz : ∀ᶠ u in cofinite, z u ∈ GlobalTheory.LFun.KGL u (n := n)) :
    ∃ g : GL (Fin n) (Af E), ∀ u, GeneralLinearGroup.map (pLoc E u) g = z u := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (z w).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((z w)⁻¹).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E),
      (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
    Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun u => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem exists_of_family (z : ∀ u : Pl E, GLw a u × GLw b u) (hz : ∀ᶠ u in cofinite, z u ∈ K2 a b u) :
    ∃ g : Gf E a b, ∀ u, atH a b u g = z u := by
  obtain ⟨g₁, h₁⟩ := exists_GL_of_family (fun u => (z u).1) (hz.mono fun u h => h.1)
  obtain ⟨g₂, h₂⟩ := exists_GL_of_family (fun u => (z u).2) (hz.mono fun u h => h.2)
  exact ⟨(g₁, g₂), fun u => Prod.ext (h₁ u) (h₂ u)⟩

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTw.Comm.thF_thF y.1) (GlobalTheory.EulerTw.Comm.thF_thF y.2)

theorem atH_thP_congr {u v : Pl E} (huv : GlobalTheory.EulerTw.cPl E u = v) {g h : Gf E a b}
    (H : atH a b v g = atH a b v h) : atH a b u (thP E a b g) = atH a b u (thP E a b h) := by
  subst huv
  refine Prod.ext ?_ ?_
  · change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) = GeneralLinearGroup.map (pLoc E u) (thF E a h.1)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.fst H)
  · change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) = GeneralLinearGroup.map (pLoc E u) (thF E b h.2)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.snd H)

theorem integral_of_twist_conjugate_place (u : Pl E) {g : Gf E a b} (H : atH a b u (thP E a b g) ∈ K2 a b u) :
    atH a b (GlobalTheory.EulerTw.cPl E u) g ∈ K2 a b (GlobalTheory.EulerTw.cPl E u) := by
  refine ⟨GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_, GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_⟩
  · have := H.1
    change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this
  · have := H.2
    change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this

theorem map_thF_of_not_split {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (thF E n g) = thL n w (GeneralLinearGroup.map (pLoc E w) g) := by
  rw [GlobalTheory.EulerTw.IntRead.map_thF]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (cj w) (GeneralLinearGroup.map (pLoc E w) g) i j
  have e : thL n w = thetaGL n (cj w) := if_neg hw
  rw [e, h2, GlobalTheory.EulerTw.IntRead.thAt_apply, GlobalTheory.EulerTwRestr.loc_inv_val, GlobalTheory.EulerTwRestr.loc_inv_val]
  congr 1
  exact GlobLev.conjLoc_eq_cj hw _

theorem usage₇ {w : Pl E} (hw : ¬ IsSplitAt w) (g : Gf E a b) :
    atH a b w (thP E a b g) = thW a b w (atH a b w g) :=
  Prod.ext (map_thF_of_not_split hw g.1) (map_thF_of_not_split hw g.2)

theorem thW_of_split {w : Pl E} (hw : IsSplitAt w) (y : GLw a w × GLw b w) : thW a b w y = y := by
  simp [thL, hw]

theorem atH_dG_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_neg hw]; rfl
  · simp only [locEl, if_neg hw]; rfl

theorem atH_norm_of_split {w : Pl E} (hw : IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂ * thP E a b (dG δ₁ δ₂)) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E a δ₁ * thF E a (ratF E a δ₁)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E b δ₂ * thF E b (ratF E b δ₂)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl

theorem mem_or_conj {S : Set (Pl E)} (hS : IsSection S) (u : Pl E) : u ∈ S ∨ ∃ v ∈ S, u = GlobalTheory.EulerTw.cPl E v := by
  obtain ⟨v, ⟨hv, hvu⟩, -⟩ := hS u
  rcases GlobLev.eq_or_eq_conjSrc hvu.symm with h | h
  · exact Or.inl (h ▸ hv)
  · exact Or.inr ⟨v, hv, h⟩

theorem split_of_conj_ne {v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ v) : IsSplitAt v := by
  by_contra hv
  exact h (GlobLev.conjSrc_eq_of_not_split hv)

theorem cPl_cPl (v : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem conj_not_mem {S : Set (Pl E)} (hS : IsSection S) {v : Pl E} (hv : v ∈ S) (h : IsSplitAt v) :
    GlobalTheory.EulerTw.cPl E v ∉ S := by
  intro hc
  obtain ⟨u, hne, hu⟩ := h
  have h1 : (GlobalTheory.EulerTw.cPl E v).under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) :=
    (GlobalTheory.EulerTwRestr.mem_orb_iff v _).1 (by simp [GlobalTheory.EulerTw.orb])
  have h2 : GlobalTheory.EulerTw.cPl E v = v := (hS v).unique ⟨hc, h1⟩ ⟨hv, rfl⟩
  rcases GlobLev.eq_or_eq_conjSrc hu with h3 | h3
  · exact hne h3
  · exact hne (h3.trans h2)

end GlobalTheory.CompanionTheory.SuppFinTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNull
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

open GlobalTheory.CompanionTheory.MPDict.SmoothRep (rt mem_mchart ev_rt)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

def ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) ((i.appLE (mchart p) (i ⁻¹ᵁ mchart p) le_rfl).hom (rt p q)) y

theorem mem_ptsIn_of_over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
  (mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)

theorem ratioVec_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0)
    (q : Σ k, Bk n k) : ratioVec i p y q = z q / z ⟨q.1, p q.1⟩ :=
  (CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _
    (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)

theorem sameOrbit_ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (ratioVec i p y) := by
  refine ⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩
  rw [ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]

theorem over_liftOf {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Over i y (liftOf i y) := by
  obtain ⟨z, -, hz⟩ := _root_.GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder m n X i y
  have h : ∃ z, Over i y z := ⟨z, hz⟩
  rw [liftOf, dite_eq_left h]
  exact h.choose_spec

theorem differentiableAt_projCoord {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ c.e.source) {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (h0 : Ψ (segre z) 0 ≠ 0) :
    DifferentiableAt ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) := by
  choose p hp using fun k => exists_block_ne_zero_of_isUnder H k
  have hyW := mem_ptsIn_of_over i H hp
  have hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) :=
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    ⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩
  have hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y) :=
    differentiableAt_pi.2 fun q =>
      (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl
  let L := LinearMap.toContinuousLinearMap Ψ
  have hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y) :=
    L.differentiableAt.comp _ hs
  have hc (a : Fin (D + 1)) := differentiableAt_pi.1 hL a
  have hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0 := by
    obtain ⟨l, hl0, e⟩ := sameOrbit_ratioVec i H hp
    intro h
    apply h0
    rw [segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]
  have hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0 := by
    rw [c.finChart.left_inv hy]
    exact hne
  have hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)]
      fun v => ratios Ψ (ratioVec i p (c.finChart.symm v)) := by
    filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0
    have H' := over_liftOf i (c.finChart.symm v)
    have hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0 := fun k =>
      (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k)
        ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))
    exact ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0
  refine DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev
  simp only [ratios, div_eq_mul_inv]
  exact (hc a.succ).mul ((hc 0).inv hne')

theorem volume_image_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D Ψ c
  set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA
  have e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun y hy => by
      simp only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]
  rw [e]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_
  · rintro _ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩
    exact ((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · rintro _ ⟨y, ⟨-, -, hc⟩, rfl⟩
    have h0 := not_not.1 hc
    have hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det =
        Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
        (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, h0, Algebra.norm_complex_apply, map_zero]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrderedStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_factors_dual_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k → ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)), LFactors 𝔪 x → ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  first | exact @GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | exact GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | (intros; apply GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLevChars

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem sigR_algebraMap (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

theorem smul_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hG.carrier]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hG.carrier] at h2
  exact h2

theorem fixed_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a : S) (ha : σS a = a) :
    ∃ α : Fv F v, (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) α :=
  hG.fixed a (by rw [← hG.sig, ha])

theorem basis_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hG.carrier] at h
  exact h

theorem nontrivial_S (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hG.quad.notUnit (isUnit_of_subsingleton _)

theorem card_eq_two (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : d = 2 := by
  obtain ⟨u, hu, hb⟩ := hG.quad.basis
  have : Nontrivial S := nontrivial_S hG
  have : Nontrivial (Fv F v ⊗[F] E) := (Subtype.val_injective (p := fun x => x ∈ S)).nontrivial
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s)) := by
        have h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E)) := eq_neg_of_add_eq_zero_right h
        have h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]
      have hfix : σS u = u := Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])
      rw [hfix, sub_self, isUnit_zero_iff] at hu
      exact zero_ne_one hu
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at h
    exact hinj (by rw [h, map_zero])
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]) := by
    rw [← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := hb ⟨_, basis_mem hG i⟩
    obtain ⟨α, hα⟩ := fixed_eq hG x hx
    obtain ⟨β, hβ⟩ := fixed_eq hG y hy
    have e2 : Algebra.TensorProduct.basis (Fv F v) bs i =
        α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E) := by
      have e3 := congrArg Subtype.val e
      simp only [Subring.coe_add, Subring.coe_mul] at e3
      rw [e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [SetLike.mem_coe, e2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  have h2 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  simpa using h2.symm.trans h1

theorem trace_algebraMap_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) (Fv F v ⊗[F] E) x) = 2 * x := by
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin,
    card_eq_two hG, two_nsmul, two_mul]

theorem psiF_compat (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) :
    psiF ψv ϖ c (k + 1) (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * a) = psiF ψv ϖ c k a := by
  unfold psiF
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv,
    mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]

theorem mem_level_of_character_trivial (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (hc1 : ‖c‖ = 1) (a : S) (ha : σS a = a)
    (hb : ∀ b, σS b = b → hG.psiLev hc 1 (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev hG.pS 1 := by
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h
    have := hG.two
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨α, hα⟩ := fixed_eq hG a ha
  have hαO : α ∈ v.adicCompletionIntegers F := by
    have h2 := hG.trace_mem a.2
    rw [hα, trace_algebraMap_eq hG] at h2
    have h3 := mul_mem hG.half_mem h2
    rwa [← mul_assoc, inv_mul_cancel₀ h20, one_mul] at h3
  have hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F := by
    refine (hG.psi_cond _).1 fun β hβ => ?_
    have hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
      have h1 := smul_mem hG hβ (one_mem S)
      rwa [← Algebra.algebraMap_eq_smul_one] at h1
    have hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩ := Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)
    have h1 := hb _ hfix
    rw [hG.psiLev_mk] at h1
    have e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β) := by
      rw [Subring.coe_mul, hα, map_mul]
    rw [e] at h1
    unfold psiF at h1
    rw [trace_algebraMap_eq hG] at h1
    rw [← h1]
    congr 1
    have := hG.unif_ne
    field_simp
  have hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hkey ⊢
    rw [norm_mul, hc1, one_mul] at hkey
    exact hkey
  have hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S := by
    have h1 := smul_mem hG hγ (one_mem S)
    rwa [← Algebra.algebraMap_eq_smul_one] at h1
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩
  rw [pow_one, Subring.coe_mul, hα]
  show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _
  rw [← map_mul]
  congr 1
  have := hG.unif_ne
  field_simp

theorem levChars : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1
  refine ⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩
  rw [GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]
  exact psiF_compat hG c k a

end GlobalTheory.CompanionTheory.GunrLevChars

end
end

