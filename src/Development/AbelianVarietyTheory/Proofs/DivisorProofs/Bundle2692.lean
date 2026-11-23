module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.FirstChernW

open GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.LineForm.FirstChern

theorem smoothOn_atlas {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : Type} {U : Set (CxPts X.str σ)}
    {G : CxPts X.str σ → Matrix m m ℂ} (H : ∀ y ∈ U, MInfAt G y) (i j : m) :
    (atlas X σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1W_isForm_and_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  intro F _ σ X L ψ hψ
  have hφ : ∀ a (x : (atlas X σ).Pt), x.pt ∈ ptsIn X.str σ (L.U a) →
      ContDiffAt ℝ 2 (fun v => ψ.φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (hψ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := _root_.GlobalTheory.ChernFrame.chern_frame_closed (atlas X σ) (ι := Unit) (fun a => ptsIn X.str σ (L.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv X.str σ L a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ))
    (fun a => smoothOn_atlas fun y hy _ _ => (vInfAt_iff_cInfAt.2 (hψ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv X.str σ L a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [ψ.trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, -, h3⟩ := hP (fld _ (c1W ψ)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick ψ.isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨h1, h3⟩

end GlobalTheory.ChernCalc.FirstChernW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem det_upU {K : Type} [Field K] {s : ℕ} (y : Low s → K) : (upU y).det = 1 := by
  have hb : (upU y).BlockTriangular id := fun a b (hab : b < a) => by
    simp only [upU, Matrix.of_apply, dif_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => by simp [upU]

theorem pts_of {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hR : Refines E E' φ f) {A : Mat m X.Fn}
    {u : Cell m → Y.Fn} (hg : InCell E E' φ f A u (genericPoint Y.X)) {K : Type} [Field K] (x : Sp K ⟶ X.X)
    (hA : A ∈ E.S (x (IsLocalRing.closedPoint K))) (y₀ : Cell m → K)
    (hbears : ∀ p : Sp K ⟶ Y.X, A ∈ E.S (f (p (IsLocalRing.closedPoint K))) →
      (Bears E' φ A (upM y₀) p ↔ ∃ u' : Cell m → Y.Fn, upM u' * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, (ratOf Y).val p (u' j) = y₀ j))
    (huniq : ∀ (s : ℕ) (y y' : Low s → Y.Fn) (b : Matrix (Fin s) (Fin s) Y.Fn), (∀ i j, i < j → b i j = 0) →
      upU y = b * upU y' → y = y') :
    ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧
      ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  have hPar : Par 0 ⊤ (upM y₀) := fun τ =>
    ⟨fun _ _ => trivial, by simp [upM, det_upU], trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨p, ⟨hpf, hpB⟩, huq⟩ := hR.lifts K x A hA (upM y₀) hPar
  have hfz : f (p (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
    rw [← hpf]; rfl
  have hA' : A ∈ E.S (f (p (IsLocalRing.closedPoint K))) := hfz ▸ hA
  obtain ⟨u', hu'S, hu'v⟩ := (hbears p hA').1 hpB
  have huu : u' = u := by
    have h1 := Fr.mem_genericPoint hu'S
    have hdA : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
      have := Mat.det_map A φ.toRingHom τ
      rw [show A.map φ.toRingHom = A.map φ from rfl] at this
      rw [this]; exact (map_ne_zero _).2 (Fr.det_ne hg.1 τ)
    have hdu : ∀ τ, (upM u τ).det ≠ 0 := fun τ => by simp [upM, det_upU]
    have hP := (Fr.mem_iff hg.2).1 h1
    rw [Mat.mul_inv_rev, ← mul_assoc, mul_assoc (upM u'), Mat.mul_inv hdA, mul_one] at hP
    have he : upM u' = (upM u' * (upM u)⁻¹) * upM u := by rw [mul_assoc, Mat.inv_mul hdu, mul_one]
    funext ⟨τ, s⟩
    have := huniq (m τ) (fun s => u' ⟨τ, s⟩) (fun s => u ⟨τ, s⟩) ((upM u' * (upM u)⁻¹) τ)
      (fun i j hij => (hP τ).2.2.2 i j i.2 hij) (congrFun he τ)
    exact congrFun this s
  subst huu
  refine ⟨p, ⟨hpf, ⟨hA', hu'S⟩, hu'v⟩, fun p' ⟨hp'f, ⟨h1, h2⟩, hv⟩ => huq p' ⟨hp'f, (hbears p' h1).2 ⟨u', h2, hv⟩⟩⟩

theorem cell_points_existsUnique : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hR A u hg K _ x hA y₀
  exact pts_of hR hg x hA y₀ (fun p hp => _root_.GlobalTheory.FlagCell2.BearsCell.bears_iff F X Y ι m E E' φ f hR A K p hp y₀)
    (fun s y y' b hb h => upU_unique_of_lower Y.Fn s y y' b hb h)

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem graded_weight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr →
    IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L),
      Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  intro F _ σ X ι _ m E H gr hG hH x
  obtain ⟨B, hB, hgr⟩ := hG
  have hunit : ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∀ f : X.Fnˣ, (gr x).IsEqn z f →
      UnitAt z ((B * A⁻¹) x.1 x.2 x.2 / f) := by
    intro z A hA f hf
    obtain ⟨A₀, hA₀, t, ht, he⟩ := hgr z x
    obtain ⟨hu, hd⟩ := _root_.GlobalTheory.FlagChange.diag_unitAt_and_mul F X ι m E B hB z A₀ A hA₀ hA x
    have htf : UnitAt z ((t : X.Fn) / f) := (hf.iff_unitAt).1 he
    have hne : (A * A₀⁻¹) x.1 x.2 x.2 ≠ 0 := fun h0 => by
      obtain ⟨a, ha, h⟩ := hu
      rw [h0] at h
      exact (ha.map (algebraMap _ X.Fn)).ne_zero h
    have e : (B * A⁻¹) x.1 x.2 x.2 / f = ((t : X.Fn) / f) * ((A * A₀⁻¹) x.1 x.2 x.2)⁻¹ := by
      rw [← ht, hd]; field_simp
    rw [e]; exact htf.mul hu.inv

  let Ach : CxPts X.str σ → Mat m X.Fn := fun y => (E.nonempty (under y)).choose
  have hAch : ∀ y, Ach y ∈ E.S (under y) := fun y => (E.nonempty (under y)).choose_spec
  let val : Mat m X.Fn → CxPts X.str σ → X.Fn → ℝ := fun A y f =>
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2)
  let D := gr x
  have hP := presents_toLB D
  have heq : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      D.IsEqn (under y) (i.1.2) := fun i y hy => i.2.2 _ (mem_ptsIn.1 hy)
  have hindep : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      ∀ A ∈ E.S (under y), val (Ach y) y i.1.2 = val A y i.1.2 := fun i y hy A hA =>
    _root_.GlobalTheory.ChernCalc.grWeight_frame_indep F σ X ι m E H hH B hB y (Ach y) (hAch y) A hA x _ (hunit _ A hA _ (heq i y hy))
  let ψ : Weight X.str σ (toLB D) :=
    { isLB := isLB_toLB D
      φ := fun i y => val (Ach y) y i.1.2
      trans := by
        intro i j y hi hj
        have hu1 := hunit _ _ (hAch y) _ (heq i y hi)
        have hu2 : UnitAt (under y) ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := ((heq j y hj).iff_unitAt).1 (heq i y hi)
        have hg : gv X.str σ (toLB D) i j y = ratVal ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) y := by
          have hgen : genericPoint X.X ∈ (toLB D).U i ⊓ (toLB D).U j := ⟨i.2.1, j.2.1⟩
          rw [← fnOf_toLB_g i j hgen, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩) hgen]
          rfl
        have hi0 := (i.1.2).ne_zero
        have hj0 := (j.1.2).ne_zero
        have e : (B * (Ach y)⁻¹) x.1 x.2 x.2 / (j.1.2 : X.Fn) =
            ((B * (Ach y)⁻¹) x.1 x.2 x.2 / i.1.2) * ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := by
          field_simp
        show val (Ach y) y j.1.2 = val (Ach y) y i.1.2 - _
        simp only [val]
        rw [e, ratVal_mul hu1.regAt hu2.regAt, log_normSq_mul (ratVal_ne_zero hu1) (ratVal_ne_zero hu2), hg]
        ring }
  refine ⟨toLB D, fun i => i.1.2, ψ, hP, ?_, ?_⟩
  · intro i y hy
    have hu := hunit _ _ (hAch y) _ (heq i y hy)
    refine (_root_.GlobalTheory.ChernCalc.cInfAt_logUnit_grD F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2).congr ?_
    filter_upwards [frame_eventually_near F σ X ι m m E y (Ach y) (hAch y), (isOpen_ptsIn _).mem_nhds hy] with z hz hzi
    exact hindep i z hzi (Ach y) hz
  · funext p
    obtain ⟨⟨c, y⟩, hy⟩ := p
    have hy' : y ∈ c.e.source := hy
    have ha : y ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) := mem_pick ψ.isLB y
    have hu := hunit _ _ (hAch y) _ (heq _ y ha)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧ Ach y ∈ E.S (under z) :=
      Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds ha) (frame_eventually_near F σ X ι m m E y (Ach y) (hAch y))
    have hnear' : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧
        Ach y ∈ E.S (under (c.e.symm v)) := by
      have hc := c.e.continuousAt_symm (c.e.map_source hy')
      rw [ContinuousAt, c.e.left_inv hy'] at hc
      exact hc.eventually hnear
    have key : leviForm (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y) := by
      rw [leviForm_congr (u' := fun v => val (Ach y) (c.e.symm v) (pick ψ.isLB y).1.2)]
      · exact _root_.GlobalTheory.ChernCalc.leviForm_neg_log_unit_sub_log_grD F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2 c hy'
      · filter_upwards [hnear'] with v hv
        exact hindep _ _ hv.1 (Ach y) hv.2
    have e1 : c1W ψ ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y)) := rfl
    have e2 : grF E H x ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y)) := rfl
    rw [e1, e2]
    unfold HermFrame.ddc
    rw [key]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwistRank

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem rkK_eq_of_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) : Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  have hmap : (Submodule.span K (L : Set V)).map (φ : V →ₗ[K] W) = Submodule.span K (L' : Set W) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro f hf
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    · rw [Submodule.span_le]
      intro g hg
      refine ⟨a⁻¹ • (a • φ.symm g), Submodule.smul_mem _ _ (Submodule.subset_span (R := K) (hout g hg)), ?_⟩
      show φ (a⁻¹ • (a • φ.symm g)) = g
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul, φ.apply_symm_apply]
  unfold Formalism.HN.rkK
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem rankOn_twist {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) :
    rankOn U Z (G + G₀) = rankOn U Z G := by
  obtain ⟨φ, -, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := Good.exists_twist_scalar s
  exact rkK_eq_of_equiv φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _))

theorem cuspW_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') :
    cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem rankOn_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : rankOn U Z G = rankOn U Z G' := by
  have e : cuspOn U Z G = cuspOn U Z G' := by rw [cuspOn, cuspOn, cuspW_congr hU h]
  unfold rankOn latOn
  rw [e]

theorem psi_nonempty : Nonempty (Psi H) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : φ (H.rt : E) = H.rt0
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨conjEmb φ, conj_mem h⟩⟩

theorem exists_twSec_par (hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {a : ℝ} (hF : FlatExistsAt U x a) (Z : Comp Xo c) (w : Psi H → ℤ) :
    Nonempty (TwSec U x Z (wtOf Dw (parWt Dw w) 0)) := by
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF Z τ).1.some
  obtain ⟨τ₀⟩ := psi_nonempty (H := H)
  have hp : HasPts U Z := (sF τ₀).hasPts
  let s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ) :=
    (FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _)
  refine ⟨TwSec.ofConst s (GlobalTheory.FlatTwisting.finite_sum_flDefect w) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq s)
    fun G hG f hf => ?_⟩
  have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl)
    (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
  rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem wtOf_zero_nat (k : ℕ) : wtOf Dw 0 (k : ℤ) = k • wtOf Dw 0 1 := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul]; exact wtOf_zero
  | succ k ih =>
    rw [succ_nsmul, ← ih, ← wtOf_add]
    simp

end Gen

end GlobalTheory.TwistRank

namespace GlobalTheory.TwistRank

end GlobalTheory.TwistRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

theorem isIntAf_zero : IsIntAf (0 : AfP p) := fun v => by rw [map_zero]; exact zero_mem _

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_zsmul_mul (n : ℤ) {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) :
    IsIntAf ((n : ℚ) • (a * b)) := fun v => by
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_mul]
  exact zsmul_mem (mul_mem (ha v) (hb v)) n

theorem formInt_gen (D : Datum p) (a a' : AfP p) (x y : D.La) (ha : IsIntAf a) (ha' : IsIntAf a') :
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ y))) := by
  rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, zsmul_eq_mul, _root_.mul_one]
  exact isIntAf_zsmul_mul _ ha ha'

theorem formInt_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D →
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  intro p _ D v w hv hw
  set B := (D.EF.baseChange ℚ).baseChange (AfP p)

  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, IsIntAf (B z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      exact formInt_gen D a a' x y ha ha'
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBundlePullbackAdjointActionEqDiagonalPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  first | exact @GlobalTheory.ElRep.main | exact GlobalTheory.ElRep.main | (intros; apply GlobalTheory.ElRep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRowStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedLine_potential_hessian_det_own_row : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FlagCell2.row_levi_det | exact GlobalTheory.FlagCell2.row_levi_det | (intros; apply GlobalTheory.FlagCell2.row_levi_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → HasPolChart F s j e φ BD d x → HasChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasChart_of_hasPolChart | exact GlobalTheory.PolDeg.hasChart_of_hasPolChart | (intros; apply GlobalTheory.PolDeg.hasChart_of_hasPolChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotientsStatement
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceBasis_sectionTupleQuotients : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1)) (A : Subring K), Algebra.trdeg ℤ K = D → x l ≠ 0 → Algebra.FiniteType ℤ A → (∀ w ∈ A, IsIntegral (ratR x l) w) → (∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) K := by
  first | exact @GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | exact GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | (intros; apply GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR <;> assumption)
end

