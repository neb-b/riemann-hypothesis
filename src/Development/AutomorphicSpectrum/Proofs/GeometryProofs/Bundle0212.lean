module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0210
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwo
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.CompanionTheory.Ar.AVExp

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem compactSpace_points (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace _ (PointsCompact.pointTopology A) := by
  have h1 := @valAt'_rules
  have h2 := @existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov
      fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

theorem surjective_mulA (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (r : ℕ) (hr : 1 ≤ r) :
    Surjective (Out.mulA A r).left := by
  obtain ⟨hfin, hflat⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation ((Out.mulA A r).left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (Out.mulA A r).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  have hcl : IsClosed (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isOpenMap.isOpen_range
  have hne : (Set.range (Out.mulA A r).left).Nonempty := Set.range_nonempty _
  exact ⟨Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)⟩

theorem exists_div (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ A) (r : ℕ) (hr : 1 ≤ r) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = a₀ := by
  obtain ⟨hfin, -⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have hsurj := surjective_mulA A hA r hr
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (Out.mulA A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ (Out.mulA A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ A.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (Out.mulA A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = b ≫ Out.mulA A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

theorem exists_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  intro A _ L g hA hL hdim
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := hA.comm
  have := htop A
  have := compactSpace_points A L hL
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hdim 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
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
  have hex0 : (hφ.exp 0).toMul = 1 := by rw [map_zero]; rfl
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x =>
    exists_div A hA x.toMul n (Nat.one_le_iff_ne_zero.mpr hn)

  obtain ⟨W', large₂, hW', h0', hL', hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (large₂ : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ large₂ W' ∧
      Set.MapsTo large₂ W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (large₂ v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩, U, t, hU, ?_, ?_, hφ.hasFDerivAt_chart_exp⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (large₂ (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL' hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add (f := _), add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    simp
  · show ⊤ ≤ (hφ.exp 0).toMul.left ⁻¹ᵁ U
    rwa [hex0]
  · show ∀ D : Γ(A.left, U) →+ ℂ, _ → (∀ f f', D (f * f') =
      valAt' (hφ.exp 0).toMul.left U f * D f' + valAt' (hφ.exp 0).toMul.left U f' * D f) → _
    rwa [hex0]

end GlobalTheory.CompanionTheory.Ar.AVExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

open Matrix

variable {p q : ℕ} {g : ℕ}

theorem det_fromRows_mul_top (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows (A * C) F).det = A.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows (A * C) F = Matrix.fromBlocks A 0 0 1 * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_fromRows_mul_bot (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows C (B * F)).det = B.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows C (B * F) = Matrix.fromBlocks 1 0 0 B * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_chg (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Pe Tc : Fin p ⊕ Fin q → Fin g → ℂ)
    (S : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ) (V V' : Fin p → Fin g → ℂ) (W W' : Fin q → Fin g → ℂ)
    (Fm Fm' B₀ B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d d' : ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ)
    (hV : ∀ a, V' a = ∑ b, A a b • V b) (hW : ∀ j, W' j = ∑ k, B j k • W k)
    (hWi : LinearIndependent ℂ W) (hWi' : LinearIndependent ℂ W')
    (k3 : ∀ n, Tc n = ∑ j, B₀ j n • W j) (l3 : ∀ n, Tc n = ∑ j, B' j n • W' j)
    (l4 : ∀ j n, ∑ m, Fm' j m * S m n = B' j n) (hd' : d' ≠ 0)
    (k6 : ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • Pe m) = V a)
    (l7 : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V' a) →
      (Matrix.fromRows C Fm').det = d')
    (hu : ∀ (F₂ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d₂ : ℂ), (∀ j n, ∑ m, F₂ j m * S m n = B₀ j n) → d₂ ≠ 0 →
      (∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
        (Matrix.fromRows C F₂).det = d₂) → d₂ = d) :
    d * A.det = d' * B.det := by
  have lift : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
      ∀ a, T (∑ m, (A * C) a m • Pe m) = V' a := by
    intro C hC a
    have : ∑ m, (A * C) a m • Pe m = ∑ b, A a b • ∑ m, C b m • Pe m := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, hV a]
    exact Finset.sum_congr rfl fun b _ => by rw [map_smul, hC b]
  obtain ⟨C₀, hC₀⟩ := k6
  have hA : A.det ≠ 0 := by
    intro h0
    have := l7 _ (lift C₀ hC₀)
    rw [det_fromRows_mul_top, h0, zero_mul] at this
    exact hd' this.symm
  have hB : B.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hc
    have hz : ∑ j, c j • W' j = 0 := by
      simp only [hW, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_smul]
      have := congrFun hcB k
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    funext j
    exact Fintype.linearIndependent_iff.1 hWi' c hz j
  have hB₀ : ∀ k n, B₀ k n = ∑ j, B j k * B' j n := by
    intro k n
    have hz : ∑ k, (B₀ k n - ∑ j, B j k * B' j n) • W k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← k3 n]
      rw [sub_eq_zero, l3 n]
      simp only [hW, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hWi _ hz k)
  have hfin := hu (Bᵀ * Fm') (B.det * d' / A.det) ?_ (div_ne_zero (mul_ne_zero hB hd') hA) ?_
  · rw [← hfin]; field_simp
  · intro j n
    rw [hB₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, ← l4]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, _root_.mul_assoc]
  · intro C hC
    have h1 := l7 _ (lift C hC)
    rw [det_fromRows_mul_top] at h1
    rw [det_fromRows_mul_bot, Matrix.det_transpose, ← h1]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l}

theorem isDerivAt0_of_isComb {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty)
    (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Sp ℂ ⟶ Xo.X)
    (hx : x = FU.u i P) {n : ℕ} (a : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) (V : Fin n → Fin g → ℂ)
    (hV : ∀ k, IsDerivAt0 (fun z => (FU.ex i P z).left) (V k) (v k).left) (h : IsComb a v w) :
    IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, a k • V k) w.left := by
  subst hx
  exact (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV a w.left).1
    ((EigDir.isComb_iff_isCombAt _ a v w).1 h)

theorem tauIn_conj {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ}
    (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) (a : 𝓞 E) :
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
    apply Subtype.ext
    show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
  rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem isLinearMap_tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty τ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem chg_of_isFlatAn {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hT : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (he : LinearIndependent (𝓞 E) e)
    (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (y : Sp ℂ ⟶ Xo.XF c)
    (hy : under y = FU.u i P) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (A : Matrix (Fin D.p) (Fin D.p) ℂ) (Bm : Matrix (Fin D.q) (Fin D.q) ℂ)
    (hf : IsFramed Set.univ τ σ y v w) (hf' : IsFramed Set.univ τ σ y v' w')
    (hA : ∀ a, IsComb (A a) v (v' a)) (hB : ∀ j, IsComb (Bm j) w (w' j))
    (Φ : CFn Xo c) (ρ : ℂ) (hΦ : IsFlatAn Set.univ τ τ' σ Φ FU i e ρ) :
    Φ y v' w' * A.det = Φ y v w * Bm.det := by
  obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, hu⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.anSolve E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v w he hP hy hf
  obtain ⟨⟨V', W', Fm', B', d'⟩, ⟨l1, l2, l3, l4, l5, ⟨C', hC'⟩, l7⟩, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.anSolve E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v' w' he hP hy hf'
  have f1 : Φ y v w * d = ρ := by
    have := hΦ P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rwa [k7 C hC] at this
  have f2 : Φ y v' w' * d' = ρ := by
    have := hΦ P y v' w' V' W' C' Fm' B' hP hy hf' l1 l2 hC' l3 l4
    rwa [l7 C' hC'] at this
  obtain ⟨V₀, hV₀, -, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ τ' D.p v' hP hy hτ hf'.2.2.1
  obtain ⟨W₀, hW₀, hWi, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w hP hy (tauIn_conj hτ) hf.2.2.2
  obtain ⟨W₁, hW₁, hWi', -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w' hP hy (tauIn_conj hτ) hf'.2.2.2
  have eW : W = W₀ := funext fun j => (hW₀ j _).1 (k2 j)
  have eW' : W' = W₁ := funext fun j => (hW₁ j _).1 (l2 j)
  have hV : ∀ a, V' a = ∑ b, A a b • V b := fun a =>
    ((hV₀ a _).1 (l1 a)).trans ((hV₀ a _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ v _ V k1 (hA a))).symm
  have hW : ∀ j, W' j = ∑ k, Bm j k • W k := fun j =>
    ((hW₁ j _).1 (l2 j)).trans ((hW₁ j _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ w _ W k2 (hB j))).symm
  have key := det_chg ((isLinearMap_tyPart ty τ').mk' _) (fun m => P (e m))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)))
    (fun m n => τ' (sesq (FU.Di i) (e m) (e n))) V V' W W' Fm Fm' B₀ B' d d' A Bm hV hW
    (eW ▸ hWi) (eW' ▸ hWi') k3 l3 l4 l5 ⟨C, hC⟩ l7
    (fun F₂ d₂ h4 h5 h7 => congrArg (fun x => x.2.2.2.2) (hu (V, W, F₂, B₀, d₂) ⟨k1, k2, k3, h4, h5, ⟨C, hC⟩, h7⟩))
  apply mul_right_cancel₀ (mul_ne_zero k5 l5)
  linear_combination (A.det * d) * f2 - (Bm.det * d') * f1 + ρ * key

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hT hrt hτ
  have hrank : ∀ i, ∃ e : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e := by
    intro i
    have hr : D.p + D.q ≤ Module.finrank (𝓞 E) (FU.Di i).La := by
      rw [(FU.Di i).rank, (FU.sig i).1, (FU.sig i).2]
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hr
    exact ⟨f ∘ finSumFinEquiv, hf.comp _ finSumFinEquiv.injective⟩
  choose e he using hrank
  choose t ht hN using fun i => _root_.GlobalTheory.CompanionTheory.Ar.Flat.hodgeNorm_flat E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) (he i)
  let ρ : Fin FU.n → ℂ := fun i => (((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)
  have hs : ∀ i, Real.sqrt (t i) ≠ 0 := fun i => (Real.sqrt_pos.2 (ht i)).ne'
  have hρ : ∀ i, ρ i ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (inv_ne_zero (hs i))
  have hρt : ∀ i, ‖ρ i‖ ^ 2 * t i = 1 := by
    intro i
    have h1 : ‖ρ i‖ = (Real.sqrt (t i))⁻¹ := by
      show ‖(((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [h1, inv_pow, Real.sq_sqrt (ht i).le, inv_mul_cancel₀ (ht i).ne']
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.anDef E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ he
  have hloc : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ →
      ∃ (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P := by
    intro y hy
    obtain ⟨i, P, hP, hu⟩ := FU.onto (under y) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
      simp only [spMap, ← Spec.map_comp]
      rfl)
    exact ⟨i, P, hP, hu.symm⟩
  refine ⟨Φ, { ne := ?_, chg := ?_, norm := ?_, hol := ?_ }, fun i => ⟨e i, ρ i, hρ i, he i, hΦ i⟩⟩
  · intro y v w hf h0
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, -⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.Flat.anSolve E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) P y v w (he i) hP hy hf
    have := hΦ i P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rw [h0, zero_mul] at this
    exact hρ i this.symm
  · intro y v w v' w' A B hf hf' hA hB
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    exact Unit.chg_of_isFlatAn FU hT hrt hτ i (e i) (he i) P hP y hy v v' w w' A B hf hf' hA hB Φ (ρ i) (hΦ i)
  · intro y v w Γ Δ hf hΓ hΔ
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    have := hN i (ρ i) Φ (hΦ i) P y v w Γ Δ hP hy hf hΓ hΔ
    rw [this, hρt i, _root_.one_mul]
  · intro R _ x vR wR m B ψ v w h1 h2 h3
    exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.anHol E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ Φ he hΦ R x vR wR m B ψ v w h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.Flat
end

