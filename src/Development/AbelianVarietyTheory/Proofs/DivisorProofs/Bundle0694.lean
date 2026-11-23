module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilLift

theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionHolomorphicMulFrameExtendByZero
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  intro n Y _ _ _ _ _ ι La _ A la U z β F0 hE hβ hF
  have hfun : (fun y : U => GlobalTheory.OTY.TwEst.ext0 U F0 y) = F0 :=
    funext fun y => GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U F0 y
  have hd := (_root_.GlobalTheory.holo_etale_iff_charts n Y ι La A U z hE (GlobalTheory.OTY.TwEst.ext0 U F0)).1 (by rw [hfun]; exact hF)
  refine ⟨⟨fun i => (hβ.1.1 i).mul (hd i), fun i j y hy hi hj => ?_⟩, ?_⟩
  · show β i y * _ = _ * (β j y * _)
    rw [hβ.1.2 i j y hy hi hj, mul_assoc]
  · have hc : ContinuousOn (GlobalTheory.OTY.TwEst.ext0 U F0) U := by
      intro y hy
      have hs := A.mem_pick y
      set e := A.chart (A.pick y) with he
      have hop : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hE.isOpen
      have hm : e y ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hs, by simpa [e.left_inv hs] using hy⟩
      have h1 : ContinuousAt (GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) (e y) :=
        (hd (A.pick y)).continuousOn.continuousAt (hop.mem_nhds hm)
      have h2 : ContinuousAt ((GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) ∘ e) y :=
        h1.comp (e.continuousAt hs)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with x hx
      simp [e.left_inv hx]
    classical
    have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)) (s := Uᶜ))
      hE.isOpen.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, GlobalTheory.OTY.TwEst.ext0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieAway

section Basic

variable {R : Type} [CommRing R]

theorem scaleS_toRingHom (c : R) : (Chart.scaleS (S := R) c).toRingHom = epsScaleR c := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleS_fst, epsScaleR]
  · simp [Chart.scaleS_snd, epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem tanS_of_isTangent {v : epsR R ⟶ G} (h : IsTangent v) : Chart.TanS (S := R) (A := R) v :=
  (Chart.isTan_iff v).mpr h

theorem isTangent_of_tanS {v : epsR R ⟶ G} (h : Chart.TanS (S := R) (A := R) v) : IsTangent v :=
  (Chart.isTan_iff v).mp h

theorem isTangent_iff_tanS (r : R) (y : epsR (Localization.Away r) ⟶ Chart.Gs G r) :
    IsTangent y ↔ Chart.TanS (Chart.pushR G y) := by
  rw [← Chart.isTan_iff]
  constructor
  · intro h
    have := congrArg (Chart.pushR G) h
    rw [Chart.pushR_spMap, Chart.pushR_one] at this
    exact this
  · intro h
    apply Chart.pushR_inj G
    rw [Chart.pushR_spMap, Chart.pushR_one]
    exact h

theorem scale_left (c : R) (v : epsR R ⟶ G) :
    Geo.Tor.spMap (epsScaleR c) ≫ v.left = (Chart.spMap (Chart.scaleS (S := R) c) ≫ v).left := by
  rw [Over.comp_left, Chart.spMap_left, ← scaleS_toRingHom]

end Basic

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Res

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)

def resA (v : epsR R ⟶ G) : epsR (Localization.Away r) ⟶ Chart.Gs G r :=
  Chart.pullR G (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v)

theorem pushR_resA (v : epsR R ⟶ G) :
    Chart.pushR G (resA r v) = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v :=
  Chart.pushR_pullR G _

variable {O O' : Type} [CommRing O] [CommRing O'] [IsCommMonObj G] (a : OAct O G)
  (a' : OAct O' (Chart.Gs G r))

def resL (v : GlobalTheory.Serre.Lie a) : GlobalTheory.Serre.Lie a' :=
  GlobalTheory.Serre.Lie.mk a' (resA r v.hom) (by
    rw [isTangent_iff_tanS, pushR_resA]
    exact Chart.tanS_restrict _ (tanS_of_isTangent v.isTangent))

theorem pushR_resL (v : GlobalTheory.Serre.Lie a) :
    Chart.pushR G (resL r a a' v).hom = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom :=
  pushR_resA r v.hom

theorem pushR_smul (c : Localization.Away r) (y : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (c • y).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ Chart.pushR G y.hom := by
  have e : (c • y).hom = Chart.spMap (Chart.scaleS (S := Localization.Away r) c) ≫ y.hom :=
    Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c y).trans (scale_left c y.hom))
  rw [e, Chart.pushR_spMap]
  rfl

theorem hom_smul_eq (c : R) (v : GlobalTheory.Serre.Lie a) :
    (c • v).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ v.hom :=
  Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c v).trans (scale_left c v.hom))

theorem pushR_add (y z : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (y + z).hom = Chart.pushR G y.hom * Chart.pushR G z.hom :=
  map_mul (Chart.pushforwardHom G) y.hom z.hom

theorem resL_add (v w : GlobalTheory.Serre.Lie a) : resL r a a' (v + w) = resL r a a' v + resL r a a' w := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_add, pushR_resL, pushR_resL, pushR_resL, GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul]

theorem resL_smul (c : R) (v : GlobalTheory.Serre.Lie a) :
    resL r a a' (c • v) = algebraMap R (Localization.Away r) c • resL r a a' v := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_smul, pushR_resL, pushR_resL, hom_smul_eq, Chart.res_scale]
  rfl

end Res

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Cover

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [∀ s : R, Smooth (Chart.Gs G s).hom]

theorem tan_away_uniq (r : R) {w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G} (hw : Chart.TanS w)
    (h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w = 1) :
    ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (r ^ N)) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  have C : ∀ k, Chart.Chart (Chart.Gs G (s k)) := fun k => (hC k).some
  have hwk : ∀ k, Chart.TanS (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w) :=
    fun k => Chart.tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra R A], Chart.TanS (1 : Chart.sp (R₀ := R) (DualNumber A) ⟶ G) :=
    fun A _ _ => Chart.comp_one' _
  have h2 : ∀ k, ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w =
      Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫ 1 := by
    intro k
    apply Chart.tanS_away_uniq (C k) (A := Localization.Away (s k)) r (hwk k) (hone _)
    have hu : IsUnit (algebraMap R (Localization.Away (algebraMap R (Localization.Away (s k)) r)) r) :=
      Chart.isUnit_qv (s k) r
    rw [Chart.comp_one', Chart.res_res,
      show (IsScalarTower.toAlgHom R (Localization.Away (s k))
          (Localization.Away (algebraMap R (Localization.Away (s k)) r))).comp
          (Algebra.ofId R (Localization.Away (s k))) =
        (Chart.awayHom r _ hu).comp (Algebra.ofId R (Localization.Away r)) from Chart.ofId_ext _ _,
      ← Chart.res_res, h1, Chart.comp_one']
  choose N hN using h2
  refine ⟨Finset.univ.sup N, Chart.tan_ext_cover s hs fun k => ?_⟩
  rw [Chart.comp_one', Chart.res_scale, Algebra.ofId_apply, map_pow,
    Chart.scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), Chart.comp_one']

theorem tan_away_lift (r : R) (hr : Nonempty (Chart.Chart (Chart.Gs G r)))
    {y : Chart.sp (R₀ := R) (DualNumber (Localization.Away r)) ⟶ G} (hy : Chart.TanS y) :
    ∃ N : ℕ, ∃ w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G, Chart.TanS w ∧
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w =
        Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away r) r ^ N)) ≫ y := by
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  let s' : Fin (n + 1) → R := Fin.cons r s
  have hs' : Ideal.span (Set.range s') = ⊤ := by
    rw [eq_top_iff, ← hs]
    apply Ideal.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨k.succ, Fin.cons_succ _ _ _⟩
  have C : ∀ k, Chart.Chart (Chart.Gs G (s' k)) := Fin.cases hr.some (fun k => (hC k).some)
  exact Chart.tan_extend s' hs' C 0 hy

end Cover

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

theorem lie_away {R O O' : Type} [CommRing R] [CommRing O] [CommRing O'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (a : OAct O G) (r : R) (a' : OAct O' (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) :
    Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) →
    Nonempty (LocalizedModule (Submonoid.powers r) (GlobalTheory.Serre.Lie a) ≃ₗ[Localization.Away r] GlobalTheory.Serre.Lie a') := by
  intro hr
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  letI : Module R (GlobalTheory.Serre.Lie a') := Module.compHom _ (algebraMap R (Localization.Away r))
  haveI : IsScalarTower R (Localization.Away r) (GlobalTheory.Serre.Lie a') :=
    ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  let ρ : GlobalTheory.Serre.Lie a →ₗ[R] GlobalTheory.Serre.Lie a' :=
    { toFun := resL r a a'
      map_add' := resL_add r a a'
      map_smul' := resL_smul r a a' }
  have hρ : ∀ v, Chart.pushR G (ρ v).hom =
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom := pushR_resL r a a'
  haveI : IsLocalizedModule (Submonoid.powers r) ρ := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.Away r) x
      have hx : ∀ m : GlobalTheory.Serre.Lie a',
          (algebraMap R (Module.End R (GlobalTheory.Serre.Lie a')) x) m = (u : Localization.Away r) • m := fun m => by
        rw [Module.algebraMap_end_apply, hu]; rfl
      refine ⟨fun m₁ m₂ e => ?_, fun m => ⟨(↑u⁻¹ : Localization.Away r) • m, ?_⟩⟩
      · rw [hx, hx] at e
        have := congrArg (fun z => (↑u⁻¹ : Localization.Away r) • z) e
        simp only [smul_smul, Units.inv_mul, one_smul] at this
        exact this
      · rw [hx, smul_smul, Units.mul_inv, one_smul]
    · have hy : Chart.TanS (Chart.pushR G y.hom) := (isTangent_iff_tanS r y.hom).mp y.isTangent
      obtain ⟨N, w, hw, he⟩ := tan_away_lift r hr hy
      refine ⟨(GlobalTheory.Serre.Lie.mk a w (isTangent_of_tanS hw), ⟨r ^ N, N, rfl⟩), ?_⟩
      ext1
      apply Chart.pushR_inj G
      rw [hρ, GlobalTheory.Serre.Lie.hom_mk, he]
      change Chart.pushR G ((algebraMap R (Localization.Away r) (r ^ N)) • y).hom = _
      rw [pushR_smul, map_pow]
    · have h0 : ρ (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
      have h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ (x₁ - x₂).hom = 1 := by
        rw [← hρ, h0, GlobalTheory.Serre.Lie.hom_zero, Chart.pushR_one]
      obtain ⟨N, hN⟩ := tan_away_uniq r (tanS_of_isTangent (x₁ - x₂).isTangent) h1
      refine ⟨⟨r ^ N, N, rfl⟩, ?_⟩
      rw [← sub_eq_zero, ← smul_sub]
      ext1
      rw [Submonoid.smul_def, hom_smul_eq, hN, GlobalTheory.Serre.Lie.hom_zero]
  exact ⟨(IsLocalizedModule.iso (Submonoid.powers r) ρ).extendScalarsOfIsLocalization (Submonoid.powers r)
    (Localization.Away r)⟩

end GlobalTheory.LieAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

theorem isTest_pullback : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  intro Rg _ A B _ _ L M T T' t h A₁ B₁ _ _ φA₁ φB₁ Φ₁ hT
  obtain ⟨hA, hB, hm, hl⟩ := hT
  haveI : IsMonHom Φ₁ := hm
  have eΦ : ((Over.pullback h).map Φ₁).left ≫ pullback.fst B₁.hom h = pullback.fst A₁.hom h ≫ Φ₁.left :=
    pullback.lift_fst _ _ _
  have gA := isGrpPullback_pullback A₁ h
  have gB := isGrpPullback_pullback B₁ h
  refine ⟨(Over.pullback h).obj A₁, inferInstance, (Over.pullback h).obj B₁, inferInstance,
    pullback.fst A₁.hom h ≫ φA₁, pullback.fst B₁.hom h ≫ φB₁, (Over.pullback h).map Φ₁,
    ⟨gA.comp hA, gB.comp hB, PullGtPf.isMonHom_of_grpPullback gA gB Φ₁ _ eΦ, ?_⟩,
    pullback.fst A₁.hom h, pullback.fst B₁.hom h, gA, gB, rfl, rfl, eΦ⟩
  exact LBIso.chartPull
    (chartPullSame L (fun _ => pullback.fst A₁.hom h ≫ φA₁) (fun _ => φA₁) (fun _ => 1) (pullback.fst A₁.hom h)
      (fun _ => rfl))
    (HomFixGlue.chartPullPullPull M _ _ _ _ (pullback.fst A₁.hom h)
      (by rw [← Category.assoc, eΦ, Category.assoc])) hl

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassVanishesFinitelyGeneratedSubalgebraStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) → ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i), pull _ (spMap (GlobalTheory.EtC.GmStep.laurentMap (algebraMap A S))) _ _ x = 0 → ∃ t : Finset S, pull _ (spMap (GlobalTheory.EtC.GmStep.laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (exact GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (intros; apply GlobalTheory.EtC.GmStep.KillColim.kill_colim  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (exact GlobalTheory.EtC.laurent_vanishing_of_noetherian) | (intros; apply GlobalTheory.EtC.laurent_vanishing_of_noetherian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologous
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem log_cocycle_cohomologous : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by

  intro I _ g Λ _ F K a lg β ha hdw hsh hlgsh hlgadd e uu ℓ huu hℓ
  have hnil : ∀ T : K.Obj, IsNilDP T.δ := fun T ↦ by letI := T.ratAlg; exact isPDNilpotent_of_rat _ T.nil
  have hdp : ∀ {T T' : K.Obj} (ψ : T ⟶ T'), DividedPowers.IsDPMorphism T.δ T'.δ (ψ.φ : T.C →+* T'.C) := fun {T T'} ψ ↦ by
    letI := T'.ratAlg; exact isDPMorphism_of_rat T.δ T'.δ (ψ.φ : T.C →+* T'.C) ψ.mem
  have hw : ∀ (T T' : K.Obj) (φ : T ⟶ T'), ∃ n ∈ T'.J, dpExp T'.δ n =
      uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) := by
    intro T T' φ
    have hm : uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) - 1 ∈ T'.J := by
      have := T'.J.mul_mem_right (((e T')⁻¹ : (T'.C)ˣ) : T'.C) (huu T T' φ)
      convert this using 1
      rw [sub_mul, Units.mul_inv]
    obtain ⟨x, hx, hx'⟩ := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T'.C T'.J T'.δ (hnil T')).surjOn hm
    exact ⟨x, hx, hx'⟩
  choose n hnJ hn using hw
  refine ⟨fun T T' φ ↦ (n T T' φ - T'.ρ (lg φ.deg T'.k) : T'.C), ?_⟩
  intro T T' T'' φ ψ
  obtain ⟨hℓJ, hℓe⟩ := hℓ T T' T'' φ ψ
  have hce := close_exp T''.J T''.δ (hnil T'') _ _ (a φ.deg T'.k) (lg φ.deg T'.k) (hdw φ.deg T'.k) ψ.close
  have hxJ := ψ.close.sub_mem (lg φ.deg T'.k)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at hce hxJ
  have hnat : ∀ c ∈ T'.J, ψ.φ (dpExp T'.δ c) = dpExp T''.δ (ψ.φ c) := fun c hc ↦
    (dpExp_add_and_natural _ _ _ _ T'.δ T''.δ (hnil T')).2 _ (hdp ψ) c hc
  have hadd := (dpExp_add_and_natural _ _ _ _ T''.δ T''.δ (hnil T'')).1
  have hQ : ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * ψ.φ (e T' : T'.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have haa : T''.ρ (a (φ ≫ ψ).deg T''.k) = T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) := by
    rw [Charts.comp_deg, hsh _ _ _ _ (Charts.Hom.le ψ), map_mul]
  have hn1 := hn T T'' (φ ≫ ψ)
  have hn2 := hn T T' φ
  have hn3 := hn T' T'' ψ
  rw [Charts.comp_φ, haa] at hn1
  set x := ψ.φ (T'.ρ (lg φ.deg T'.k)) - T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) with hx
  have key : dpExp T''.δ (ℓ T T' T'' φ ψ + n T T'' (φ ≫ ψ) + x) = dpExp T''.δ (ψ.φ (n T T' φ) + n T' T'' ψ) := by
    rw [hadd _ (T''.J.add_mem hℓJ (hnJ _ _ _)) _ hxJ, hadd _ hℓJ _ (hnJ _ _ _),
      hadd _ (ψ.mem _ (hnJ _ _ _)) _ (hnJ _ _ _), ← hnat _ (hnJ _ _ _), hn1, hn2, hn3]
    simp only [map_mul]
    linear_combination (ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) *
        (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hℓe
      - (ψ.φ (uu T T' φ) * ψ.φ (φ.φ (e T : T.C)) * ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * uu T' T'' ψ * ψ.φ (e T' : T'.C) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C)) * hce
      - (ψ.φ (uu T T' φ) * uu T' T'' ψ * ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hQ
  have hinj := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T''.C T''.J T''.δ (hnil T'')).injOn
    (T''.J.add_mem (T''.J.add_mem hℓJ (hnJ _ _ _)) hxJ) (T''.J.add_mem (ψ.mem _ (hnJ _ _ _)) (hnJ _ _ _)) key
  have hb : T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) = T''.ρ (lg φ.deg T''.k) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
    rw [hlgsh _ _ _ _ (Charts.Hom.le ψ), T''.ρ.map_add, T''.ρ_cst]
  show ℓ T T' T'' φ ψ = (ψ.φ (n T T' φ - T'.ρ (lg φ.deg T'.k)) - (n T T'' (φ ≫ ψ) - T''.ρ (lg (φ ≫ ψ).deg T''.k)) +
    (n T' T'' ψ - T''.ρ (lg ψ.deg T''.k))) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)
  rw [Charts.comp_deg, hlgadd, map_sub, T''.ρ.map_add]
  rw [hx, hb] at hinj
  linear_combination hinj

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmEFormAndDegree
section
noncomputable section
namespace GlobalTheory.FockOm
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem omE_form_and_degree : ∀ (p q r s : ℕ) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → (linePos l = linePos l' → omE l l' P ∈ homog (Ix p q × Ix r s) d) ∧ (linePos l = true → linePos l' = false → omE l l' P = X l * X l' * P) ∧ (linePos l = false → linePos l' = true → omE l l' P = - pderiv l (pderiv l' P)) := by
  intro p q r s l l' d P hP
  refine ⟨fun h => GlobalTheory.FockDeg.omE_mem_homog h hP, fun hl hl' => ?_, fun hl hl' => ?_⟩
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne, mul_assoc]
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne]

end GlobalTheory.FockOm
end
end

