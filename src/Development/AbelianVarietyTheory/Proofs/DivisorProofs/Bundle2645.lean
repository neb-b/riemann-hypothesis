module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GenericRatio

theorem exists_complete_point (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B), IsAdicComplete (maximalIdeal B) B ∧
      ∃ q : Sp B ⟶ T, Flat q ∧ q (closedPoint B) = t := by
  let O : Type := T.presheaf.stalk t
  have : IsNoetherianRing O := inferInstanceAs (IsNoetherianRing (T.presheaf.stalk t))
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))) ≫ T.fromSpecStalk t, ?_, ?_⟩
  · have h1 : Flat (T.fromSpecStalk t) := GenericExt.flat_fromSpecStalk T t
    have h2 : Flat (Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact Flat.comp _ _
  · have : IsLocalHom (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))).hom :=
      inferInstanceAs (IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (T.fromSpecStalk t) Spec_closedPoint).trans
      Scheme.fromSpecStalk_closedPoint)

theorem secRatioEq_of_levels {B : Type} [CommRing B] [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {k k' : ℕ} {u v : Sp B ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ e, SecRatioEq L (thick B (maximalIdeal B) e ≫ u) (thick B (maximalIdeal B) e ≫ v) s₁ s₂ t₁ t₂) :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  have top : ∀ w : Sp B ⟶ X, ∃ i : Fin 1 → L.ι, ⊤ ≤ w ⁻¹ᵁ secChart L i := fun w => by
    obtain ⟨i, hi⟩ := exists_chart hL (w (closedPoint B))
    have : closedPoint B ∈ w ⁻¹ᵁ secChart L (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff _).1 this).ge⟩
  obtain ⟨i, hi⟩ := top u
  obtain ⟨i', hi'⟩ := top v
  have key : ∀ (s : H0 L k) (t : H0 L k') (Z : Scheme.{0}) (r : Z ⟶ Sp B) (z : Z),
      gs r z ⊤ ((u.appLE _ ⊤ hi).hom (s.f i) * (v.appLE _ ⊤ hi').hom (t.f i')) =
        secGerm (r ≫ u) z s i * secGerm (r ≫ v) z t i' := fun s t Z r z =>
    (gs_mul r z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (gs_appLE u _ ⊤ hi r z trivial _)
      (gs_appLE v _ ⊤ hi' r z trivial _))
  have E := GlobalTheory.FormalGeneric.fn_ext_germs (maximalIdeal B) (a := (u.appLE _ ⊤ hi).hom (s₁.f i) *
      (v.appLE _ ⊤ hi').hom (t₂.f i')) (b := (u.appLE _ ⊤ hi).hom (s₂.f i) * (v.appLE _ ⊤ hi').hom (t₁.f i'))
    fun e z => (key _ _ _ _ z).trans ((secRatioEq_iff_germ.1 (h e) z i i' (hi trivial) (hi' trivial)).trans
      (key _ _ _ _ z).symm)
  refine secRatioEq_of_exists_germ fun y => ⟨i, i', hi trivial, hi' trivial, ?_⟩
  exact (key s₁ t₂ _ (𝟙 _) y).symm.trans ((congrArg _ E).trans (key s₂ t₁ _ (𝟙 _) y))

theorem exists_generic_mem {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) [Flat f]
    (W : Y.Opens) {y : Y} (hy : y ∈ W) : ∃ a : (pullback f (jK R) :), pullback.fst f (jK R) a ∈ W := by
  let ξ : Sp R := jK R (closedPoint (FractionRing R))
  have hξ : ξ ⤳ f y := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h1 : algebraMap R (FractionRing R) r ∈ maximalIdeal (FractionRing R) := hr
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]
    exact Ideal.zero_mem _
  obtain ⟨y', h1, h2⟩ := Flat.generalizingMap f hξ
  have : y' ∈ Set.range (pullback.fst f (jK R)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨_, h2.symm⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha ▸ h1.mem_open W.isOpen hy⟩

theorem isDominant_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [Flat f] (y : Y) : IsDominant f := by
  obtain ⟨y', -, h2⟩ := Flat.generalizingMap f (genericPoint_specializes (f y))
  refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨y', h2⟩) ?_⟩
  exact dense_iff_closure_eq.2 (genericPoint_spec X)

theorem exists_formal_pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G] [LocallyOfFiniteType G.hom]
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (hb : ∀ e, IsMonHom (b e))
    (hc : ∀ e, thickMap R (maximalIdeal R) e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R (maximalIdeal R) e G)
    {L : LB G.left} (hL : L.IsLB) :
    ∃ (Y : Over (Sp R)) (x₁ x₂ : Y ⟶ G) (Φ : (Y ⟶ G) → (Y ⟶ G)), Nonempty Y.left ∧ Flat (lift x₁ x₂).left ∧
      (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Y ⟶ G) (k k' : ℕ) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'),
        (∀ e, SecRatioEq L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left
          s₁ s₂ t₁ t₂) → SecRatioEq L (Φ x).left x.left s₁ s₂ t₁ t₂ := by
  have : LocallyOfFiniteType (G ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  let o : 𝟙_ (Over (Sp R)) ⟶ G ⊗ G := lift 1 1
  obtain ⟨B, _, _, hB, q, hq, hqt⟩ := exists_complete_point (G ⊗ G).left (o.left (closedPoint R))
  have hs : (q ≫ (G ⊗ G).hom) (closedPoint B) ∈ Set.range (thick R (maximalIdeal R) 0) := by
    have h1 : (q ≫ (G ⊗ G).hom) (closedPoint B) = closedPoint R :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (G ⊗ G).hom hqt).trans
        ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun g => g (closedPoint R)) (Over.w o))))
    exact ⟨_, (GlobalTheory.adicLevelι_closedPoint (maximalIdeal.isMaximal R).ne_top 0).trans h1.symm⟩
  obtain ⟨Φ, hΦ, hr⟩ := _root_.GlobalTheory.exists_mul_map_points_of_thickEndo R (maximalIdeal R) G b hb hc B (q ≫ (G ⊗ G).hom) hs
  let q' : Over.mk (q ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk q rfl
  refine ⟨Over.mk (q ≫ (G ⊗ G).hom), q' ≫ fst G G, q' ≫ snd G G, Φ, ⟨closedPoint B⟩, ?_, hΦ,
    fun x k k' s₁ s₂ t₁ t₂ h => secRatioEq_of_levels hL fun e => ?_⟩
  · rw [lift_comp_fst_snd]
    exact hq
  · obtain ⟨r, h1, h2⟩ := hr x e
    have h3 := (h e).comp r
    exact h1 ▸ h2 ▸ h3

theorem exists_generic_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), 1 ≤ N → (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∃ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ ∧ (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' _ b hb N S _ hS hnd
  have := hR.1.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  let F := Over.pullback (jK R)
  let π : (F.obj G).left ⟶ G.left := pullback.fst G.hom (jK R)
  have hA : GlobalTheory.SS.SmConn (F.obj G) := ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom (jK R))),
    inferInstanceAs (IsSeparated (pullback.snd G.hom (jK R))),
    inferInstanceAs (QuasiCompact (pullback.snd G.hom (jK R))),
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (jK R)))⟩
  have := hA.2.1
  have := hA.2.2.2.2
  have hint : IsIntegral (F.obj G).left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (F.obj G).hom
  obtain ⟨m, σ, hσ⟩ := _root_.GlobalTheory.Mum.exists_veryAmpleAlong_unif R (maximalIdeal R) D A G U
  obtain ⟨s₀, y₀, i₀, i₀', -, hy₀⟩ := hnd 4 (by norm_num)
  have ht₀ : ∃ p : (F.obj G).left, π p ∈ nonzeroLocus (S 4 s₀) := by
    refine exists_generic_mem G.hom _ (y := (fstG (maximalIdeal R) 0 G).left y₀) ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i₀', (Scheme.preimage_basicOpen _ _).ge hy₀⟩
  obtain ⟨Y, x₁, x₂, Φ, ⟨y⟩, hfl, hΦ, hrat⟩ := exists_formal_pair G b hb.1 hb.2.1 U.LG.isLB
  have hπ : ∀ x : Y ⟶ G, (F.map x).left ≫ π = pullback.fst Y.hom (jK R) ≫ x.left := fun x =>
    pullback.lift_fst _ _ _
  have hratK : ∀ (x : Y ⟶ G) (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((F.map (Φ x)).left ≫ π)
      ((F.map x).left ≫ π) s₁ s₂ (S k s₁) (S k s₂) := fun x k s₁ s₂ => by
    rw [hπ, hπ]
    exact (hrat x k _ s₁ s₂ _ _ fun e => hS k e s₁ s₂).comp _
  have hflK : Flat (lift (F.map x₁) (F.map x₂)).left := by
    rw [← Functor.OplaxMonoidal.lift_δ, Over.comp_left]
    have h1 : Flat (F.map (lift x₁ x₂)).left := MorphismProperty.overPullbackMap (P := @Flat) (jK R) _ hfl
    have h2 : IsIso (Functor.OplaxMonoidal.δ F G G).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Functor.OplaxMonoidal.δ F G G)))
    infer_instance
  have hYfl : Flat Y.hom := by
    have : Flat (G ⊗ G).hom := inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
    rw [← Over.w (lift x₁ x₂)]
    infer_instance
  obtain ⟨yK, -⟩ := exists_generic_mem Y.hom ⊤ (y := y) trivial
  have : Smooth (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (Smooth (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : GeometricallyConnected (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (GeometricallyConnected (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : IsIntegral (F.obj G ⊗ F.obj G).left := by
    have := GlobalTheory.isNormalScheme_of_smooth (S := Sp (FractionRing R)) (F.obj G).hom
    have : IsLocallyNoetherian (F.obj G).left := LocallyOfFiniteType.isLocallyNoetherian (F.obj G).hom
    exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (fst (F.obj G) (F.obj G)).left
  have hdom : IsDominant (lift (F.map x₁) (F.map x₂)).left := isDominant_of_flat _ yK
  have hfl₁ : Flat (F.map x₁).left := by
    rw [← lift_fst (F.map x₁) (F.map x₂), Over.comp_left]
    infer_instance
  have hdom₁ : IsDominant (F.map x₁).left := isDominant_of_flat _ yK
  obtain ⟨V, j, f, hj, hV, hf⟩ := _root_.GlobalTheory.Mum.exists_morphism_of_secRatio (FractionRing R) (F.obj G) G.left U.LG.L U.LG.isLB π 4 _ m σ hσ s₀
    (S 4 s₀) (fun i => S 4 (σ i)) ht₀ (F.obj Y) (F.map x₁) (F.map (Φ x₁)) hdom₁ fun i => hratK x₁ 4 _ _
  have hpt : ∀ (x : Y ⟶ G) (Z : Over (Sp (FractionRing R))) (w : Z ⟶ F.obj Y) (u : Z ⟶ V),
      u ≫ j = w ≫ F.map x → u ≫ f = w ≫ F.map (Φ x) := fun x Z w u e => hf Z u _ fun i => by
    rw [e, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    exact (hratK x 4 _ _).comp _
  have hadd := _root_.GlobalTheory.Mum.mul_of_isDominant_pair (FractionRing R) (F.obj G) hA V j f hj (F.obj Y) _ _ _ _ hdom (hpt x₁) (hpt x₂)
    (by rw [← Functor.map_mul, ← Functor.map_mul, ← hΦ]; exact hpt (x₁ * x₂))
  obtain ⟨φ, hφ, hjφ⟩ := _root_.GlobalTheory.GenericHomField.exists_monHom_extension_of_field (FractionRing R) (F.obj G) (F.obj G) V hA hA j f hj hV hadd
  refine ⟨φ, hφ, fun k s₁ s₂ => ?_⟩
  let Z : Over (Sp (FractionRing R)) := Over.mk (pullback.fst (F.map x₁).left j.left ≫ (F.obj Y).hom)
  let w : Z ⟶ F.obj Y := Over.homMk (pullback.fst (F.map x₁).left j.left) rfl
  let u : Z ⟶ V := Over.homMk (pullback.snd (F.map x₁).left j.left) (by
    have e := congrArg (· ≫ (F.obj G).hom) (pullback.condition (f := (F.map x₁).left) (g := j.left))
    simp only [Category.assoc, Over.w] at e
    exact e.symm)
  have huw : u ≫ j = w ≫ F.map x₁ := Over.OverMorphism.ext pullback.condition.symm
  have e : (w ≫ F.map x₁) ≫ φ = w ≫ F.map (Φ x₁) := by rw [← huw, Category.assoc, hjφ, hpt x₁ Z w u huw]
  obtain ⟨z⟩ : Nonempty Z.left := by
    obtain ⟨v⟩ := hV
    obtain ⟨p, v', hp⟩ := (F.map x₁).left.denseRange.exists_mem_open (IsOpenImmersion.isOpen_range j.left)
      ⟨_, v, rfl⟩
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback p v' hp.symm
    exact ⟨z⟩
  have : Flat (w ≫ F.map x₁).left :=
    inferInstanceAs (Flat (pullback.fst (F.map x₁).left j.left ≫ (F.map x₁).left))
  have := isDominant_of_flat (w ≫ F.map x₁).left z
  refine SecRatioEq.of_isDominant (Y := (F.obj G).left) (w ≫ F.map x₁).left ?_
  have e' : (w ≫ F.map x₁).left ≫ φ.left ≫ π = w.left ≫ (F.map (Φ x₁)).left ≫ π := by
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
  have h3 := (hratK x₁ k s₁ s₂).comp w.left
  rw [← e', ← Category.assoc w.left] at h3
  exact h3

end GlobalTheory.Mum.GenericRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTriv
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidHom

theorem exists_hom_of_triv : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  intro k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hA
  let AV : GlobalTheory.AV.AbVar k := { X := A, ab := hA, dim := g, smooth := hg }
  obtain ⟨c, L, hL, hamp, -⟩ := GlobalTheory.AV.exists_isAmpleCls k AV
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp
  obtain ⟨a₁, -⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, -⟩ := hd.univ A P hP a₁
  have hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB := pull_isLB hd.isLB _
  have e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x) := (cls_eq_iff hP hE).2 hx
  refine ⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩
  apply hd.eq_one
  rw [triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]
  have u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]
  rw [u1]
  exact evc_one_right hP h₂ _

end GlobalTheory.BirigidHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIntTraceSectionTuple
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TraceHom

theorem trace_homog : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (q : ℕ) (w : K), (∀ l, IsIntegral (ratR x l) (w / x l ^ q)) →
    ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) = aeval (fun l => x l / x 0) T := by
  intro K _ _ D x hx hind hfd q w hint
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  have hyF : ∀ j, y j ∈ ratF x := fun j => Subfield.subset_closure ⟨j, rfl⟩
  have hzF : ∀ l k, x k / x l ∈ ratF x := by
    intro l k
    have e : ∀ k, x k / x 0 ∈ ratF x := by
      intro k
      refine Fin.cases ?_ (fun i => hyF i) k
      rw [div_self (hx 0)]; exact one_mem _
    have : x k / x l = (x k / x 0) / (x l / x 0) := by field_simp [hx 0, hx l]
    rw [this]; exact div_mem (e k) (e l)
  set t : K := (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) with htdef

  obtain ⟨f₀, hf₀, hft₀⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x 0) (hzF 0) _ (hint 0)
  have hz0 : ∀ k, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = x k / x 0 := by
    intro k
    refine Fin.cases ⟨1, ?_⟩ (fun i => ⟨X i, by simp [y]⟩) k
    rw [map_one, div_self (hx 0)]
  obtain ⟨T₀, hT₀⟩ := _root_.GlobalTheory.mem_polyring_of_integral_closure_range y hind t (Algebra.trace (ratF x) K (w / x 0 ^ q)).2 _ hz0 f₀ hf₀ hft₀

  have hdeg : T₀.totalDegree ≤ q := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [MvPolynomial.eq_C_of_isEmpty T₀, totalDegree_C]; exact Nat.zero_le _
    · set j : Fin D := ⟨0, hD⟩
      have hyj : y j ≠ 0 := div_ne_zero (hx _) (hx 0)
      obtain ⟨f₁, hf₁, hft₁⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x j.succ) (hzF j.succ) _ (hint j.succ)
      have hc : (⟨(x 0 / x j.succ) ^ q, pow_mem (hzF _ 0) q⟩ : ratF x) • (w / x 0 ^ q) = w / x j.succ ^ q := by
        rw [Subfield.smul_def]; simp only [smul_eq_mul, div_pow]; field_simp [hx 0, hx j.succ] <;> ring
      have htr : (Algebra.trace (ratF x) K (w / x j.succ ^ q) : K) = aeval y T₀ / y j ^ q := by
        rw [← hc, LinearMap.map_smul, smul_eq_mul, Subfield.coe_mul, ← htdef, hT₀]
        simp only [y, j, div_pow]; field_simp [hx 0, hx _] <;> ring
      rw [htr] at hft₁
      refine _root_.GlobalTheory.totalDegree_le_of_integral_at_infinity y hind j hyj T₀ q _ ?_ f₁ hf₁ hft₁
      intro k
      refine Fin.cases ⟨1, 1, by simp, ?_⟩ (fun i => ⟨1, X i, ?_, ?_⟩) k
      · simp only [y, pow_one, map_one]; field_simp [hx 0, hx _]
      · simp [totalDegree_X]
      · simp only [y, pow_one, aeval_X]; field_simp [hx 0, hx _]
  obtain ⟨T, hT, hTa⟩ := _root_.GlobalTheory.exists_isHomogeneous_dehomogenize T₀ q hdeg
  refine ⟨T, hT, ?_⟩
  rw [hTa K _ (div_self (hx 0)), ← hT₀]

end GlobalTheory.HSAmp.TraceHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafPullbackEqDivisorOfApprox
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc

theorem exists_idealSheaf_comap_eq_of_approx : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → (∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ x : M.Z, π x = z → IsClosed ({x} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ ∧ ∀ e : ℕ, ∃ F ∈ M₁.O z, (∀ f, EqAt M D x f → ‖M.val (gPt p ≫ y₀) F‖ = ‖M.val (gPt p ≫ y₀) f‖) ∧ ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ J : M₁.Z.IdealSheafData, J.comap π = D.idealSheaf := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU hUD hyp
  refine ⟨D.idealSheaf.map π, le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_⟩
  haveI : QuasiCompact M.s := M.qc
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  refine GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints M.Z D _ ?_
  intro x hx
  have hz : IsClosed ({π x} : Set M₁.Z) := by
    have := π.isClosedMap _ hx
    simpa [Set.image_singleton] using this
  obtain ⟨p, hp, y₀, hcen, hF⟩ := hyp (π x) hz x rfl hx
  obtain ⟨i, hi⟩ := D.exists_mem x
  have hEq : EqAt M D x (valF M.pt (D.U i) (D.f i)) := ⟨i, hi, rfl⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.generates_of_close_localEquation_classicalPoint o Ω M₁ M π hπ U D hUD x p y₀ hcen _ hEq
  obtain ⟨e, he⟩ := _root_.GlobalTheory.FibreCorr.exists_correction o Ω M₁ M π hπ hprop hn₁ hn U D hU hUD (π x) hz k
  obtain ⟨F, hFm, h1, h2⟩ := hF e
  obtain ⟨G, b, hFGb, hfib, hb⟩ := he ⟨F, hFm⟩ h2
  have hGf : (G : Ω) / valF M.pt (D.U i) (D.f i) ∈ M.O x := hfib x rfl _ hEq
  have hnorm : ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) (valF M.pt (D.U i) (D.f i))‖ := by
    rw [← hFGb]; exact h1 _ hEq
  obtain ⟨hG0, hfG⟩ := hk G b hnorm hb hGf
  obtain ⟨V, g, hzV, hg, hV⟩ := _root_.GlobalTheory.Poinc.spread_regular_div o Ω M₁ M π hπ hprop D (π x) G G.2 hfib
  have hgI := _root_.GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div o Ω M₁ M π hπ hprop D V g (by rw [hg]; exact hV)
  obtain ⟨W, h, hxW, hW⟩ := GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point o Ω M₁ M π hπ D V g x i hzV hi hgI (by rw [hg]; exact hG0) (by rw [hg]; exact hfG)
  exact ⟨W, i, h, hxW, hW⟩


end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNearOfClosureShort
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem span_intCast_image_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] (T : Set (ι → ℤ))
    (hT : AddSubgroup.closure T = ⊤) :
    Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) = ⊤ := by
  have h : ∀ z : ι → ℤ, (fun i => (z i : ℝ)) ∈
      Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) := by
    intro z
    have hz : z ∈ AddSubgroup.closure T := by rw [hT]; trivial
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero =>
      have : (fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0 := by ext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      have : (fun i => (((u + v) i : ℤ) : ℝ)) = (fun i => (u i : ℝ)) + fun i => (v i : ℝ) := by
        ext i; simp
      rw [this]; exact Submodule.add_mem _ hu hv
    | neg u _ hu =>
      have : (fun i => (((-u) i : ℤ) : ℝ)) = -(fun i => (u i : ℝ)) := by
        ext i; simp
      rw [this]; exact Submodule.neg_mem _ hu
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have := h (fun j => if i = j then 1 else 0)
  convert this using 2 with j
  split_ifs <;> simp

theorem exists_int_near_of_closure_short :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ : ℝ), 0 ≤ ρ → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → ∀ x : ι → ℝ, ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ (Fintype.card ι * ρ) ^ 2 := by
  intro ι _ _ A hA T ρ hρ hT hz x
  classical
  set B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' A with hB
  have hBq : ∀ v : ι → ℝ, ∑ i, ∑ j, A i j * v i * v j = B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpos : ∀ v : ι → ℝ, 0 ≤ B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply']
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg v
  have hsymm : ∀ u v : ι → ℝ, B u v = B v u := by
    intro u v
    rw [hB, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : A j i = A i j := by simpa using hA.isHermitian.apply i j
    rw [this]; ring
  obtain ⟨b, hbS, hspan, hli⟩ :=
    exists_linearIndependent ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)
  rw [span_intCast_image_eq_top T hT] at hspan
  have hfin : b.Finite := hli.setFinite
  haveI : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ Fintype.card ι := by
    simpa using hli.fintype_card_le_finrank
  have hx : x ∈ Submodule.span ℝ (Set.range ((↑) : b → ι → ℝ)) := by
    rw [Subtype.range_coe, hspan]; trivial
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  choose w hwT hw using fun a : b => hbS a.2
  have hq : ∀ a : b, B a a ≤ ρ ^ 2 := by
    intro a
    rw [← hBq, ← hw a]
    exact hz _ (hwT a)
  have hq2 : ∀ a c : b, B a c ≤ ρ ^ 2 := by
    intro a c
    have h1 := hpos ((a : ι → ℝ) - c)
    simp only [map_sub, LinearMap.sub_apply] at h1
    have := hsymm c a
    have := hq a
    have := hq c
    linarith
  refine ⟨∑ a : b, ⌊t a⌋ • w a, ?_⟩
  have hy : (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ)) =
      ∑ a : b, Int.fract (t a) • (a : ι → ℝ) := by
    ext i
    rw [← ht]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : (w a i : ℝ) = (a : ι → ℝ) i := congrFun (hw a) i
    rw [this, Int.fract]; ring
  have := hBq (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ))
  rw [this, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  calc _ ≤ ∑ _a : b, ∑ _c : b, ρ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        try rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := Int.fract_nonneg (t a)
        have h2 := (Int.fract_lt_one (t a)).le
        have h3 := Int.fract_nonneg (t c)
        have h4 := (Int.fract_lt_one (t c)).le
        have h5 := hq2 a c
        have h6 := hq2 c a
        have h7 : 0 ≤ ρ ^ 2 := by positivity
        have h8 := mul_nonneg h1 h3
        have h9 : Int.fract (t a) * Int.fract (t c) ≤ 1 := mul_le_one₀ h2 h3 h4
        nlinarith [mul_le_mul_of_nonneg_left h5 h8, mul_le_mul_of_nonneg_left h6 h8,
          mul_le_mul_of_nonneg_right h9 h7]
    _ = (Fintype.card b * ρ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by
        gcongr

end GlobalTheory.HSAmp
end

