module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOpensSmoothOfRelativeDimensionOfFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperFlatNearFibre

theorem exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have hz : z ∈ s.smoothLocus := by
    refine GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
    exact GlobalTheory.VeryDenseFibres.smooth_fiber_of_smooth_fiber s t w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (s.smoothLocus.ι ≫ s) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (s.smoothLocus.ι ≫ s) t g (by simpa using h2) ⟨z, hz⟩ w hw
  let j := W.ι ≫ s.smoothLocus.ι
  refine ⟨j.opensRange, ⟨⟨⟨z, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : j.opensRange.ι ≫ s = j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + g)
      (j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s)) := inferInstance
  rw [e]
  simpa using h3

theorem smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2

theorem exists_away_smoothOfRelativeDimension :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩

end GlobalTheory.ProperFlatNearFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleMap

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gm r z (LB.wchart L φ j) (u.s j) = gm r z ⊤ a * gm r z (LB.wchart L φ j) (u'.s j) := by
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      gm r z (LB.wchart L φ j) (u.s j * (u'.s j)⁻¹) =
        gm r z (LB.wchart L φ j) (u.s j) * (gm r z (LB.wchart L φ j) (u'.s j))⁻¹ := fun Z r z j =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (φ k y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp⟩) (fun j => u.s j * (u'.s j)⁻¹)
    (fun j j' y hy => by
      rw [hv, hv, gen_trans hu (𝟙 Y) y hy.1 hy.2, gen_trans hu' (𝟙 Y) y hy.1 hy.2, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨a, fun Z r z j hj => ?_⟩
  rw [← gm_res r z le_top hj a, ha j, hv, inv_mul_cancel_right]

theorem exists_rigidified {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) (e : S ⟶ X) (e' : S' ⟶ X') (p : X' ⟶ S')
    (hp : e' ≫ p = 𝟙 _) (f : S' ⟶ S) (he : e' ≫ F = f ≫ e) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) ρ' ρ f := by
  obtain ⟨ρ₀, h₀, H⟩ := DegPull.exists_pmaps hw hL hL' (K := PUnit) (φ' := fun _ => e') (φ := fun _ => e)
    (ε := fun _ => 1) f (fun _ => he) ρ hρ
  obtain ⟨a, ha⟩ := exists_ratio hL' h₀ hρ'
  let w' : LB.Iso L' (L.pull F) := ⟨fun j => res le_top (pullU p ⊤ a) * w.s j⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ a * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _
      (show r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k from ⟨mem_pull.2 hj, hk⟩) _).trans
        (gm_pull r p z ⊤ trivial a)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [key Z r z j k hj hk, key Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · rw [H Z r z j k hj hk, ha Z r z k (Set.mem_iInter.2 hk), Fintype.prod_unique, Fintype.prod_unique,
      key Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id, zpow_one, zpow_one,
      ← _root_.mul_assoc, mul_comm (gm r z ⊤ a)]

theorem pmaps_cubical {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  obtain ⟨a, ha⟩ := exists_ratio L'.isLB ht c'.isGen
  have a1 : a = 1 := rigid a fun y => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' L'.isLB y
    let o : 𝟙_ (Over S') ⟶ G' := 1
    have e := DegPull.pmaps_val hψ H (lift o (lift o o)).left y hJ hJ'
    have q : (lift o (lift o o)).left ≫ (cubeMapOf gp).F3 =
        (lift (pushHom gp _ o) (lift (pushHom gp _ o) (pushHom gp _ o))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    have e₁ : cubV c y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by
      rw [map_one]
      exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
    have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
    have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
    have e₄ := ha _ (lift o (lift o o)).left y _ (hJ'.mem (thφ G' (x3 G')) _)
    have e₅ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) e₂ (e₄.trans (congrArg _ e₃))))
    simp only [o, _root_.mul_one, mul_inv_cancel, inv_mul_cancel_right, mul_inv_cancel_right, _root_.one_mul, inv_mul_cancel] at e₅
    exact e₅.symm
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, ha Z r z q (Set.mem_iInter.2 hq), a1, map_one, _root_.one_mul]

end TripleMap

theorem exists_sabMap_of_lbIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (φ : t'.G.left ⟶ t.G.left), (IsReduced X' ∧ genericPoints X' ⊆ abLocus t'.G) → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ ν : SABMap t' t f, ν.φ = φ := by
  intro E _ _ _ H X X' t t' f φ ⟨hr, hab⟩ gp hact ⟨w, hw⟩
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have sm := t'.semi.smooth
  have gc := t'.semi.geomConnected
  have gi := grpObj_geometricallyIntegral_of_smooth X' t'.G
  obtain ⟨s₂, i₂, l₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G t'.G sm sm gi gi
  obtain ⟨s₃, i₃, l₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G (t'.G ⊗ t'.G) sm s₂ gi i₂
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over X') ⟶ t'.G) (lift (1 : 𝟙_ (Over X') ⟶ t'.G) (1 : 𝟙_ (Over X') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  refine Units.ext (eq_one_of_appLE_section_eq_one X' (G3 t'.G) o.left (Over.w o) s₃ i₃
    ⟨hr, fun x hx => l₃ ⟨hab hx, l₂ ⟨hab hx, hab hx⟩⟩⟩ ⊤ a.val le_rfl ?_)
  exact (congrArg (fun q => q.hom a.val) (o.left.appLE_eq_app (U := ⊤))).trans (congrArg Units.val h₁)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmoothNearFibre

open GlobalTheory.VeryDenseFibres

private lemma smoothOfRelativeDimension_pullback_snd_restrict {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (W : Z.Opens)
    (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd s t)) :
    SmoothOfRelativeDimension g (pullback.snd (W.ι ≫ s) t) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _

private lemma smoothOfRelativeDimension_opensRange_ι_comp' {U Z S : Scheme.{0}} (i : U ⟶ Z) [IsOpenImmersion i] (s : Z ⟶ S)
    (g : ℕ) (h : SmoothOfRelativeDimension g (i ≫ s)) :
    SmoothOfRelativeDimension g (i.opensRange.ι ≫ s) := by
  rw [← i.isoOpensRange_inv_comp, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact h

theorem exists_opens_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}} (s : Z ⟶ Spec R)
    [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
  have hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have hF' : Smooth (s.fiberToSpecResidueField (s z)) := by
    rw [hw]
    exact smooth_fiber_of_smooth_fiber s t w hF
  have hz : z ∈ s.smoothLocus := mem_smoothLocus_of_smooth_fiber s z hF'
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext a
    simp
  have h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t) :=
    smoothOfRelativeDimension_pullback_snd_restrict s t _ g h
  obtain ⟨V, hV, hVg⟩ :=
    exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)
  refine ⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩
  apply smoothOfRelativeDimension_opensRange_ι_comp'
  simpa using hVg

theorem smoothOfRelativeDimension_pullback_snd {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  have hb := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
  have key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens,
      p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t) := by
    intro p
    have hc : s (pullback.fst s t p) = t (pullback.snd s t p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨W, hzW, hW⟩ := h _ _ hc
    let e := pullbackRightPullbackFstIso s t W.ι
    let j := e.inv ≫ pullback.snd W.ι (pullback.fst s t)
    have hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t := by
      simp [j, e]
    refine ⟨j.opensRange, ?_, ?_⟩
    · obtain ⟨q, -, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)
      refine ⟨e.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      simpa [j] using hq2
    · rw [← j.isoOpensRange_inv_comp, Category.assoc, hj,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
      exact MorphismProperty.pullback_snd _ _ hW
  choose U hU hP using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP
  rw [eq_top_iff]
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩

theorem exists_smoothOfRelativeDimension_of_isUnit :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  intro R _ _ Z s g K _ x hprop hflat hsm
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := sSup {W : Z.Opens | SmoothOfRelativeDimension g (W.ι ≫ s)}
  have hpt : ∀ w : Sp K, ∀ z : Z, (s z).asIdeal = RingHom.ker x → z ∈ U := by
    intro w z hz
    have hzw : s z = spMap x w := PrimeSpectrum.ext (by rw [hz, spMap_apply_asIdeal])
    obtain ⟨W, hzW, hW⟩ :=
      exists_opens_of_flat (R := CommRingCat.of R) s (spMap x) g hsm z w hzw
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨W, hW, hzW⟩
  let w₀ : Sp K := IsLocalRing.closedPoint K
  let C : Set (Sp R) := s '' (U : Set Z)ᶜ
  have hC : IsClosed C := s.isClosedMap _ U.isOpen.isClosed_compl
  have hp : spMap x w₀ ∈ Cᶜ := by
    rintro ⟨z, hzU, hzp⟩
    apply hzU
    apply hpt w₀ z
    rw [hzp, spMap_apply_asIdeal]
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfC⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hC.isOpen_compl
  refine ⟨f, ?_, ?_⟩
  · intro hf0
    apply hpf
    show f ∈ (spMap x w₀).asIdeal
    rw [spMap_apply_asIdeal]
    exact hf0
  · intro R' _ φ hφ
    apply smoothOfRelativeDimension_pullback_snd
    intro z w hzw
    have hzU : z ∈ U := by
      by_contra hzU
      have hmem : s z ∈ C := ⟨z, hzU, rfl⟩
      apply hfC (PrimeSpectrum.mem_basicOpen _ _ |>.mpr ?_) hmem
      rw [hzw]
      show f ∉ (PrimeSpectrum.comap (CommRingCat.ofHom φ).hom w).asIdeal
      intro hfw
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfw hφ)
    obtain ⟨W, hW, hzW⟩ := TopologicalSpace.Opens.mem_sSup.mp hzU
    exact ⟨W, hzW, hW⟩

end GlobalTheory.SmoothNearFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FderivFnAddLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Uniq

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem mem_dom_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (z : Fin g → ℂ) (l : u.Λ) :
    z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W
  rw [ex_add_lattice]

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) (l : u.Λ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  have h : (fun w => fn u m W f (w + (l : Fin g → ℂ))) = fn u m W f := by
    funext w
    unfold fn
    rw [ex_add_lattice]
  calc fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fun w => fn u m W f (w + (l : Fin g → ℂ))) z :=
        (fderiv_comp_add_right (l : Fin g → ℂ)).symm
    _ = fderiv ℂ (fn u m W f) z := by rw [h]

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW f f', h'.add W hW f f']
    ring
  · intro W hW f f'
    rw [h.mul W hW f f', h'.mul W hW f f']
    ring
  · intro W W' hle hW' f
    rw [h.res W W' hle hW' f, h'.res W W' hle hW' f]
end

theorem ks_unique : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := _root_.GlobalTheory.KS.VertField.exists_differentiableOn_vertical P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := _root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij

end GlobalTheory.KS.Uniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousIdealSectionsOfLineBundlePowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) := by
  first | exact @GlobalTheory.ZV.FormSec.ideal_of_veryAmple | exact GlobalTheory.ZV.FormSec.ideal_of_veryAmple | (intros; apply GlobalTheory.ZV.FormSec.ideal_of_veryAmple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullPointIdentityDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

end GlobalTheory.TorsionFormCompare
end
end

