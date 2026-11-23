module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenCondition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_open_forall {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (p : Cpt ξ) {I : Type} [Finite I]
    (P : I → Cpt ξ → Prop) (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  classical
  have := Fintype.ofFinite I
  have key : ∀ s : Finset I, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i ∈ s, P i q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨U, hU, HU⟩ := ih
      obtain ⟨V, hV, HV⟩ := h a
      refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact HV q hq.2
      · exact HU q hq.1 i hi
  obtain ⟨U, hU, HU⟩ := key Finset.univ
  exact ⟨U, hU, fun q hq i => HU q hq i (Finset.mem_univ i)⟩

theorem exists_open_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  obtain ⟨U, hU, HU⟩ := exists_open_forall p (fun (j : Fin n) (q : Cpt ξ) => (f j : Ω) ∈ regAt ξ q)
    fun j => exists_open_mem_regAt ξ p _ (f j).2
  refine ⟨U, hU, fun q hq => ?_⟩
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (⟨(f j : Ω), HU q hq j⟩ : regAt ξ q) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_span_field_of_mem_span_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type}
    [AddCommGroup E] [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) : e ∈ Submodule.span Ω (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (f j : Ω) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_span_and_nhd : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  intro X G _ _ _ Ω _ ξ E _ _ M p g b hb
  obtain ⟨R, _, x, hx, F, _, _, MR, n, bR, hp⟩ := exists_chart G p.1
  have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR bR ξ M φ hφ
  have hc : ∀ q : Cpt ξ, q.1 ∈ x.opensRange → M.lat.IsFrameAt c q := by
    intro q hq
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  have hbc : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range c) :=
    hb.2.symm.trans (hc p hp).2
  have hbi : ∀ i, b i ∈ Submodule.span (regAt ξ p) (Set.range c) := fun i => by
    rw [← hbc]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcj : ∀ j, c j ∈ Submodule.span (regAt ξ p) (Set.range b) := fun j => by
    rw [hbc]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨top_le_iff.1 (hsp.ge.trans (Submodule.span_le.2 ?_)), ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact mem_span_field_of_mem_span_regAt ξ p b _ (hcj j)
  obtain ⟨U, hU, HU⟩ := exists_open_forall p
    (fun (i : Fin g) (q : Cpt ξ) => b i ∈ Submodule.span (regAt ξ q) (Set.range c))
    fun i => exists_open_mem_span ξ p c _ (hbi i)
  obtain ⟨V, hV, HV⟩ := exists_open_forall p
    (fun (j : Fin n) (q : Cpt ξ) => c j ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun j => exists_open_mem_span ξ p b _ (hcj j)
  refine ⟨x.opensRange ⊓ (U ⊓ V), ⟨hp, hU, hV⟩, fun q hq => ⟨hb.1, ?_⟩⟩
  rw [(hc q hq.1).2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact HV q hq.2.2 j
  · rintro _ ⟨i, rfl⟩
    exact HU q hq.2.1 i

end GlobalTheory.CompanionTheory.Ar.LieVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (φ : R →+* R') :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ)
      = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_epsMul (φ : R →+* R') (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_one_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact comp_one u

theorem comp_mul_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (p q : X ⟶ M) :
    u ≫ (p * q) = (u ≫ p) * (u ≫ q) := by
  exact comp_mul u p q

def pullEps (φ : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap φ)) (by
    simp only [Over.mk_hom, epsAt]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap])

def pullPt (φ : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap φ ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap φ) rfl

theorem isTanAt_pull (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap φ ≫ x) (pullEps φ x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [← comp_one_over (pullPt φ x), Over.comp_left, Over.comp_left, ← hv]
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫ spMap (dualMap φ)
      = spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_dualMap]
  simp only [pullEps, pullPt, Over.homMk_left]
  rw [reassoc_of% key]

theorem exists_linear (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S)
    {E E₀ : Type} [AddCommGroup E] [Module R E] [AddCommGroup E₀] [Module R' E₀] [Module R E₀]
    (hs : ∀ (a : R) (e : E₀), a • e = φ a • e) (M : LieModel G x E)
    (M₀ : LieModel G (spMap φ ≫ x) E₀) :
    ∃ j : E →ₗ[R] E₀, ∀ e, M₀.pt (j e) = pullEps φ x ≫ M.pt e := by
  choose j hj using fun e => M₀.onto _ (isTanAt_pull G φ x (M.pt e) (M.tan e))
  refine ⟨{ toFun := j, map_add' := ?_, map_smul' := ?_ }, hj⟩
  · intro e e'
    apply M₀.inj
    rw [M₀.add, hj, hj, hj, M.add, comp_mul_over]
  · intro c e
    apply M₀.inj
    rw [RingHom.id_apply, hs, hj]
    apply Over.OverMorphism.ext
    rw [M₀.smul, hj, Over.comp_left, Over.comp_left, M.smul]
    simp only [pullEps, Over.homMk_left, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp_epsMul]

def transport {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (f : E' ≃ₗ[R] E) : LieModel G x E' where
  pt e := M.pt (f e)
  tan e := M.tan _
  inj := M.inj.comp f.injective
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto v hv
    exact ⟨f.symm e, by simpa using he⟩
  add e e' := by simp only [map_add (f := _)]; exact M.add _ _
  smul c e := by simp only [map_smul]; exact M.smul _ _


open GroundTheory.Heights₂.Heights in
theorem lieModel_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  intro S G _ _ _ L _ _ z V _ _ M σ
  classical
  let _ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  obtain ⟨E₀, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  let _ : Module (𝓞 L) E₀ := Module.compHom E₀ (σ.comp (algebraMap (𝓞 L) L))
  have _ : IsScalarTower (𝓞 L) ℂ E₀ := ⟨fun a b e => by
    show ((σ.comp (algebraMap (𝓞 L) L)) a * b) • e = (σ.comp (algebraMap (𝓞 L) L)) a • b • e
    rw [mul_smul]⟩
  obtain ⟨j, hj⟩ := exists_linear G (σ.comp (algebraMap (𝓞 L) L)) z (fun a e => rfl) M M₀
  have hl : ∀ e, M.Lifts (algebraMap (𝓞 L) ℂ) (𝟙 G.left) e (M₀.pt (j e)) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
    rw [hj e, Over.comp_left, Category.comp_id]
    rfl
  have hb := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange S G (𝓞 L) ℂ z V E₀ M M₀ j hl
  let f : GroundTheory.Heights₂.Heights.Fibre σ V ≃ₗ[ℂ] E₀ := hb.equiv
  refine ⟨transport M₀ f, fun e => ?_⟩
  have hf : f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
    show hb.equiv ((1 : ℂ) ⊗ₜ[𝓞 L] e) = j e
    rw [IsBaseChange.equiv_tmul, one_smul]
  unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
  show (M₀.pt (f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ 𝟙 _ = _
  rw [hf, hj e, Over.comp_left, Category.comp_id]
  rfl

end GlobalTheory.CompanionTheory.Ar.LieSigma
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieRank

variable {S : Scheme.{0}}

theorem dualMap_apply {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (a : DualNumber R) :
    dualMap c a = TrivSqZeroExt.inl (c a.fst) + TrivSqZeroExt.inr (c a.snd) := rfl

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  change (dualMap c a).fst = c a.fst
  simp [dualMap_apply]

theorem dualMap_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => ?_
  change dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) =
    TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)
  ext <;> simp [dualMap_apply, mul_comm]

def epsPull {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) :
    epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_algebraMap c))

theorem one_left_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) :
    (1 : Over.mk (spMap c ≫ x) ⟶ G).left = spMap c ≫ (1 : Over.mk x ⟶ G).left := by
  have h := MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)
  exact (congrArg (fun k => k.left) h).symm

theorem isTanAt_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G (spMap c ≫ x) (epsPull c x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [one_left_pull, ← hv]
  change _ ≫ spMap (dualMap c) ≫ v.left = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (by
    refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (fst_comp_dualMap c) a))

theorem epsPull_comp_left (G : Over S) {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : (epsPull c x ≫ v).left = spMap (dualMap c) ≫ v.left := by
  simp [epsPull]

theorem exists_lift (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (x : Sp R ⟶ S) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] [Module R E']
    [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ j : E →ₗ[R] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := by
  have hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e := fun e =>
    M'.onto _ (isTanAt_pull G _ x _ (M.tan e))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply M'.inj
    rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) a, f (r • a) = r • f a := fun r a => by
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)
  have hl : ∀ e, ((M'.pt (f e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    rw [hf, Category.comp_id, epsPull_comp_left]
  exact ⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩

theorem finrank_of_isBaseChange {A F : Type} [CommRing A] [Field F] [Algebra A F] {E E' : Type} [AddCommGroup E]
    [Module A E] [AddCommGroup E'] [Module F E'] [Module A E'] [IsScalarTower A F E'] [Module.Finite A E]
    [Module.Projective A E] (j : E →ₗ[A] E') (hj : IsBaseChange F j) (p : PrimeSpectrum F) :
    Module.finrank F E' = Module.rankAtStalk E (PrimeSpectrum.comap (algebraMap A F) p) := by
  rw [← Module.rankAtStalk_baseChange (S := F) (M := E) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (LinearEquiv.finrank_eq hj.equiv).symm

theorem finrank_eq_of_isBaseChange_fractionRing {D L : Type} [CommRing D] [IsDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] {E E' : Type} [AddCommGroup E] [Module D E] [AddCommGroup E'] [Module L E'] [Module D E']
    [IsScalarTower D L E'] (j : E →ₗ[D] E') (hj : IsBaseChange L j) :
    Module.finrank D E = Module.finrank L E' := by
  have : IsLocalizedModule (nonZeroDivisors D) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj
  have h1 := IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j
  have h2 := IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl
  simp only [Module.finrank, h1, h2]

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar.LieRank

theorem exists_factor {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) [IsOpenImmersion i₀]
    (y : Sp F ⟶ X) (h : genPt y ∈ Set.range i₀) : ∃ φ : A →+* F, spMap φ ≫ i₀ = y := by
  have hr : Set.range y ⊆ Set.range i₀ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hp]
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr :=
    Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac i₀ y hr

theorem genPt_comp {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) (φ : A →+* F) :
    genPt (spMap φ ≫ i₀) = i₀ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := rfl

theorem finrank_fieldPt {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {A F : Type} [CommRing A] [Field F]
    (i₀ : Sp A ⟶ S) {E Li : Type} [AddCommGroup E] [Module A E] [AddCommGroup Li] [Module F Li]
    (MA : LieModel G i₀ E) (φ : A →+* F) (M : LieModel G (spMap φ ≫ i₀) Li) :
    Module.finrank F Li = Module.rankAtStalk E (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := by
  obtain ⟨hf, hp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S G A i₀ E MA
  letI : Algebra A F := φ.toAlgebra
  letI : Module A Li := Module.compHom Li φ
  haveI : IsScalarTower A F Li := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := exists_lift G i₀ MA M
  exact finrank_of_isBaseChange j (_root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange S G A F i₀ E Li MA M j hj) _

theorem finrank_eq_of_specializes {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : Sp F₁ ⟶ X) (y₂ : Sp F₂ ⟶ X) (h : genPt y₁ ⤳ genPt y₂)
    {E₁ E₂ : Type} [AddCommGroup E₁] [Module F₁ E₁] [AddCommGroup E₂] [Module F₂ E₂]
    (M₁ : LieModel G y₁ E₁) (M₂ : LieModel G y₂ E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial
  have h₁U : genPt y₁ ∈ U := h.mem_open U.isOpen hqU
  have hr : Set.range hU.fromSpec = (U : Set X) := hU.range_fromSpec
  obtain ⟨φ₁, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)
  obtain ⟨φ₂, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)
  obtain ⟨E, _, _, ⟨MA⟩⟩ := lieModel_exists X G Γ(X, U) hU.fromSpec
  obtain ⟨hf, hp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective X G Γ(X, U) hU.fromSpec E MA
  haveI := Module.finitePresentation_of_projective Γ(X, U) E
  rw [finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]
  rw [genPt_comp, genPt_comp] at h
  have hs := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h
  exact (hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finrank_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  intro X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G z MB M'
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing j (_root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]
  exact (LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm

end GlobalTheory.CompanionTheory.Ar
end
end

