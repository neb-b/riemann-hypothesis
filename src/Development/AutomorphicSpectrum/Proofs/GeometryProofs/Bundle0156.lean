module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilfun

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

section Frame

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V] {K : Type} [Field K]

theorem valAt_of_isDiffOf {M : LieModel G ξ V} {z : Sp K ⟶ X} (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V)
    (hf : M.IsDiffOf f A) {e : V} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hs, v, hv, hw⟩ := h
  refine ⟨hs, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · change _ ≫ (v ≫ f).left = _
    rw [Over.comp_left, ← Category.assoc, hv.1]
    exact congrArg Over.Hom.left (one_comp f)
  · change (M.pt (A e)).left = _
    rw [hf e, Over.comp_left, hv.2, Over.comp_left, Category.assoc]
  · change (w ≫ f).left = _
    rw [Over.comp_left, hw, Over.comp_left, Category.assoc]

theorem exists_model_of_frame [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ V) (z : Sp K ⟶ X)
    (h : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h⟩ →+* K) (hψ : ∀ a : regAt ξ ⟨_, h⟩, ValAt ξ z (a : Ω) (ψ a)) {g : ℕ}
    (ℓ : Fin g → V) (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) :
    ∃ MY : LieModel G z (Fin g → K), ∀ x : Fin g → regAt ξ ⟨_, h⟩,
      M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i)) := by
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G K z
  obtain ⟨ev, hev, hsm, hsp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ V M K z h F MF hξ inferInstance
  have hmem : ∀ i, ℓ i ∈ M.lat ⟨_, h⟩ := fun i => by
    rw [hℓ.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  let u : Fin g → F := fun i => ev ⟨ℓ i, hmem i⟩
  have hcomb : ∀ x : Fin g → regAt ξ ⟨_, h⟩, comb ℓ x ∈ M.lat ⟨_, h⟩ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hmem i)
  have hevc : ∀ x : Fin g → regAt ξ ⟨_, h⟩, ev ⟨comb ℓ x, hcomb x⟩ = ∑ i, ψ (x i) • u i := by
    intro x
    have e1 : (⟨comb ℓ x, hcomb x⟩ : M.lat ⟨_, h⟩) = ∑ i, x i • (⟨ℓ i, hmem i⟩ : M.lat ⟨_, h⟩) := by
      apply Subtype.ext
      simp [comb]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm (x i) (ψ (x i)) _ (hψ (x i))
  have hle : ⊤ ≤ Submodule.span K (Set.range u) := by
    have hr : Set.range ev ⊆ (Submodule.span K (Set.range u) : Set F) := by
      rintro _ ⟨⟨e, he⟩, rfl⟩
      have he' := he
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨x, rfl⟩ := he'
      have e2 : (∑ i, x i • ℓ i) = comb ℓ x := rfl
      simp only [e2]
      rw [hevc x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hsp]
    exact Submodule.span_le.2 hr
  have hcard : Fintype.card (Fin g) = Module.finrank K F := by
    obtain ⟨_, hU, b', hb'sp, hb'⟩ := (lieLat_isVB_of_smooth X Ω ξ G V M hξ inferInstance).1 ⟨_, h⟩ trivial
    have hfr := hb' ⟨_, h⟩ trivial hU
    have htop : Submodule.span Ω (Set.range ℓ) = ⊤ := by
      rw [eq_top_iff, ← hb'sp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h3 : b' i ∈ M.lat ⟨_, h⟩ := by
        rw [hfr.2]
        exact Submodule.subset_span ⟨i, rfl⟩
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at h3
      obtain ⟨x, hx⟩ := h3
      rw [← hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hg : Module.finrank Ω V = g := by
      rw [← finrank_top, ← htop, finrank_span_eq_card hℓ.1, Fintype.card_fin]
    obtain ⟨R', _, x, hx, F', _, _, MR, n, b, hp⟩ := exists_chart G (centre z)
    have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨a, ha⟩ := exists_lift x z hp
    obtain ⟨β, B, -, -⟩ := basis_tr a x z ha MR MF b
    obtain ⟨c, hli, hsp', -⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω V := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp'.ge), Fintype.card_fin]
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin]
    omega
  let bb : Module.Basis (Fin g) K F := basisOfTopLeSpanOfCardEqFinrank u hle hcard
  refine ⟨lieModelOfEquiv MF bb.equivFun.symm, fun x => ?_⟩
  have e3 : bb.equivFun.symm (fun i => ψ (x i)) = ev ⟨comb ℓ x, hcomb x⟩ := by
    rw [hevc, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [bb]
  change M.ValAt z (comb ℓ x) (MF.pt (bb.equivFun.symm fun i => ψ (x i)))
  rw [e3]
  exact (hev _ _).2 ⟨hcomb x, rfl⟩

theorem isActOf_of_frame {E : Type} [Field E] [NumberField E] (hξ : IsCptGen ξ) {M : LieModel G ξ V} {z : Sp K ⟶ X}
    {h : genPt ξ ⤳ centre z} {ψ : regAt ξ ⟨_, h⟩ →+* K} {g : ℕ} {ℓ : Fin g → V}
    (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) (act : OAct (𝓞 E) G) {ρ : 𝓞 E →+* Module.End Ω V}
    (hact : M.IsActOf act.act ρ) {ρK : 𝓞 E →+* Module.End K (Fin g → K)} (hT : Tied ℓ ψ ρ ρK)
    {MY : LieModel G z (Fin g → K)}
    (hY : ∀ x : Fin g → regAt ξ ⟨_, h⟩, M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i))) :
    MY.IsActOf act.act ρK := by
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ G K z _ MY (𝓞 E) act.act act.hom act.one act.mul act.add
  suffices hq : ρ' = ρK from hq ▸ hρ'
  refine RingHom.ext fun a => (Pi.basisFun K (Fin g)).ext fun i => ?_
  let x : Fin g → regAt ξ ⟨_, h⟩ := Pi.single i 1
  have hx : (fun j => ψ (x j)) = Pi.basisFun K (Fin g) i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [x]
    · simp [x, hj]
  have hmem : ρ a (comb ℓ x) ∈ M.lat ⟨_, h⟩ := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable X Ω ξ G V M (𝓞 E) act ρ hact ⟨_, h⟩ a _ ?_
    rw [hℓ.2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨x', hx'⟩ := hmem
  have hc : comb ℓ x' = ρ a (comb ℓ x) := hx'
  have := act.hom a
  have h1 : M.ValAt z (ρ a (comb ℓ x)) (MY.pt (fun j => ψ (x j)) ≫ act.act a) :=
    valAt_of_isDiffOf (act.act a) (ρ a) (hact a) (hY x)
  have h2 := hY x'
  rw [hc] at h2
  have h3 := h2.unique hξ h1
  rw [← hρ' a] at h3
  have h4 := MY.inj h3
  rw [← hx, ← h4]
  exact (hT a x x' hc.symm).symm

end Frame

theorem tangent_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z K _ y h₁ ψ g ℓ ρK hψ hℓ hT
  have : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨MY, hMY⟩ := exists_model_of_frame Z.gen Z.M (y ≫ Y.j) h₁ ψ hψ ℓ hℓ
  have hY : MY.IsActOf Y.t.act.act ρK := isActOf_of_frame Z.gen hℓ Y.t.act Z.act hT hMY
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  obtain ⟨Mo, hMo⟩ := (LiePull.lieModel_pullback _ _ Y.t.G Y.oF.t.G Y.j Y.m.φ hq K y (Fin g → K)).1 MY
  obtain ⟨MU, hMU⟩ := (LiePull.lieModel_pullback _ _ Xo.univ.t.G Y.oF.t.G (pullback.fst _ _) Y.m0.toSABMap.φ hp
    K y (Fin g → K)).2 Mo
  have hMoAct : ∀ (a : 𝓞 E) (e : Fin g → K), Mo.pt (ρK a e) = Mo.pt e ≫ Y.oF.t.act.act a := by
    intro a e
    apply Over.OverMorphism.ext
    apply hq.1.hom_ext
    · rw [hMo, hY a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m.act, ← Category.assoc, hMo]
    · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]
  refine ⟨MU, MY, fun e => ⟨(Mo.pt e).left, Over.w (Mo.pt e), hMU e, hMo e⟩, hMY, fun a e => ?_, hY⟩
  apply Over.OverMorphism.ext
  rw [← hMU, hMoAct a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m0.act, ← Category.assoc, hMU]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove

def chartPullComp {X Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (h : Z ⟶ Y) :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h where
  idx J := J
  le J y hy := mem_pull.2 (by simpa using mem_pull.1 hy)
  g y i j hi hj := by
    have hi' : h y ∈ (L.pull F).U i := mem_pull.2 (by simpa using mem_pull.1 hi)
    have hj' : h y ∈ (L.pull F).U j := mem_pull.2 (by simpa using mem_pull.1 hj)
    refine (gm_pull_g L (h ≫ F) (𝟙 Z) y i j hi hj).trans ?_
    refine Eq.trans ?_ (gm_pull_g L F h y i j hi' hj').symm
    rw [Category.id_comp]

theorem lbIso_pull {X Y Z : Scheme.{0}} {L' : LB Y} {L : LB X} {F : Y ⟶ X} (H : LBIso L' (L.pull F)) (h : Z ⟶ Y) :
    LBIso (L'.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' h h rfl) (chartPullComp L F h) H

theorem fibreLat_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  intro E _ _ _ H X X' t t' f g Λ _ _ R R' z
  refine ⟨fun ⟨m⟩ => ⟨?_, ?_⟩, fun hP hH hB => ?_⟩
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    obtain ⟨w, hw, -⟩ := m.lin
    obtain ⟨v, hv⟩ := lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ
    have h₁ := pull_isLB t'.PP.isLB φ
    have h₂ := pull_isLB t.PP.isLB (φ ≫ m.cm.F)
    refine ⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv, χ, hpb.comp m.cart,
      GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left
    rw [← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have hp := m.cart.1
    obtain ⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z :=
      ⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    obtain ⟨w, hw', -⟩ := m.lin
    obtain ⟨v, hv⟩ := (lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm
    have h₁ := pull_isLB t'.PP.isLB F
    have h₂ := pull_isLB t.PP.isLB (F ≫ m.cm.F)
    refine ⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv, χ, m.cart.cancel hpb hw,
      GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left
    apply hp.hom_ext
    · have e := hact a p
      simp only [Category.assoc] at e ⊢
      rw [m.act a]
      exact e
    · simp only [Category.assoc]
      rw [Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
    refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
      GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
      fun p => ?_, fun i => i.elim⟩
    · rw [hH]
      exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
    · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
        (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t'.act.act a).left
      rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
        ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
      simp only [Category.assoc]
    · intro x y e
      rw [hP, hP] at e
      exact hinj (star_injective e)
    · show star p ∈ u.Λ ↔ _
      rw [hmem]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hP, hx, star_star]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [hP, star_star]⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgree
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.COrder

theorem order_on_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (α κ : Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → ConstClosed O Ω → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Ω).range) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → 𝓗.DegZero σ (algebraMap O Ω ϖ) → IsLineGenOn (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (α • exteriorPower.ιMulti Ω p v) (κ • exteriorPower.ιMulti Ω q w) (genFibre O ξ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ x : Cpt ξ, OrderAt (detLat (𝓗.quot σ) u) (α / κ) (algebraMap O Ω ϖ) M a x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u α κ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hc hσ h1 h2
    hv hvs hw hws had hdz hgen
  obtain ⟨hu, husp, -⟩ := AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  have hO : ∀ (x : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ x := fun x o =>
    (ConstReg.regular_const X Ω ξ O s hs x o).1
  have hσr : ∀ (x : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ x := fun x a => by
    obtain ⟨o, ho⟩ := hσ a
    exact ho ▸ hO x o
  have hinv : ∀ x ∈ genFibre O ξ, ∀ b : 𝓞 E, (σ (b : E))⁻¹ ∈ regAt ξ x := fun x hx b => by
    obtain ⟨o, ho⟩ := hσ b
    rw [← ho]
    by_cases h0 : o = 0
    · rw [h0, map_zero, inv_zero]
      exact zero_mem _
    · exact (hx o h0).2.2
  refine _root_.GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical X Ω ξ O s ϖ hϖ hinj hs hg hn (_root_.GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper X Ω ξ O s ϖ hϖ hinj hs hg hc) _ _
    (𝓗.det_isVB σ hσr hu husp) (hdz u hu husp) fun x hx => ?_
  obtain ⟨ha, hb, hco⟩ := hgen
  have hα : α ≠ 0 := left_ne_zero_of_smul ha
  have hκ : κ ≠ 0 := left_ne_zero_of_smul hb
  refine (GenAgree.generic_agree X Ω ξ E V L ρ bar p q 𝓗 σ σ' v w u x (α / κ) hg h1 h2 (fun a => ?_)
    hv hvs hw hws had).2 ⟨div_ne_zero hα hκ, ?_⟩
  · obtain ⟨y, z, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have e : ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = (c : E) := fun _ => rfl
    rw [e, e, map_div₀, map_div₀, h1, h1, div_eq_mul_inv, div_eq_mul_inv]
    exact ⟨mul_mem (hσr x _) (hinv x hx _), mul_mem (hσr x _) (hinv x hx _)⟩
  · obtain ⟨a', b', ha', hb', hA, hB, e⟩ := hco x hx
    rw [one_mul] at e
    subst e
    refine ⟨a' * α, a' * κ, mul_ne_zero ha' hα, mul_ne_zero ha' hκ, by rw [hA, smul_smul], by rw [hB, smul_smul], ?_⟩
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.COrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDetStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_index_frame_log_det : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L), T.det ≠ 0 → gIdx (locAt v (frame T)).toAddSubgroup (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem moduli_isReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l), IsReduced Xo.X := by
  intro E _ _ _ H D l Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  exact isReduced_of_smooth Xo.s

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem isSemiAbelian_of_isGrpPullback : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G']
    [IsCommMonObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsSemiAbelian G →
    IsSemiAbelian G' := by
  intro X X' G _ G' _ _ f φ h hG
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback f G hG)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingCubical
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_pairing_cubical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (n : ℕ), 1 ≤ n → ∃ (w : ∀ (T : Over S) (x z : T ⟶ t.G), x ^ n = 1 → z ^ n = 1 → Γ(T.left, ⊤)ˣ), (∀ (T T' : Over S) (f : T' ⟶ T) (x z : T ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (hx' : (f ≫ x) ^ n = 1) (hz' : (f ≫ z) ^ n = 1), (w T' (f ≫ x) (f ≫ z) hx' hz' : Γ(T'.left, ⊤)) = f.left.appTop.hom (w T x z hx hz)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S), IsProper (Limits.pullback.snd t.G.hom g) → ∀ (x z : Over.mk g ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (c : kˣ), Out.WeilIs t.G t.PP.L n x z (unitOn c) → w (Over.mk g) x z hx hz = unitOn c :=
  PositivityTheory.HtPt.Weilfun.weil_fun

end GlobalTheory.CompanionTheory.Ar.HT
end

