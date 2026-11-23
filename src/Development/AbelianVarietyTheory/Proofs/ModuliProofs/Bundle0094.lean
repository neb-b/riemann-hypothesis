module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueRigMulRight
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubCompare
variable {S S' : Scheme.{0}}

section Gen
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section Pack
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

end Pack

section Maps
variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

end Maps

section Triv
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]


variable {L : RigLB G} {i : H ⟶ G}




variable {c : CubicalStr G L} [IsMonHom i]


end Triv

section Wt
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(Y, V)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((r.appLE V ⊤ h).hom u) = gs r z V u :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) r z V (h trivial) u).trans (by rw [Category.id_comp]))

theorem gs_comp {Y Z Z' : Scheme.{0}} (ρ : Z' ⟶ Z) (r : Z ⟶ Y) (V : Y.Opens) (z : Z') (h : r (ρ z) ∈ V) (u : Γ(Y, V)) :
    gs (ρ ≫ r) z V u = (ρ.stalkMap z).hom (gs r (ρ z) V u) := by
  rw [gs_eq (ρ ≫ r) z V h, gs_eq r _ V h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ V) z h _).symm

theorem isWt_iff_germ (i : splitTorus S X ⟶ G) (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X) :
    IsWt i V u χ ↔ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ V →
      ((t ≫ i) * x).left z ∈ V → gs ((t ≫ i) * x).left z V u = (charV χ z t).val * gs x.left z V u := by
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V) (z : Z.left),
      gs (𝟙 Z.left) z ⊤ (t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u) =
        (charV χ z t).val * gs g.left z V u := fun Z t g h₂ z => by
    rw [gs_mul _ z ⊤ trivial, gs_appLE, ← chV_val, gs_unit _ z ⊤ trivial, charV, gm_charUnit]
  constructor
  · intro h T z t x hx hx'
    let O : T.left.Opens := x.left ⁻¹ᵁ V ⊓ ((t ≫ i) * x).left ⁻¹ᵁ V
    let ρ : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    have e : ((ρ ≫ t) ≫ i) * (ρ ≫ x) = ρ ≫ ((t ≫ i) * x) := by rw [MonObj.comp_mul, Category.assoc]
    have h₁ : ⊤ ≤ (((ρ ≫ t) ≫ i) * (ρ ≫ x)).left ⁻¹ᵁ V := by rw [e]; exact fun y _ => y.2.2
    have h₂ : ⊤ ≤ (ρ ≫ x).left ⁻¹ᵁ V := fun y _ => y.2.1
    have a := congrArg (gs (𝟙 _) (⟨z, hx, hx'⟩ : O) ⊤) (h _ (ρ ≫ t) (ρ ≫ x) h₁ h₂)
    erw [key, gs_appLE] at a
    rw [e] at a
    unfold charV at a
    erw [← gs_unit _ _ ⊤ trivial] at a
    have inj : ∀ y : O.toScheme, Function.Injective (O.ι.stalkMap y).hom := fun y =>
      (ConcreteCategory.bijective_of_isIso _).1
    apply inj ⟨z, hx, hx'⟩
    rw [charV, ← gs_unit _ _ ⊤ trivial]
    exact ((gs_comp O.ι _ V ⟨z, hx, hx'⟩ hx' u).symm.trans a).trans ((congrArg₂ (· * ·)
      (gs_comp O.ι t.left ⊤ ⟨z, hx, hx'⟩ trivial _) (gs_comp O.ι x.left V ⟨z, hx, hx'⟩ hx u)).trans (map_mul _ _ _).symm)
  · intro h Z t g h₁ h₂
    refine fn_ext fun z _ => ?_
    rw [key, gs_appLE]
    exact h Z z t g (h₂ trivial) (h₁ trivial)

end Wt

section Ext
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

variable {B : Over S} [GrpObj B]


end Ext

section Desc
variable {G H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]
  {i : H ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] {P : CP G} {M : CP B} {w : LB.Iso P.L.L (M.L.L.pull q.left)}



end Desc

end GlobalTheory.CubCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ValGenExtend

def genSec {X : Scheme.{0}} {L : LB X} (t : LB.Gen L) (ht : t.IsGen) : LB.Sec L :=
  ⟨fun i => (t.s i).val, fun i j => by
    have h := congrArg Units.val (ht i j)
    exact h⟩

theorem isGen_inv_of_eq {X : Scheme.{0}} {N : LB X} (t : LB.Gen N) (ht : t.IsGen)
    (g : ∀ a b, Γ(X, N.U a ⊓ N.U b)ˣ) (hg : ∀ a b, g a b = (N.g a b)⁻¹) :
    LB.Gen.IsGen (L := ⟨N.ι, N.U, g⟩) ⟨fun i => (t.s i)⁻¹⟩ := by
  intro a b
  have h : res (inf_le_left : N.U a ⊓ N.U b ≤ _) (t.s a)⁻¹ =
      g a b * res (inf_le_right : N.U a ⊓ N.U b ≤ _) (t.s b)⁻¹ := by
    rw [map_inv, map_inv, ht a b, _root_.mul_inv, hg]
  exact h

theorem exists_isGen_inv {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by
  refine ⟨⟨fun i => (t.s i)⁻¹⟩,
    isGen_inv_of_eq t ht ((⟨I, U, g'⟩ : LB X).pull j).g fun a b => ?_, fun i => ?_⟩
  · dsimp only [LB.pull, LB.LinComb]
    simp only [hg, map_inv, zpow_one, Finset.prod_inv_distrib]
    try rfl
  · exact (map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _))

theorem mem_basicOpen_of_mem {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have h := congrArg X.basicOpen (s.compat i k)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i k).isUnit] at h
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at h
  have hm : x ∈ L.U i ⊓ L.U k := ⟨hi, X.basicOpen_le _ hk⟩
  exact (h.ge (⟨hm, hm, hk⟩ : x ∈ _ ⊓ (_ ⊓ X.basicOpen (s.f k)))).2

theorem app_cst {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {X Y : Scheme.{0}}
    {f : X ⟶ Sp O} {j : Y ⟶ X} {g : Y ⟶ Sp K} (h : j ≫ f = g ≫ spMap φ) (U : X.Opens) (a : O) :
    (j.app U).hom (GlobalTheory.AbLaw.cst f U a) = GlobalTheory.AbLaw.cst g (j ⁻¹ᵁ U) (φ a) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 := congrArg (fun u => u.hom a) h1
  have h3 := congrArg (fun u => u.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)))
    (j.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  exact h3.trans (congrArg (rs Y le_top) h2)

theorem isUnit_of_mem_basicOpen {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}}
    (f : X ⟶ Sp O) {U : X.Opens} {a : O} {x : X} (hx : x ∈ X.basicOpen (GlobalTheory.AbLaw.cst f U a))
    (hf : f x = IsLocalRing.closedPoint O) : IsUnit a := by
  have h : X.basicOpen (GlobalTheory.AbLaw.cst f U a) =
      U ⊓ X.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) :=
    Scheme.basicOpen_res _ _ _
  have h1 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := (h.le hx).2
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  have h2 : a ∉ (f x).asIdeal := h1
  rw [hf] at h2
  exact not_not.1 h2

theorem triv_of_triv_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  intro O K _ _ _ _ _ _ _ _ X XK f j fK hp hsm hqc hgi M hM ⟨t, ht⟩
  have : IsDominant (spMap (algebraMap O K)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap O K))
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  have : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ hp
  obtain ⟨z⟩ : Nonempty XK := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (j z)
  have : Nonempty ((M.pull j).U fun _ => i₀) := ⟨⟨z, le_pull M j le_rfl hi₀⟩⟩
  obtain ⟨t', ht', htt⟩ := exists_isGen_inv M.g (GlobalTheory.AbLaw.pw M (-1)).g
    (fun a b => zpow_neg_one _) j t ht
  have hne : (t'.s fun _ => i₀).val ≠ 0 := fun h => by
    have h1 := htt i₀
    have : Nonempty (j ⁻¹ᵁ M.U i₀) := ⟨⟨z, hi₀⟩⟩
    rw [h, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, s, hc, hs, x, hx, hfx⟩ := _root_.GlobalTheory.exists_smul_sec_nonzero_on_special_fibre O K X XK f j fK hp hsm hqc hgi M hM
    (genSec t ht) ⟨fun _ => i₀, (t.s fun _ => i₀).ne_zero⟩
  obtain ⟨c', s', hc', hs', x', hx', hfx'⟩ := _root_.GlobalTheory.exists_smul_sec_nonzero_on_special_fibre O K X XK f j fK hp hsm hqc hgi _
    (isLB_pw hM (-1)) (genSec t' ht') ⟨fun _ => i₀, hne⟩
  have hprod : ∀ i : M.ι, (j.app (M.U i)).hom (s.f i * (show Γ(X, M.U i) from s'.f i)) =
      GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) (c * c') := fun i => by
    have h' : (j.app (M.U i)).hom (s'.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c' *
      rs XK (le_pull (GlobalTheory.AbLaw.pw M (-1)) j (W := M.U i) (i := i) le_rfl)
        (t'.s fun _ => i).val := hs' i
    have h : (j.app (M.U i)).hom (s.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c *
      rs XK (le_pull M j le_rfl) (t.s fun _ => i).val := hs i
    rw [map_mul, h, h', _root_.mul_mul_mul_comm, ← map_mul]
    exact (congrArg _ (htt i)).trans (_root_.mul_one _)
  have key : ∀ i, IsUnit (s.f i) := by
    rcases ValuationRing.isInteger_or_isInteger O (c * c') with ⟨a, ha⟩ | ⟨a, ha⟩
    · have e : ∀ i : M.ι, s.f i * (show Γ(X, M.U i) from s'.f i) = GlobalTheory.AbLaw.cst f (M.U i) a :=
        fun i => j.app_injective _ ((hprod i).trans (ha ▸ (app_cst _ hp.w _ a).symm))
      obtain ⟨y, hy, hy₁, hy₂⟩ := (f.isIrreducible_preimage f.isOpenMap
        (isIrreducible_singleton (x := IsLocalRing.closedPoint O))).isPreirreducible _ _
        (Out.nonzeroLocus s).isOpen (Out.nonzeroLocus s').isOpen ⟨x, hfx, hx⟩ ⟨x', hfx', hx'⟩
      obtain ⟨k, hk⟩ := exists_chart hM y
      have hu : IsUnit a := by
        refine isUnit_of_mem_basicOpen f (U := M.U k) (x := y) ?_ hy
        rw [← e k, Scheme.basicOpen_mul]
        exact ⟨mem_basicOpen_of_mem s hy₁ hk, mem_basicOpen_of_mem s' hy₂ (i := k) hk⟩
      exact fun i => isUnit_of_mul_isUnit_left ((e i).symm ▸ hu.map _)
    · intro i
      have e : s.f i * ((show Γ(X, M.U i) from s'.f i) * GlobalTheory.AbLaw.cst f (M.U i) a) = 1 := by
        refine j.app_injective _ ?_
        change (j.app (M.U i)).hom _ = (j.app (M.U i)).hom _
        rw [← _root_.mul_assoc, map_mul, hprod, app_cst _ hp.w, ← map_mul, ha,
          mul_inv_cancel₀ (mul_ne_zero hc hc'), map_one, map_one]
      exact IsUnit.of_mul_eq_one _ e
  exact ⟨⟨fun i => (key i).unit⟩, fun a b => Units.ext (s.compat a b)⟩

end GlobalTheory.ValGenExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfIdModEpsThickening
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsIso

theorem ker_fst_eq_span (K : Type) [Field K] :
    RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h0 : x.fst = 0 := hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext
    · simp [h0]
    · simp
  · rintro ⟨y, rfl⟩
    show (DualNumber.eps * y).fst = 0
    simp

set_option maxHeartbeats 1000000 in
private theorem exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    ∃ d : C, c = a DualNumber.eps * d := by
  let _ : Algebra (DualNumber K) C := a.toAlgebra
  have _ : Module.Flat (DualNumber K) C := ha
  have hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hc
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C)
    (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum
  have hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd := by
    intro i
    have h1 : DualNumber.eps * b () i = 0 := by
      have h0 := hb i
      rwa [Fintype.sum_unique] at h0
    have h2 : (b () i).fst = 0 := by
      have h3 := congrArg TrivSqZeroExt.snd h1
      rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add,
        TrivSqZeroExt.snd_zero] at h3
      exact h3
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]
    · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul,
        TrivSqZeroExt.fst_inl]
  refine ⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩
  rw [show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hki := hkill i
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  conv_lhs => rw [hki]
  rw [map_mul, _root_.mul_assoc]

theorem mem_span_of_flat {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    c ∈ Ideal.span {a DualNumber.eps} := by
  rw [Ideal.mem_span_singleton]
  exact exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc

theorem bijective_of_mod_eps {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by
  have hee : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hk : jC (φ (a DualNumber.eps)) = 0 := by
    rw [← RingHom.mem_ker, hC]
    exact Ideal.mem_span_singleton_self _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : b ∈ RingHom.ker jB := by rw [RingHom.mem_ker, ← hφ, hb, map_zero]
    rw [hB, Ideal.mem_span_singleton] at h1
    obtain ⟨b1, rfl⟩ := h1
    have h2 : (φ.comp a) DualNumber.eps * φ b1 = 0 := by
      rw [RingHom.comp_apply, ← map_mul]
      exact hb
    have h3 := mem_span_of_flat (φ.comp a) hfl (φ b1) h2
    rw [Ideal.mem_span_singleton] at h3
    obtain ⟨c', hc'⟩ := h3
    have h4 : b1 ∈ RingHom.ker jB := by
      rw [RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]
    rw [hB, Ideal.mem_span_singleton] at h4
    obtain ⟨b2, rfl⟩ := h4
    rw [← _root_.mul_assoc, hee, zero_mul]
  · intro c
    obtain ⟨b, hb⟩ := hs (jC c)
    have h1 : c - φ b ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨b1, hb1⟩ := hs (jC c1)
    have h2 : c1 - φ b1 ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h2
    obtain ⟨c2, hc2⟩ := h2
    have hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0 := by
      rw [← map_mul, hee, map_zero]
    refine ⟨b + a DualNumber.eps * b1, ?_⟩
    rw [map_add (f := _), map_mul]
    linear_combination (-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe

theorem fst_surjective (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := by
  intro x
  exact ⟨algebraMap K (DualNumber K) x, by simp⟩

theorem isHomeomorph_of_isPullback {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by
  have hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) := rfl
  have hsurj := fst_surjective K
  have hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [hsp]
    exact IsClosedImmersion.spec_of_surjective _ hsurj
  have hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ := by
      rw [range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom)
        (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      rw [SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      show _ ∈ nilradical _
      rw [mem_nilradical]
      exact ⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩
    rw [hsp]
    exact ⟨fun p => Set.range_eq_univ.1 hr p⟩
  have hcj : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci
  have hsj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu
  refine ⟨hcj, ?_⟩
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩

theorem isAffineHom_of_isHomeomorph {X Y : Scheme.{0}} (e : X ⟶ Y) (he : IsHomeomorph e) :
    IsAffineHom e := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := he.surjective y
  have hmem : e x ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ e ⁻¹ᵁ V from hxV)
  let O : Y.Opens := ⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩
  obtain ⟨g, hgO, hgy⟩ := (show IsAffineOpen V from hV).exists_basicOpen_le (V := O)
    ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV
  have hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgO hz
    rwa [← he.injective hwz]
  refine ⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩
  have heq : e ⁻¹ᵁ Y.basicOpen g =
      X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 hsub).symm
  rw [heq]
  exact (show IsAffineOpen W from hW).basicOpen _

end GlobalTheory.EpsIso

namespace GlobalTheory

theorem isIso_of_id_mod_eps : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  intro K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj
  subst hπ hj
  obtain ⟨hcj, hhj⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h
  obtain ⟨hcj', hhj'⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'
  have hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j := rfl
  have hhe : IsHomeomorph e := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨e.continuous, ?_, ?_⟩
    · intro F hF
      have hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F) := by
        rw [hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]
      rw [hF']
      exact hhj'.isClosedMap _ (hF.preimage j.continuous)
    · have hb := hhj'.bijective
      rw [hcf] at hb
      exact (Function.Bijective.of_comp_iff _ hhj.bijective).1 hb
  have hA : IsAffineHom e := GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe
  have hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    GlobalTheory.EpsIso.fst_surjective K
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := GlobalTheory.EpsIso.ker_fst_eq_span K
  have hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W) := by
    intro W hW
    have hW' : IsAffineOpen (e ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE ..).symm
    have hB := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW
    have hC := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'
    rw [hker, Ideal.map_span, Set.image_singleton] at hB hC
    have hC' := hC.trans (congrArg
      (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)
    have hfl' := HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top
    have hfl2 := (congrArg (fun g => g.hom.Flat) hcomp).mp hfl'
    have hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    have hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
        π'.appLE ⊤ W le_top).hom).Flat := by
      have heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
          π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom := by
        exact RingHom.ext fun x => rfl
      rw [heq]
      exact RingHom.Flat.comp hg hfl2
    have := hcj'
    have hbij := GlobalTheory.EpsIso.bijective_of_mod_eps
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom
      (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl)
      (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0})
    (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_
  have hsrc : IsAffine (e ⁻¹ᵁ V.1) := IsAffineHom.isAffine_preimage _ V.2
  have htgt : IsAffine V.1 := V.2
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]
  have hV : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)
  have hb2 : Function.Bijective
      (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact isIso_SpecMap_iff.2 (hb2.comp hb1)

end GlobalTheory
end

