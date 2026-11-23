module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ZJ.Core.Test.exists_fibre_immersion {C : ZJ.Core} (hF : C.Fib) {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ h : pullback τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f ∧ h ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion h ∧ Set.range h = Set.univ := by
  have w : (pullback.fst τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ τ.f) ≫ C.GG.hom =
      pullback.snd τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ ZJ.rPt p ≫ y := by
    rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac]
  let h := pullback.lift _ _ w
  have h₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hc := τ.imm h h₁ h₂
  refine ⟨h, h₁, h₂, hc, ?_⟩
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have := (ZJ.core_basic C).2.1
  let s := pullback.snd C.GG.hom (ZJ.rPt p ≫ y)
  have : JacobsonSpace ↥(pullback C.GG.hom (ZJ.rPt p ≫ y)) := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.univ_subset_iff, ← closure_closedPoints, h.isClosedEmbedding.isClosed_range.closure_subset_iff]
  intro x hx
  obtain ⟨z, hz, hzx⟩ : ∃ z : Sp (ZJ.kb p) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      z ≫ pullback.snd _ _ = 𝟙 _ ∧ ∀ q, z q = x :=
    ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, pointOfClosedPoint_apply s x hx⟩
  obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (z ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, reassoc_of% hz])
  have e : pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) ≫ h = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂, pullback.lift_snd, hz]
  exact ⟨pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) (IsLocalRing.closedPoint (ZJ.kb p)),
    (congrArg (fun g => g (IsLocalRing.closedPoint (ZJ.kb p))) e).trans (hzx _)⟩

theorem ZJ.Core.Test.exists_isGt_special {C : ZJ.Core} {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ E : SplitExt (Sp (ZJ.kb p)), E.IsGt ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := by
  have := τ.j_loc
  have hr : Set.range (ZJ.rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
    have h : ∀ q, (ZJ.rPt p ≫ spMap τ.j) q = IsLocalRing.closedPoint τ.V := fun q => by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint (ZJ.kb p))]
      exact (congrArg (PrimeSpectrum.comap τ.j)
        (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZJ.OO p)))).trans (IsLocalRing.comap_closedPoint τ.j)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint (ZJ.kb p), h _⟩, by
      rintro _ ⟨q, rfl⟩
      exact h q⟩
  obtain ⟨G₁, _, _, E, φ, hE, hφ⟩ := τ.exists_isGt_fibre _ _ hr
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback τ.H _)
  exact ⟨E, isGt_of_iso e hE⟩

theorem ZH.Clos.TMap.eSec_comp_f {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} (ex : Q.Ext) {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) :
    (eSec t.u.G ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι : Sp t.u.V ⟶ Q.P.left) = c.yV ≫ ex.e ≫ Q.G.ι := by
  have := Q.proper
  have : IsDominant (Out.jK t.u.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective t.u.V _)]
    exact bot_le)⟩
  obtain ⟨e₁, he₁, s₁⟩ : ∃ e₁ : Sp t.u.V ⟶ t.u.G.left, e₁ = eSec t.u.G ∧ e₁ ≫ t.u.G.hom = 𝟙 _ :=
    ⟨_, rfl, Over.w η[t.u.G]⟩
  obtain ⟨e₂, he₂, s₂⟩ : ∃ e₂ : Sp (FractionRing t.u.V) ⟶ pullback t.u.G.hom (jK t.u.V),
      e₂ = eSec ((Over.pullback (jK t.u.V)).obj t.u.G) ∧ e₂ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback (jK t.u.V)).obj t.u.G]⟩
  obtain ⟨e₃, he₃, s₃⟩ : ∃ e₃ : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀,
      e₃ = eSec ((Over.pullback Q.u₀).obj ρ.P.A) ∧ e₃ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]⟩
  obtain ⟨e₄, he₄⟩ : ∃ e₄ : Sp S.R ⟶ ρ.P.A.left, e₄ = eSec ρ.P.A := ⟨_, rfl⟩
  have h₂ : e₂ ≫ pullback.fst _ _ = jK t.u.V ≫ e₁ := by
    subst he₁ he₂
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback t.u.G (jK t.u.V))
  have h₃ : e₃ ≫ pullback.fst _ _ = Q.u₀ ≫ e₄ := by
    subst he₃ he₄
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback ρ.P.A Q.u₀)
  have h₄ : e₂ ≫ t.u.U.gen.hom.left ≫ t.u.φ = spMap t.u.yK ≫ e₄ := by
    subst he₂ he₄
    have := t.u.U.gen_hom
    exact ZJ.eSec_comp_of_isGrpPullback
      (((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr (Category.id_comp _) rfl)
  have h₅ : U₀.ι ≫ ex.e = e₃ ≫ ex.a := he₃ ▸ ex.e_zero
  have h₆ : e₂ ≫ tm.φ = c.yK ≫ e₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tm.φ_fst, h₃, reassoc_of% c.yK_u]
      exact h₄
    · rw [Category.assoc, Category.assoc, tm.φ_snd, s₃, reassoc_of% s₂, Category.comp_id]
  rw [← he₁]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (Out.jK t.u.V) ?_
  · simp only [Category.assoc]
    rw [tm.f_over, ex.e_sec, reassoc_of% s₁, Category.comp_id]
  · rw [← reassoc_of% c.yK_fac, reassoc_of% h₅, ex.a_eq, ← reassoc_of% h₆, tm.φ_f, reassoc_of% h₂]

theorem ZH.exists_iso_special_fibre_of_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm τ hS hF
  obtain ⟨τ₀, e₀, he₁, he₂⟩ := _root_.GlobalTheory.ZH.Clos.exists_core_test_of_geoTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  obtain ⟨h, h₁, h₂, hc, hr⟩ := τ.exists_fibre_immersion hF
  obtain ⟨h₀, h₀₁, h₀₂, hc₀, hr₀⟩ := τ₀.exists_fibre_immersion hF
  obtain ⟨E, hE⟩ := τ.exists_isGt_special
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have : IsCommMonObj ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := Functor.isCommMonObj_obj
  let Y : Over (Sp (ZJ.kb p)) := Over.mk (pullback.snd ex.core.GG.hom (ZJ.rPt p ≫ y))
  let f : (Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H ⟶ Y := Over.homMk h h₂
  have w : (e₀.inv ≫ h₀) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h₀₂, ← he₁, Iso.inv_hom_id_assoc]
  let f' : t.mod.Φ.G ⟶ Y := Over.homMk (e₀.inv ≫ h₀) w
  have k : (e₀.inv ≫ h₀) ≫ pullback.fst _ _ ≫ Q.G.ι = t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rw [Category.assoc, Iso.inv_comp_eq, he₂]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₀₁).trans (Category.assoc _ _ _))
  have k' : h ≫ pullback.fst _ _ ≫ Q.G.ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₁).trans (Category.assoc _ _ _))
  have hr' : Set.range (e₀.inv ≫ h₀) = Set.univ := by
    rw [Set.range_eq_univ] at hr₀ ⊢
    exact hr₀.comp e₀.inv.surjective
  have hone : η[(Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H] ≫ f = η[t.mod.Φ.G] ≫ f' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (cancel_mono Q.G.ι).1 ?_
      have u₁ := ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (ZJ.rPt p ≫ spMap τ.j))
      have u₂ := ZJ.eSec_comp_of_isGrpPullback t.mod.cart
      have v₁ : eSec ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) ≫ pullback.fst _ _ ≫ τ.f ≫ Q.G.ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.f ≫ Q.G.ι) u₁)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap τ.j ≫ g ≫ Q.G.ι) τ.eSec_comp_f
        exact a.trans (congrArg (fun g => ZJ.rPt p ≫ g ≫ ex.e ≫ Q.G.ι) τ.fac)
      have v₂ : eSec t.mod.Φ.G ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) u₂)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap t.u.j ≫ g) (tm.eSec_comp_f ex)
        simp only [Category.assoc] at a ⊢
        rw [reassoc_of% c.fac] at a
        exact a
      rw [← k'] at v₁
      rw [← k] at v₂
      exact v₁.trans v₂.symm
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨e, he, hef⟩ := exists_iso_isMonHom_of_isGt_of_range_eq (ZJ.kb p) Y E t.mod.Φ.E _ _ f f' hE ⟨t.mod.Φ.D⟩ hc
    (inferInstanceAs (IsClosedImmersion (e₀.inv ≫ h₀))) (hr.trans hr'.symm) hone
  refine ⟨e, he, ?_⟩
  have hl : e.hom.left ≫ e₀.inv ≫ h₀ = h := congrArg (fun g => g.left) hef
  rw [← k, ← k', ← hl]
  simp only [Category.assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.GaugeHom
open GlobalTheory.TorusExt GlobalTheory.ArcExt

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {L : LB X}
  {J J' : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (hJ' : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ))
include hJ hJ'

theorem exists_trans : ∃ T : (Sp F ⟶ X) → Fˣ, ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y), sF s r J = (∏ k, T (r ≫ φ k) ^ ε k : Fˣ) * sF s r J' := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hm : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ (L.U (J ψ) ⊓ L.U (J' ψ)) := fun ψ z hz => ⟨hJ ψ hz, hJ' ψ hz⟩
  have hv : ∀ ψ : Sp F ⟶ X, (gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))).val =
      stalkConst y (valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val) := fun ψ =>
    (gs_unit ψ y _ (hm ψ trivial) _).symm.trans (gs_eq_stalkConst ψ y (hm ψ) _)
  have hne : ∀ ψ : Sp F ⟶ X, valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val ≠ 0 := fun ψ h =>
    (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (hm ψ)).symm.trans h)
  refine ⟨fun ψ => Units.mk0 _ (hne ψ), fun Y K _ φ ε s r => (stalkConst y).injective ?_⟩
  have e : ∀ ψ : Sp F ⟶ X, gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)) =
      Units.map (stalkConst y).toMonoidHom (Units.mk0 _ (hne ψ)) := fun ψ => Units.ext (hv ψ)
  have a := sec_trans s r y (top_le_chart hJ φ r trivial) (top_le_chart hJ' φ r trivial)
  rw [map_mul]
  refine (gs_eq_stalkConst r y (top_le_chart hJ φ r) _).symm.trans
    (a.trans (congrArg₂ (· * ·) ?_ (gs_eq_stalkConst r y (top_le_chart hJ' φ r) _)))
  show _ = (Units.map (stalkConst y).toMonoidHom _).val
  rw [map_prod, trF]
  refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow, e]

end Val

theorem exists_trans_ext {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {J : (Sp F ⟶ X) → L.ι} {J' : (Sp F' ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    (hJ' : ∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) : ∃ T : (Sp F ⟶ X) → F'ˣ,
    (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J)) ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ r : Sp F ⟶ Y,
      vF t (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (vF t r J) := by
  obtain ⟨J₀, h₀, e₀⟩ := exists_gauge f hL hJ
  obtain ⟨T, hT⟩ := exists_trans hJ' h₀
  have k : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (spMap f ≫ r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J) := fun Y K _ φ ε s r => by
    rw [hT, sF_ext f hJ e₀]
    simp only [Category.assoc]
  exact ⟨fun ψ => T (spMap f ≫ ψ), k, fun Y K _ φ ε t ht r => k Y K φ ε (genSec t ht) r⟩

theorem exists_hom (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (N : NumD F) (N' : NumD F')
    (ν : NumOf D F N) (ν' : NumOf D F' N') (hth : ν'.th = ν.th) :
    ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧
      ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q →
        ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  obtain ⟨T, hs, hg⟩ := exists_trans_ext f D.P.isLB ν.good ν'.good
  have hr : rigVal ν' = T (1 : TF (R := R) F ⟶ D.P.A).left * f (rigVal ν) := by
    have := hg _ _ (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) F).hom
    rw [Fintype.prod_unique, zpow_one] at this
    refine Eq.trans ?_ this
    exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
      (Over.w (extMap (R := R) f hf)).symm
  have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
  let I : NumD.Hom f N N' :=
    { φ := ptHom f hf ν ν'
      h := fun x => T (ν.eA x).left / T (1 : TF (R := R) F ⟶ D.P.A).left
      h_one := by rw [map_one, div_self']
      θ_eq := fun x y u => by
        have e : N'.θ (ptHom f hf ν ν' x) (ptHom f hf ν ν' y) (ptHom f hf ν ν' u) =
            (∏ I : thK, T ((lift (ν.eA x) (lift (ν.eA y) (ν.eA u))).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I) *
              Units.map f.toMonoidHom (N.θ x y u) := by
          refine Units.ext ?_
          show _ = _ * f (N.θ x y u : F)
          rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
          exact hg _ _ _ _ _ D.cub.isGen _
        rw [e, prod_cub]
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      σ_eq := fun x => by
        have e : N'.σ (ptHom f hf ν ν' x) = (T (ν.eA x)⁻¹.left * (T (ν.eA x).left)⁻¹) *
            Units.map f.toMonoidHom (N.σ x) := by
          refine Units.ext ?_
          show _ = _ * f (N.σ x : F)
          rw [ν'.σ_eq, ν.σ_eq, eA_ptHom]
          refine (hg _ _ _ _ _ D.sym_gen _).trans (congrArg (fun z : F'ˣ => z.val * _) ?_)
          rw [Fin.prod_univ_two]
          show T ((ν.eA x)⁻¹).left ^ (1 : ℤ) * T ((ν.eA x).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
          rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
        rw [e, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      lam := 1
      th_eq := fun x => by
        have a : N'.th (ptHom f hf ν ν' x) * rigVal ν' = _ := ν'.th_eq _
        have b : N.th x * rigVal ν = _ := ν.th_eq _
        have c := hs _ _ _ _ ν.th (ν.eA x).left
        rw [Fintype.prod_unique, Category.comp_id, ← b, zpow_natCast, pow_one, map_mul] at c
        rw [eA_ptHom, hth, hr] at a
        have d := a.trans c
        have h1 : f (rigVal ν) ≠ 0 := (map_ne_zero f).2 h0
        rw [← _root_.mul_assoc, ← _root_.mul_assoc] at d
        have d' := mul_right_cancel₀ h1 d
        rw [_root_.one_mul, Units.val_div_eq_div_val, div_mul_eq_mul_div, ← d', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      e := ν.eX.trans ν'.eX.symm
      c_eq := fun χ => ν'.eA.injective (by
        rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        exact (DVR.comp_cP D (extMap f hf) _).symm)
      ψ_eq := fun χ => by
        have e : N'.ψ (ν.eX.trans ν'.eX.symm χ) = ((T (ν.eA (N.c χ)).left)⁻¹ * T (1 : TF (R := R) F ⟶ D.P.A).left) *
            Units.map f.toMonoidHom (N.ψ χ) := by
          refine Units.ext ?_
          show _ = ((T (ν.eA (N.c χ)).left)⁻¹).val * (T (1 : TF (R := R) F ⟶ D.P.A).left).val * f (N.ψ χ : F)
          rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, _root_.mul_mul_mul_comm]
          refine congrArg₂ (· * ·) ?_ hr
          have c := hg _ _ _ _ _ (D.psi_gen (ν.eX χ)) (jFK (R := R) F)
          rw [Fintype.prod_unique, zpow_neg, zpow_one] at c
          refine (congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J)
            ((extMap_jFK f hf).trans (Category.id_comp _)).symm).trans (c.trans ?_)
          refine congrArg (fun z => ((T z)⁻¹).val * _) ?_
          rw [ν.c_eq]
          exact congrArg (fun z => z.left) (DVR.comp_cP D
            (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) _)
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel }
  have hX : ∀ y, ν'.eX (I.e y) = ν.eX y := fun y => ν'.eX.apply_symm_apply _
  refine ⟨I, rfl, hX, fun k p p' q q' h hq hq' => ⟨ν'.eX.injective (hq'.1.trans (h.1.trans (hq.1.symm.trans (hX _).symm))),
    ν'.eA.injective (hq'.2.1.trans (Over.OverMorphism.ext ?_)), fun χ => ?_⟩⟩
  · rw [h.2.1, ← hq.2.1]
    exact (congrArg (fun z => z.left) (eA_ptHom f hf ν ν' _)).symm
  · have e : q'.1.2.s (I.e χ) = (∏ i, T (DegPre.gtφ D F p.g.b (ν.eX χ) i) ^ DegPre.gtε i) *
        Units.map f.toMonoidHom (q.1.2.s χ) := by
      refine Units.ext ?_
      show _ = _ * f (q.1.2.s χ : F)
      rw [hq'.2.2, hq.2.2, hX]
      have c := hg _ _ _ _ _ (p.g.isGen (ν.eX χ)) (𝟙 (Sp F))
      simp only [Category.id_comp, Category.comp_id] at c
      refine Eq.trans ?_ c
      let y : Sp F' := IsLocalRing.closedPoint F'
      have hJ : Good D.P.L y ν'.J := fun ψ => ν'.good ψ trivial
      refine (stalkConst y).injective ((val_eq_vF ν'.good _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF ν'.good _ _ y)))
      refine congrArg Units.val ((val_corr hJ (h.2.2 _) _).trans ((val_pull hJ _ _ _).trans ?_))
      rw [Category.id_comp]
    rw [e, prod_gt]
    show _ * (T (ν.eA (N.c χ * q.1.2.b)).left / _) = _ * (T (ν.eA (N.c χ)).left / _) * (T (ν.eA q.1.2.b).left / _)
    rw [map_mul, hq.2.1, ν.c_eq]
    show _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ) * p.g.b).left / _) =
      _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ)).left / _) * _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

end GlobalTheory.GaugeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' := pull_isLB hL F
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMoveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_of_isPolIso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  first | exact @GlobalTheory.FullMove.exists_tateIso_move | exact GlobalTheory.FullMove.exists_tateIso_move | (intros; apply GlobalTheory.FullMove.exists_tateIso_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPairDescentAlgClosedSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.QkDescent

theorem exists_qkExt_of_isAlgClosed : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  intro hL R _ _ _ D hB F F' _ _ _ _ _ _ _ f hf k hk p'
  have hk' : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F')
  have hk0 : k ≠ 0 := by omega
  obtain ⟨q, hq⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) hB hk0 p'.y
  obtain ⟨h₀, h₁, h₂⟩ := q.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁'
  have hh₀ : GtPtF.IsIota p'.y (k • q.g) := hq ▸ h₂
  have hext : GtPtF.IsIota p'.y (GlobalTheory.TorusExt.gtExt D f hf (k • q.g)) := by
    obtain ⟨b, -⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 hh₀
    refine (GlobalTheory.TorusExt.isIota_iff_val _ _).2 ⟨by rw [GlobalTheory.TorusExt.gtExt_b, b, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP], fun χ y J hJ => ?_⟩
    rw [GlobalTheory.TorusExt.gtExt_val f hf _ χ hJ, GlobalTheory.TorusExt.tauVal, ← GlobalTheory.TorusExt.extMap_jFK f hf]
    exact (val_corr hJ (hh₀.2 χ) _).trans (val_pull hJ _ _ _)
  have e₀ : GlobalTheory.TorusExt.gtExt D f hf (k • q.g) = k • p'.g := GlobalTheory.TorusExt.isIota_unique hext h₂'
  have ht' : k • (p'.g - GlobalTheory.TorusExt.gtExt D f hf q.g) = 0 := by
    rw [nsmul_sub, ← map_nsmul, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk' _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = GlobalTheory.TorusExt.gtExt D f hf (q.g + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, q.g + t, k • q.g, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (GlobalTheory.TorusExt.eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero]

end GlobalTheory.QkDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qval_add_of_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  first | exact @GlobalTheory.NestQVal.qval_add_tower | exact GlobalTheory.NestQVal.qval_add_tower | (intros; apply GlobalTheory.NestQVal.qval_add_tower <;> assumption)
end

