module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.ThetaExt

open TopologicalSpace

noncomputable def invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) : LB.Iso B A :=
  ⟨fun p => res (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) c *
    (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem gm_invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) (y : X) (a : A.ι) (b : B.ι)
    (ha : y ∈ A.U a) (hb : y ∈ B.U b) : gm (𝟙 X) y (A.U a ⊓ B.U b) ((invMul w c).s (a, b)) =
      gm (𝟙 X) y ⊤ c * (gm (𝟙 X) y (B.U b ⊓ A.U a) (w.s (b, a)))⁻¹ :=
  have hp : (𝟙 X : X ⟶ X) y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))

theorem isGen_invMul {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (c : Γ(X, ⊤)ˣ) :
    (invMul w c).IsGen := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a') := ⟨⟨hy.1.2, hy.1.1⟩, hy.2.2, hy.2.1⟩
  have e := congrArg (gm (𝟙 X) y (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))) (hw (b, a) (b', a'))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (b, a) (b', a') hm) (gm_res _ y _ hm _))))
  have alg : ∀ {a b t s u : (X.presheaf.stalk y)ˣ}, u = b * a⁻¹ * s → t * u⁻¹ = a * b⁻¹ * (t * s⁻¹) := by
    rintro a b t s _ rfl
    rw [mul_inv, mul_inv, inv_inv, mul_comm a, mul_left_comm]
  exact ((gm_res _ y _ hy _).trans (gm_invMul w c y a b hy.1.1 hy.1.2)).trans ((alg e').trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y (a, b) (a', b') hy)
      ((gm_res _ y _ hy _).trans (gm_invMul w c y a' b' hy.2.1 hy.2.2)))).symm)

variable {C : Core} (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem isClosed_closedPoint : IsClosed ({τ.y₀ (IsLocalRing.closedPoint τ.V)} : Set C.Z) := by
  have := τ.j_loc
  have h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V := IsLocalRing.comap_closedPoint τ.j
  have e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V) := by
    rw [← h]
    exact (congrArg (fun g => g (cPt p)) τ.fac).symm
  rw [← e]
  exact GlobalTheory.ZH.isClosed_singleton_cPt y

theorem exists_mem_basicOpen [IsIntegral τ.H.left] [Nonempty (pullback τ.H.hom (Out.jK τ.V) :)]
    [IsOpenImmersion (pullback.fst τ.H.hom (Out.jK τ.V))] (h : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) :
    ∃ (x : (pullback τ.H.hom (Out.jK τ.V) :)) (k : T.L.L.ι), τ.φ x ∈ C.A.left.basicOpen (T.θ.f k) := by
  obtain ⟨x₀, hx₀, e₀⟩ := T.s_ne _ (isClosed_closedPoint τ)
  obtain ⟨x₁, e₁, -⟩ := Scheme.exists_preimage_of_isPullback h x₀ _ e₀
  obtain ⟨_, hx₂, x₂, rfl⟩ := nonempty_preirreducible_inter (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen
    (pullback.fst τ.H.hom (Out.jK τ.V)).isOpenEmbedding.isOpen_range ⟨x₁, show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀⟩
    (Set.range_nonempty _)
  have e₂ : C.a (τ.φ x₂) = τ.f (pullback.fst τ.H.hom (Out.jK τ.V) x₂) := congrArg (fun g => g x₂) τ.φ_f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show C.a (τ.φ x₂) ∈ Out.nonzeroLocus T.s by rw [e₂]; exact hx₂)
  have hi' := C.G.toScheme.basicOpen_le _ hi
  obtain ⟨k, hk⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left (τ.φ x₂))
  have u := (SecPullIso.isUnit_gs_iff C.a _ hi' _).2 hi
  rw [T.w_sec _ i k hi' hk] at u
  have u' := (SecPullIso.isUnit_gs_iff _ _ hk _).1 (isUnit_of_mul_isUnit_right u)
  obtain ⟨x₃, e₃, -⟩ := Scheme.exists_preimage_of_isPullback τ.φ_cart.1 ((mulN C.A T.m).left (τ.φ x₂))
    (((Over.pullback (Out.jK τ.V)).obj τ.H).hom x₂)
    ((congrArg (fun g => g (τ.φ x₂)) (Over.w (mulN C.A T.m))).trans (congrArg (fun g => g x₂) τ.φ_cart.1.w))
  exact ⟨x₃, k, by rw [← e₃] at u'; exact u'⟩

end GlobalTheory.ZJ.ThetaExt

namespace GlobalTheory.ZJ

open ThetaExt TopologicalSpace

theorem Core.Theta.nonempty_ext : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  intro hE C T p _ y τ hC
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible τ.V
  have hK := IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)
  have hs := IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb T.L.L τ.φ (K := PUnit)
    (fun _ => eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (fun _ => eSec C.A) (fun _ => 1) τ.yK
    fun _ => (cubeMapOf τ.φ_cart).e_comm) T.L.rig T.L.rigGen
  obtain ⟨L, w₀, hw₀⟩ := hE τ.V (FractionRing τ.V) τ.H (eSec ((Over.pullback (Out.jK τ.V)).obj τ.H))
    (cubeMapOf (isGrpPullback_pullback τ.H (Out.jK τ.V))).e_comm (T.L.L.pull τ.φ) (pull_isLB T.L.isLB _) ρ hρ
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull τ.φ T.L.L (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) w₀ T.L.isLB
    (pull_isLB L.isLB _) hw₀ T.θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ L.isLB r (by
    obtain ⟨x, k, hk⟩ := exists_mem_basicOpen T τ (hC p y τ)
    obtain ⟨a, ha⟩ := exists_chart (pull_isLB L.isLB (pullback.fst τ.H.hom (Out.jK τ.V))) x
    have hk' := C.A.left.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff τ.φ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap τ.V (FractionRing τ.V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective τ.V _)).2 hϖ.ne_zero)
  have hc := (h0.isUnit.map (Scheme.ΓSpecIso (.of (FractionRing τ.V))).inv.hom).map
    (pullback.snd τ.H.hom (Out.jK τ.V)).appTop.hom
  refine ⟨⟨L, invMul w₀ hc.unit, isGen_invMul hw₀ _, σ, fun x i k hi hk => ?_, x₀, Opens.mem_iSup.2 ⟨b, hb⟩, hx₀⟩⟩
  have hi' : x ∈ (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))).U fun _ => i := mem_pull.2 hi
  have hk' : x ∈ (T.L.L.pull τ.φ).U fun _ => k := mem_pull.2 hk
  have e₁ := congrArg (gs (𝟙 _) x _) (hσ fun _ => i)
  have e₂ := (gs_appLE _ _ _ _ (𝟙 _) x hi' _).symm.trans (e₁.trans ((gs_mul (𝟙 _) x _ hi' _ _).trans
    (congrArg (· * _) ((gs_res (𝟙 _) x le_top hi' _).trans (gs_unit (𝟙 _) x ⊤ trivial hc.unit)))))
  rw [Category.id_comp] at e₂
  refine e₂.trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·) ((gs_unit (𝟙 _) x _ (show _ ∈ _ ⊓ _ from ⟨hi', hk'⟩) _).trans
    (congrArg Units.val (gm_invMul w₀ hc.unit x _ _ hi' hk'))) (hr x k _ hk hi')).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  exact congrArg (_ * ·) (Units.inv_mul_cancel_left _ _)

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtGenericPointOfIsDominant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem isFinite_pullback_unit_of_surjective_on_points (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ) (hG : _root_.GlobalTheory.SS.SmConn G)
    (hG' : _root_.GlobalTheory.SS.SmConn G') (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (i : G ⟶ G') [IsMonHom i]
    (hpts : ∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) :
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  unfold _root_.GlobalTheory.SS.SmConn at hG hG'
  obtain ⟨-, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨-, hsm', hsep', hqc', hgc'⟩ := hG'
  have hw : i.left ≫ G'.hom = G.hom := Over.w i
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have : ConnectedSpace G'.left := GeometricallyConnected.connectedSpace_of_subsingleton G'.hom
  have : IsIntegral G.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom
  have : IsIntegral G'.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom
  have : LocallyOfFiniteType (i.left ≫ G'.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left G'.hom
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom
  have hcl : closedPoints G'.left ⊆ Set.range i.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy)
      (pointOfClosedPoint_comp _ _ _))
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have h := congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.trans (pointOfClosedPoint_apply _ _ _ _)
  have hgen : i.left (genericPoint G.left) = genericPoint G'.left := by
    have hη : closure {genericPoint G.left} = Set.univ := genericPoint_spec G.left
    have h1 : closure (Set.range i.left) = Set.univ :=
      Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)
    have h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)} := by
      rintro _ ⟨x, rfl⟩
      exact map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)
    have h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← h1]
      simpa using closure_mono h2
    exact h3.eq (genericPoint_spec G'.left)
  have hq : i.left.QuasiFiniteAt (genericPoint G.left) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)),
        i.left.fiberι _ a = genericPoint G.left := by
      intro a
      have ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self a
      refine _root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG)
        hgG' _ ?_
      rw [← hgen]; exact ha
    have : Subsingleton (i.left.fiber (i.left (genericPoint G.left))) :=
      ⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun b => Subsingleton.elim b _
  have : LocallyQuasiFinite i.left :=
    _root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq
  have hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left
      (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left :=
    IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)
  have : LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb ‹_›
  have hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom) := by rw [hsec]; infer_instance
  have : IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have : IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ =
      (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom := by
    exact (Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans
      (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm
  have : QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
    have h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom) := inferInstance
    rw [← hw2, Category.comp_id] at h2
    exact h2
  have : IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))
  exact IsFinite.of_locallyQuasiFinite _


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.finite_ker_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G], _root_.GlobalTheory.SS.SmConn G → ∀ f : G ⟶ G, IsMonHom f →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ f = y) →
    Finite {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1} := by
  intro k _ _ G _ hG f _ hpts
  have hG0 := hG
  unfold _root_.GlobalTheory.SS.SmConn at hG0
  obtain ⟨-, hsm, -, -, hgc⟩ := hG0
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected G.hom ((η[G] : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k))
  have hK := isFinite_pullback_unit_of_surjective_on_points k G G g hG hG hg hg f hpts
  have hKhom : (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom = (pullback.snd f (η[G] : 𝟙_ _ ⟶ G)).left := by
    rw [← Over.w (pullback.snd f (η[G] : 𝟙_ _ ⟶ G))]; rfl
  have : IsFinite (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom := hKhom ▸ hK
  have hfin : Finite (pullback f (η[G] : 𝟙_ _ ⟶ G)).left := by
    have h := (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom.finite_preimage_singleton
      (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact Set.finite_univ_iff.mp
      (h.subset fun p _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
  have hone : ∀ x : {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1},
      x.1 ≫ f = 𝟙 _ ≫ (η[G] : 𝟙_ _ ⟶ G) := fun x => by
    rw [x.2, Category.id_comp]; rfl
  refine Finite.of_injective (fun x => (pullback.lift x.1 (𝟙 _) (hone x)).left
    (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))) ?_
  intro x y hxy
  have : LocallyOfFiniteType (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : Subsingleton (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : IsReduced (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hl : (pullback.lift x.1 (𝟙 _) (hone x)).left = (pullback.lift y.1 (𝟙 _) (hone y)).left := by
    have : LocallyOfFiniteType ((pullback.lift x.1 (𝟙 _) (hone x)).left ≫
        (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq (K := k) (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom Set.univ
      isClosed_univ.isLocallyClosed dense_univ (fun p _ _ => ?_) ((Over.w _).trans (Over.w _).symm)
    obtain rfl := Subsingleton.elim p (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact hxy
  have hl' : pullback.lift x.1 (𝟙 _) (hone x) = pullback.lift y.1 (𝟙 _) (hone y) := Over.OverMorphism.ext hl
  apply Subtype.ext
  have := congrArg (· ≫ pullback.fst f (η[G] : 𝟙_ _ ⟶ G)) hl'
  rw [pullback.lift_fst, pullback.lift_fst] at this
  exact this

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH.AdaptedSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.PullbackValuation GlobalTheory.IntegralCombination

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

abbrev SecGen (U : UnifPre I D A G) (k : ℕ) : Type :=
  SecOver (R := FractionRing V) (pullback.snd G.hom (jK V))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))

def toGen (U : UnifPre I D A G) (k : ℕ) : SecG U k →ₛₗ[algebraMap V (FractionRing V)] SecGen U k :=
  pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) (pullback.condition : pullback.fst G.hom (jK V) ≫ G.hom = _)
    (fun _ => (Category.comp_id _).symm)

def famAt (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (α : D.X) :
    Fam D F k →ₗ[F] SecAbF D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secScal_iff_pullAb (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.X}
    (s : SecAbF D F k α) (g : SecAb D k α) (r : V) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s (D.famφB α) (DegPre.famε k) g (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ pullAb D F k α g = toF V F r • s :=
  secScal_iff (prB_over D F) (GC.famφ_eq D F α) D.P.isLB s g _ (toF V F)
    ((Over.w (DegPre.prB D F)).symm.trans (prB_over D F)) r

theorem expandsAt_sum (U : UnifPre I D A G) (e k : ℕ) {J : Type} [Fintype J] (σ : J → SecG U k)
    (f : J → ∀ α, SecAb D.toPre k α) (h : ∀ p, U.ExpandsAt e k (σ p) (f p)) (b : J → V) :
    U.ExpandsAt e k (∑ p, b p • σ p : SecG U k) (fun α => (∑ p, b p • f p α : SecAb D.toPre k α)) := by
  have E := (Fintype.equivFin J).symm
  have H := expandsAt_comb U e k (fun p => σ (E p)) (fun p => f (E p)) (fun p => h (E p)) (fun p => b (E p))
  rw [E.sum_comp (fun p => b p • σ p)] at H
  exact (congrArg (U.ExpandsAt e k _) (funext fun α => E.sum_comp (fun p => b p • f p α))).mp H

theorem expands_toGen (U : UnifPre I D A G) (k : ℕ) (τ : SecG U k) (g : ∀ α, SecAb D.toPre k α)
    (s : Fam D.toPre (FractionRing V) k) (hτ : ∀ e, U.ExpandsAt e k τ g)
    (hs : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α s) : U.Expands k (toGen U k τ) s := by
  refine ⟨1, one_ne_zero, τ, g, ?_, fun α => ?_, hτ⟩
  · exact (secScal_iff pullback.condition _ U.LG.isLB _ _ _ (algebraMap V (FractionRing V)) rfl 1).2
      (by rw [map_one, one_smul]; rfl)
  · exact (secScal_iff_pullAb _ _ (famAt D.toPre _ k α s) _ 1).2 (by rw [map_one, one_smul]; exact hs α)


open Classical in
theorem exists_comb (hG : GlobalFnsSt) (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k) {J : Type} [Fintype J]
    (σ : J → SecG U.toUnifPre k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (h₂ : ∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') (h₃ : ∀ α, ∃ i m, α = cls i + k • m)
    (h₄ : ∀ i e, U.toUnifPre.ExpandsAt e k (σ i) (f i))
    (h₅ : ∀ i, ∃ s : Fam D.toPre (FractionRing V) k, FamOf D.toPre _ (f i) s)
    (h₆ : ∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, LB.Sec.f (f i α) j = 0)
    (h₇ : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀)))
    (s : SecGen U.toUnifPre k) : ∃ a : J → FractionRing V, s = ∑ i, a i • toGen U.toUnifPre k (σ i) := by
  obtain ⟨F, ⟨r, hr, τ, g, hτ, hg, hE⟩, -⟩ := (U.expand k hk).1 s
  have hτ' : toGen U.toUnifPre k τ = algebraMap V (FractionRing V) r • s :=
    (secScal_iff pullback.condition _ U.LG.isLB s τ _ (algebraMap V (FractionRing V)) rfl r).1 hτ
  have hg' : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α (toF V (FractionRing V) r • F) := fun α => by
    rw [map_smul]; exact (secScal_iff_pullAb _ _ _ _ r).1 (hg α)
  choose t ht using h₅
  have ht' : ∀ i α, pullAb D.toPre _ k α (f i α) = famAt D.toPre _ k α (t i) := fun i α => by
    have := (secScal_iff_pullAb _ _ (famAt D.toPre _ k α (t i)) (f i α) 1).1 (by
      have e : scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by
        unfold scal; rw [map_one, map_one]
      rw [e]; exact ht i α)
    rwa [map_one, one_smul] at this
  have hb : ∀ c : D.toPre.X, ∃ b : J → V, (∃ i₀, cls i₀ = c) →
      (show SecAb D.toPre k c from g c) = ∑ i, (if cls i = c then b i else 0) • f i c := fun c => by
    by_cases hc : ∃ i₀, cls i₀ = c
    · obtain ⟨i₀, rfl⟩ := hc
      obtain ⟨a, ha, -⟩ := h₇ i₀ (g (cls i₀))
      refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun _ => ?_⟩
      have e : (show SecAb D.toPre k (cls i₀) from g (cls i₀)) =
          ∑ i : {i // cls i = cls i₀}, a i • f i (cls i₀) :=
        SecOver.ext _ _ fun j => (ha j).trans
          (map_sum (chartLin D.toPre.P.A.hom _ j) (fun i : {i // cls i = cls i₀} => a i • f i (cls i₀)) _).symm
      rw [e, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
        Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
          (fun i _ => by rw [if_neg i.2, zero_smul]), add_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [if_pos i.2]; beta_reduce; rw [dite_eq_left i.2]
    · exact ⟨0, fun h => absurd h hc⟩
  choose b hb using hb
  have key : toF V (FractionRing V) r • F = ∑ i, toF V (FractionRing V) (b (cls i) i) • t i := by
    refine fam_ext fun α j => ?_
    obtain ⟨i₀, m, rfl⟩ := h₃ α
    refine congrArg (LB.Sec.f · j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨m, rfl⟩ ?_)
    refine (hg' _).symm.trans (Eq.trans ?_ (map_sum (famAt D.toPre _ k (cls i₀)) _ _).symm)
    refine (congrArg (pullAb D.toPre _ k (cls i₀)) (hb _ ⟨i₀, rfl⟩)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, ← ht']
    split_ifs with h
    · rw [h]
    · have z : f i (cls i₀) = 0 := SecOver.ext _ _ (h₆ i _ fun m e => h (h₂ i₀ i ⟨m, e⟩).symm)
      rw [z, map_zero (pullAb D.toPre _ k (cls i₀)), smul_zero, smul_zero]
  have E₁ := expands_toGen U.toUnifPre k τ g _ hE hg'
  have E₂ := expands_toGen U.toUnifPre k _ _ (∑ i, toF V (FractionRing V) (b (cls i) i) • t i)
    (fun e => expandsAt_sum U.toUnifPre e k σ f (fun i => h₄ i e) (fun i => b (cls i) i)) (fun α => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, map_smul, ← ht'])
  rw [key] at E₁
  have e : toGen U.toUnifPre k τ = toGen U.toUnifPre k (∑ i, b (cls i) i • σ i) :=
    ((U.expand k hk).2 _).unique E₁ E₂
  have hr' : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  refine ⟨fun i => (algebraMap V (FractionRing V) r)⁻¹ * algebraMap V _ (b (cls i) i), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hτ', map_sum] at e
  rw [← inv_smul_smul₀ hr' s, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul]

end GlobalTheory.ZH.AdaptedSpan
end
end

