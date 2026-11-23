module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0045
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfChar
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.SectionCharValues

theorem exists_section_hasValues_char (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T]
      (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  intro R _ _ _ _ T _ _ Γ χ
  have hA := PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular R T Γ
  have hm := char_mem_hopfOrder R T _ hA χ
  obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Htat.ValuationInjectivePi.mem_btOrder_iff Γ _).mp hm 1
  refine ⟨s, fun t => ?_⟩
  exact (hs t _).trans (by simp)

end PositivityTheory.HtPt.Htat.SectionCharValues

theorem PositivityTheory.HtPt.Htat.ht_char_section_of (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) :=
  @PositivityTheory.HtPt.Htat.SectionCharValues.exists_section_hasValues_char hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MgTate
section
noncomputable section

namespace PositivityTheory.HtPt.Mg

section Pairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem surjective_appTop_of_iso' {X Y : Scheme.{0}} (f : X ≅ Y) : Function.Surjective f.hom.appTop.hom := by
  have h : f.inv.appTop ≫ f.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  intro x
  refine ⟨f.inv.appTop.hom x, ?_⟩
  have hx := congrArg (fun g => g.hom x) h
  simpa using hx

theorem surj_fst_of_proper (hA : IsSemiAbelian A) (T : Over S) (hT : IsProper (pullback.snd A.hom T.hom)) :
    Function.Surjective (fst T A).left.appTop.hom := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI hAb : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    ⟨inferInstance, (inferInstance : Smooth (pullback.snd A.hom T.hom)), hT,
      (inferInstance : GeometricallyConnected (pullback.snd A.hom T.hom))⟩
  have hb := (GlobalTheory.ExpansionTotal.globalFns T.left ((Over.pullback T.hom).obj A) hAb).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom := by
    simp
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Surjective.comp (surjective_appTop_of_iso' _) hb

omit [GrpObj A] in
theorem proper_of_hom {T T' : Over S} (h : T' ⟶ T) (hT : IsProper (pullback.snd A.hom T.hom)) :
    IsProper (pullback.snd A.hom T'.hom) := by
  have e : h.left ≫ T.hom = T'.hom := Over.w h
  have q : pullback.snd A.hom (h.left ≫ T.hom) =
      (pullbackLeftPullbackSndIso A.hom T.hom h.left).inv ≫ pullback.snd (pullback.snd A.hom T.hom) h.left := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  have hp : IsProper (pullback.snd A.hom (h.left ≫ T.hom)) := by
    rw [q]
    infer_instance
  rwa [e] at hp

theorem tval_div' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left hT hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

private theorem mul_eq_mul_mul_of_ratio_eq {G : Type*} [CommGroup G] {a a' b b' c c' d d' u : G}
    (h1 : a' * a⁻¹ = b' * b⁻¹) (h2 : c' * c⁻¹ = d' * d⁻¹) (h0 : a * d = c * b * u) :
    a' * d' = c' * b' * u := by
  have hb : b' = a' * a⁻¹ * b := by rw [h1]; group
  have hd : d' = c' * c⁻¹ * d := by rw [h2]; group
  have hd0 : d = a⁻¹ * (c * b * u) := by rw [← h0]; group
  rw [hb, hd, hd0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commIsOf_change' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have h1 := tval_div' hL hT θx' θx hx r θy.pt z J hJ
  have h2 := tval_div' hL hT θy' θy hy r θx.pt z J hJ
  have h0 := H Z r z J hJ
  rw [hx, hy]
  exact mul_eq_mul_mul_of_ratio_eq h1 h2 h0

theorem weilIs_pull_of_proper (hA : IsSemiAbelian A) (hL : L.IsLB) {T T' : Over S}
    (hT : IsProper (pullback.snd A.hom T'.hom)) (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hpV, ⟨θx0, θy0, hx0, hy0⟩, hall⟩ := H (h.left p)
  let V' : T'.left.Opens := h.left ⁻¹ᵁ V
  let g : overRes V' ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    simp only [overRes, Over.mk_hom]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w h])
  have key : g ≫ overResι V = overResι V' ≫ h := by
    ext
    simp [g, overResι, morphismRestrict_ι, V']
  have hsurj : Function.Surjective (fst (overRes V') A).left.appTop.hom :=
    surj_fst_of_proper hA _ (proper_of_hom (overResι V') hT)
  have hc : unitRes V' (Units.map h.left.appTop.hom.toMonoidHom c) =
      Units.map g.left.appTop.hom.toMonoidHom (unitRes V c) := by
    have hl := congrArg Over.Hom.left key
    simp only [Over.comp_left, overResι, Over.homMk_left] at hl
    ext
    simp only [unitRes, Units.coe_map, MonoidHom.coe_coe]
    have hv := congrArg (fun f => f.appTop.hom (c : Γ(T.left, ⊤))) hl
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hv
    exact hv.symm
  obtain ⟨θx', θy', hx', hy', hcc⟩ := exists_commIsOf_pull hL g (hall θx0 θy0 hx0 hy0)
  refine ⟨V', hpV, ⟨θx', θy', ?_, ?_⟩, ?_⟩
  · rw [hx', hx0, ← Category.assoc, key, Category.assoc]
  · rw [hy', hy0, ← Category.assoc, key, Category.assoc]
  · intro θx θy hx hy
    rw [hc]
    refine commIsOf_change' hL hsurj ?_ ?_ hcc
    · rw [hx, hx', hx0, ← Category.assoc, ← key, Category.assoc]
    · rw [hy, hy', hy0, ← Category.assoc, ← key, Category.assoc]

end Pairing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem exists_section_of_finite {Z : Scheme.{0}} {k K : Type} [Field k] [IsAlgClosed k] [Field K] (i : k →+* K)
    (f : Z ⟶ Sp k) [LocallyOfFiniteType f] (hf : Finite {p : Sp k ⟶ Z // p ≫ f = 𝟙 _}) (w : Sp K ⟶ Z)
    (hw : w ≫ f = spMap i) : ∃ p : Sp k ⟶ Z, p ≫ f = 𝟙 _ ∧ w = spMap i ≫ p := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f
  haveI : Finite (closedPoints Z) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have hz : IsClosed ({w (IsLocalRing.closedPoint K)} : Set Z) := by
    set z := w (IsLocalRing.closedPoint K)
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isClosed_closure (s := ({z} : Set Z))).isLocallyClosed
    have hfin : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
      (Set.toFinite (closedPoints Z)).subset Set.inter_subset_right
    have hcl : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
      rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
      exact hfin.isClosed_biUnion (fun c hc => hc.2)
    rw [hcl.closure_eq] at h1
    have hm : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
      rw [h1]
      first
        | exact subset_closure (Set.mem_singleton z)
        | exact subset_closure (subset_closure (Set.mem_singleton z))
    exact hm.2
  refine ⟨pointOfClosedPoint f _ hz, pointOfClosedPoint_comp f _ hz, ?_⟩
  have hdesc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z w
  set φ := Z.descResidueField (Scheme.stalkClosedPointTo w)
  have hφ : Spec.map φ = spMap i ≫ Spec.map (residueFieldIsoBase f _ hz).hom := by
    have e1 : w ≫ f = Spec.map φ ≫ Spec.map (residueFieldIsoBase f _ hz).inv := by
      rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdesc]
    rw [← hw, e1, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.comp_id]
  rw [pointOfClosedPoint, ← Category.assoc, ← hφ, hdesc]

theorem torsion_desc {X : Scheme.{0}} (G : Over X) [GrpObj G] [LocallyOfFiniteType G.hom] {k K : Type} [Field k]
    [IsAlgClosed k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) (n : ℕ) (hf : Finite {g : Over.mk x ⟶ G // g ^ n = 1})
    (g : Over.mk (spMap i ≫ x) ⟶ G) (hg : g ^ n = 1) : ∃ y : Over.mk x ⟶ G, y ^ n = 1 ∧ extPt i x ≫ y = g := by
  let Kn : Over X := pullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)
  let π : Kn ⟶ G := pullback.fst _ _
  have hπ0 : π ≫ (𝟙 G) ^ n = 1 := by
    rw [pullback.condition, comp_one]
  have hπ : ∀ {Y : Over X} (q : Y ⟶ Kn), (q ≫ π) ^ n = 1 := by
    intro Y q
    rw [← Category.comp_id (q ≫ π), ← comp_pow, Category.assoc, hπ0, comp_one]
  have hmk : ∀ {Y : Over X} (a : Y ⟶ G), a ^ n = 1 → a ≫ (𝟙 G) ^ n = toUnit Y ≫ (1 : 𝟙_ (Over X) ⟶ G) := by
    intro Y a ha
    rw [comp_pow, Category.comp_id, ha, comp_one]
  have hfac : ∀ {Y : Over X} (a : Y ⟶ G) (ha : a ^ n = 1) (q : Y ⟶ Kn), q ≫ π = a →
      q = pullback.lift a (toUnit Y) (hmk a ha) := by
    intro Y a ha q hq
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hq
    · exact Subsingleton.elim _ _
  haveI h1lft : LocallyOfFiniteType (1 : 𝟙_ (Over X) ⟶ G).left := by
    have hc : (1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom = 𝟙 _ := Over.w _
    haveI : LocallyOfFiniteType ((1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  haveI hπlft : LocallyOfFiniteType π.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      ((IsPullback.of_hasPullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)).map (Over.forget X)).flip h1lft
  haveI : LocallyOfFiniteType Kn.hom := by
    rw [← Over.w π]
    infer_instance
  let fZ : pullback Kn.hom x ⟶ Sp k := pullback.snd Kn.hom x
  have hq : ∀ p : Sp k ⟶ pullback Kn.hom x, p ≫ fZ = 𝟙 _ →
      (p ≫ pullback.fst Kn.hom x) ≫ Kn.hom = (Over.mk x).hom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ fZ) ≫ x = x
    rw [hp, Category.id_comp]
  have hfin : Finite {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _} := by
    refine Finite.of_surjective (fun a : {a : Over.mk x ⟶ G // a ^ n = 1} =>
      (⟨pullback.lift (pullback.lift a.1 (toUnit _) (hmk a.1 a.2)).left (𝟙 _)
        (by rw [Over.w, Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩ :
        {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _})) ?_
    rintro ⟨p, hp⟩
    let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
    refine ⟨⟨q ≫ π, hπ q⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hfac (q ≫ π) (hπ q) q rfl]
      rfl
    · rw [pullback.lift_snd]
      exact hp.symm
  let w : Sp K ⟶ pullback Kn.hom x := pullback.lift (pullback.lift g (toUnit _) (hmk g hg)).left (spMap i)
    (by rw [Over.w]; rfl)
  obtain ⟨p, hp, hwp⟩ := exists_section_of_finite i fZ hfin w (pullback.lift_snd _ _ _)
  let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
  refine ⟨q ≫ π, hπ q, ?_⟩
  ext
  have e1 : w ≫ pullback.fst Kn.hom x = (pullback.lift g (toUnit _) (hmk g hg)).left := pullback.lift_fst _ _ _
  have e2 := congrArg Over.Hom.left (pullback.lift_fst g (toUnit _) (hmk g hg))
  rw [Over.comp_left] at e2
  rw [← e2, ← e1, hwp]
  simp [q, extPt, π]

theorem unitOn_map {k K : Type} [Field k] [Field K] (i : k →+* K) (c : kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  have := congrArg (fun q => q.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))
  exact this.symm

end PositivityTheory.HtPt.Mg
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ResFiniteOpenBtOrder
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Mk

variable (hE : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective)
include hE

theorem sub_eq_top_of : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  Htat.bt_sub_eq_top_of @Htat.hens_normal hE @Htat.reg_pull


omit hE in
theorem exists_ind {R T H : Type} [CommRing R] [CommGroup T] [CommGroup H] (K : Subgroup T) (A : Subalgebra R (K → R))
    (hA : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A) (α : H →* T) (g : H → R)
    (hg : ∀ h₀, ∃ a ∈ A, ∀ (h : H) (hh : α h ∈ K), a ⟨α h, hh⟩ = g (h₀ * h)) :
    ∃ f ∈ indOrder K.subtype A, ∀ h, f (α h) = g h := by
  have key : ∀ q : T ⧸ K, ∃ r : T, (QuotientGroup.mk r : T ⧸ K) = q ∧ ∃ a ∈ A,
      ∀ (h : H) (hh : r⁻¹ * α h ∈ K), a ⟨r⁻¹ * α h, hh⟩ = g h := by
    intro q
    by_cases hq : ∃ h₀, (QuotientGroup.mk (α h₀) : T ⧸ K) = q
    · obtain ⟨h₀, h0⟩ := hq
      obtain ⟨a, ha, hag⟩ := hg h₀
      refine ⟨α h₀, h0, a, ha, fun h hh => ?_⟩
      have := hag (h₀⁻¹ * h) (by simpa using hh)
      simpa using this
    · refine ⟨q.out, q.out_eq, 0, A.zero_mem, fun h hh => (hq ⟨h, ?_⟩).elim⟩
      rw [← QuotientGroup.eq.2 hh]
      exact q.out_eq
  choose r hr a ha hag using key
  have hm : ∀ t : T, (r (QuotientGroup.mk t))⁻¹ * t ∈ K := fun t => QuotientGroup.eq.1 (hr _)
  refine ⟨fun t => a (QuotientGroup.mk t) ⟨_, hm t⟩, fun t => ?_, fun h => hag _ h _⟩
  have := hA _ (ha (QuotientGroup.mk t)) ⟨_, hm t⟩
  convert this using 1
  funext k
  have e : (QuotientGroup.mk (t * K.subtype k) : T ⧸ K) = QuotientGroup.mk t :=
    QuotientGroup.mk_mul_of_mem t k.2
  have gen : ∀ (q q' : T ⧸ K) (e : q = q') (x : T) (h : (r q)⁻¹ * x ∈ K) (h' : (r q')⁻¹ * x ∈ K),
      a q ⟨_, h⟩ = a q' ⟨_, h'⟩ := by
    intro q q' e x h h'
    subst e; rfl
  refine (gen _ _ e _ (hm _) (by rw [← e]; exact hm _)).trans ?_
  congr 1
  apply Subtype.ext
  exact (_root_.mul_assoc _ _ _).symm

section
variable {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T : Type} [CommGroup T] [Finite T]

theorem order_ind (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    ∃ (K : Subgroup T) (A : Subalgebra R (K → R)), (∀ t, t ∈ K ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧
      Γ.btOrder ⊤ = indOrder K.subtype A ∧
      (∀ f : K → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : K) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t)) ∧
      ∀ s : Γ(Γ.G.left, U), ∃ f ∈ A, ∀ (t : K) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  obtain ⟨K, A, hK, hA, hAf⟩ := Twhopf.sub_order R T Γ U hU
  refine ⟨K, A, hK, hA, ?_, hAf, fun s => ?_⟩
  · rw [← sub_eq_top_of hE R T Γ U hU]
    ext f
    rw [Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hK t').2 h⟩ h⟩
  · have hU' := SubOrder.isAffineOpen_of_fin Γ hU
    letI : Algebra R Γ(Γ.G.left, U) := (SubOrder.secRho Γ hU').toAlgebra
    have hρ : hU'.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
      SubOrder.fromSpec_hom Γ hU'
    have hfin := SubOrder.sec_finite hρ hU
    have hval : ∀ (t : K), ∃ r : R, algebraMap R (FractionRing R) r = SubOrder.valAlg hρ t ((hK t).1 t.2) s := by
      intro t
      have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
      exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (SubOrder.valAlg hρ t ((hK t).1 t.2)))
    choose f hf using hval
    exact ⟨f, (hAf f).2 ⟨s, fun t h => (hf t).symm⟩, fun t h => (hf t).symm⟩

theorem res_fin_core (Γ : QFGroup R T) {H : Type} [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G)
    (hmul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ₁.G), (x * y) ≫ a = (x ≫ a) * (y ≫ a))
    (α : H →* T) (hα : ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) (hcl : IsClosedImmersion a.left) (U : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) : Γ₁.IsFinOpenSub (a.left ⁻¹ᵁ U) ∧ resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  let φ : ∀ S : Over (Spec (CommRingCat.of R)), (S ⟶ Γ₁.G) →* (S ⟶ Γ.G) := fun S =>
    MonoidHom.mk' (fun x => x ≫ a) (hmul S)
  have hφ : ∀ S x, φ S x = x ≫ a := fun _ _ => rfl
  have happ : ∀ {S : Over (Spec (CommRingCat.of R))} (x : S ⟶ Γ₁.G) z, (x ≫ a).left z = a.left (x.left z) := by
    intro S x z
    simp
  have h1 : Γ₁.IsFinOpenSub (a.left ⁻¹ᵁ U) := by
    refine ⟨?_, fun x => ?_, fun S x y hx hy z => ?_, fun S x hx z => ?_⟩
    · have := hU.finite
      rw [← Over.w a, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      infer_instance
    · have e : η[Γ₁.G] ≫ a = η[Γ.G] := by
        have := map_one (φ (𝟙_ _))
        rw [hφ] at this
        simpa [Hom.one_def] using this
      change a.left (η[Γ₁.G].left x) ∈ U
      rw [← happ, e]
      exact hU.one x
    · change a.left _ ∈ U
      rw [← happ, hmul]
      exact hU.mul S _ _ (fun z => by rw [happ]; exact hx z) (fun z => by rw [happ]; exact hy z) z
    · change a.left _ ∈ U
      rw [← happ, ← hφ, map_inv, hφ]
      exact hU.inv S _ (fun z => by rw [happ]; exact hx z) z
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.T.btOrder_comap_hom R H Γ₁ T Γ a α hα f hf
  · intro g hg
    obtain ⟨K, A, hK, hA, hind, -, hsec⟩ := order_ind hE Γ U hU
    rw [← sub_eq_top_of hE R H Γ₁ _ h1, Twhopf.mem_order] at hg
    have hUa := SubOrder.isAffineOpen_of_fin Γ hU
    have hsurj : Function.Surjective (a.left.app U) := a.left.app_surjective U hUa
    obtain ⟨f, hf, hfg⟩ := exists_ind K A (Twhopf.translate_mem R K A hA) α g (fun h₀ => by
      obtain ⟨s₁, hs₁⟩ := (Twhopf.reg_iff R H Γ₁ _ _).1 (hg h₀)
      obtain ⟨s, rfl⟩ := hsurj s₁
      obtain ⟨b, hb, hbs⟩ := hsec s
      refine ⟨b, hb, fun h hh => IsFractionRing.injective R (FractionRing R) ?_⟩
      have e : (Γ₁.pt h).left ≫ a.left = (Γ.pt (α h)).left := by rw [← Over.comp_left, hα]
      have h2 := (hK _).1 hh
      have h3 : ⊤ ≤ ((Γ₁.pt h).left ≫ a.left) ⁻¹ᵁ U := e ▸ h2
      rw [← hbs ⟨_, hh⟩ h2, ← hs₁ h h3, ← Htat.Pull.valAt_comp _ _ _ h3]
      exact Htat.Pull.valAt_congr e.symm _ _ _ _)
    rw [hind]
    exact ⟨f, hf, funext hfg⟩

end

theorem res_core {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T : Type} [CommGroup T] [Finite T]
    (Γ : QFGroup R T) {H : Type} [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G)
    (hmul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ₁.G), (x * y) ≫ a = (x ≫ a) * (y ≫ a))
    (α : H →* T) (hα : ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) (hcl : IsClosedImmersion a.left) :
    resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.T.btOrder_comap_hom R H Γ₁ T Γ a α hα f hf
  refine Htat.mem_descent R H (Subalgebra.toSubmodule (resOrder α (Γ.btOrder ⊤))) g fun P hP => ?_
  obtain ⟨R', _, _, _, _, hN, hflat, hP'⟩ := Htat.hens_normal R P
  have hinj : Function.Injective (algebraMap R R') := Htat.ValuationInjectivePi.flat_inj
  obtain ⟨κ, hκ⟩ := Htat.ValuationInjectivePi.exists_kappa hinj
  obtain ⟨Γ', F, hF⟩ := hE R T Γ R' (algebraMap R R') hinj
  obtain ⟨Γ₁', F₁, hF₁⟩ := hE R H Γ₁ R' (algebraMap R R') hinj
  have w : (F₁ ≫ a.left) ≫ Γ.G.hom = Γ₁'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, Over.w a, hF₁.cart.w]
  let a' : Γ₁'.G ⟶ Γ'.G := Over.homMk (hF.cart.lift _ _ w) (hF.cart.lift_snd _ _ w)
  have ha' : a'.left ≫ F = F₁ ≫ a.left := hF.cart.lift_fst _ _ w
  have hext : ∀ {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G), x.left ≫ F = y.left ≫ F → x = y :=
    fun x y e => Over.OverMorphism.ext (hF.cart.hom_ext e (by rw [Over.w, Over.w]))
  have hpb : IsPullback F₁ a'.left a.left F := by
    refine IsPullback.of_bot ?_ ha'.symm hF.cart
    rw [Over.w a', Over.w a]
    exact hF₁.cart
  have hcl' : IsClosedImmersion a'.left := MorphismProperty.of_isPullback hpb hcl
  have hmul' : ∀ (S : Over (Spec (CommRingCat.of R'))) (x y : S ⟶ Γ₁'.G),
      (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
    intro S x y
    let l : (S ⟶ Γ₁'.G) → (Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ₁.G) := fun z =>
      Over.homMk (z.left ≫ F₁) (by
        change (z.left ≫ F₁) ≫ _ = S.hom ≫ _
        rw [Category.assoc, hF₁.cart.w, ← Category.assoc, Over.w])
    have hl : ∀ z, (l z).left = z.left ≫ F₁ := fun _ => rfl
    have hla : ∀ z, (l z ≫ a).left = (z ≫ a').left ≫ F := fun z => by
      rw [Over.comp_left, Over.comp_left, hl, Category.assoc, Category.assoc, ha']
    apply hext
    rw [← hF.mul S _ _ _ _ (hla x) (hla y), ← hmul, Over.comp_left, Over.comp_left,
      hF₁.mul S _ _ _ _ (hl x) (hl y), Category.assoc, Category.assoc, ha']
  have hα' : ∀ h, Γ₁'.pt h ≫ a' = Γ'.pt (α h) := by
    intro h
    apply hext
    rw [Over.comp_left, Category.assoc, ha', ← Category.assoc, _root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R H Γ₁ R' Γ₁' F₁ hF₁ κ hκ h,
      _root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ, Category.assoc, ← Over.comp_left, hα]
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := Twhopf.finite_sub R' T Γ' U hUfin hUcl
  have hres := (res_fin_core hE Γ' Γ₁' a' hmul' α hα' hcl' U hU).2
  refine ⟨R', inferInstance, inferInstance, inferInstance, hflat, hP', ?_⟩
  have h1 := OrderApi.comp_mem_extOrder (algebraMap R R') hg
  rw [← Htat.bt_flat_bc R H Γ₁ R' Γ₁' F₁ hF₁ hflat, ← hres, Htat.bt_flat_bc R T Γ R' Γ' F hF hflat] at h1
  obtain ⟨f', hf', e⟩ := h1
  rw [← e]
  have hf'' := (Htat.ext_span R T R' _ _ f').1 hf'
  clear e hf'
  induction hf'' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact Submodule.subset_span ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem res_bt_order_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsClosedImmersion a.left → resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  intro R _ _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hα hcl
  exact res_core hE Γ Γ₁ a (fun S x y => MonObj.mul_comp x y a) α hα hcl

end PositivityTheory.HtPt.Mk
end

