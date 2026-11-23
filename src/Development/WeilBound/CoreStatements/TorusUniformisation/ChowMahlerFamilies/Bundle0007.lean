module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NormalLatticeRange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace PositivityTheory.Xgn.NormalLatticeRange

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem specMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp]

theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem transport {S : Scheme.{0}} (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    ∃ v' : epsAt x' ⟶ G, IsTanAt G x' v' ∧ v'.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left) ?_, ?_, rfl⟩
  · have hw := Over.w v
    simp only [Category.assoc, hw, epsAt, Over.mk_hom]
    rw [← hx, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  · unfold IsTanAt at hv ⊢
    rw [one_left] at hv ⊢
    simp only [Over.homMk_left]
    have hring : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ) =
        φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hv, ← hx, Category.assoc]

end PositivityTheory.Xgn.NormalLatticeRange

open PositivityTheory.Xgn.NormalLatticeRange in
theorem PositivityTheory.Xgn.normal_lattice_range : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  intro X Ω _ ξ h G _ E _ _ M p Ep _ _ Mp j hj
  simp only [spMap] at hj
  have hgen1 : (genMap ξ p).comp (regIso h p).symm.toRingHom = algebraMap (regAt ξ p) Ω :=
    RingHom.ext fun r => congrArg Subtype.val ((regIso h p).apply_symm_apply r)
  have hgen2 : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun a => rfl
  apply Set.Subset.antisymm
  · have hle : M.lat p ≤ LinearMap.range j := by
      apply Submodule.span_le.2
      rintro e ⟨v, hv, he⟩
      obtain ⟨v', hv', hv'l⟩ :=
        transport G (regIso h p).toRingHom (X.fromSpecStalk p.1) (regPt h p) rfl v hv
      obtain ⟨e', he'⟩ := Mp.onto v' hv'
      refine ⟨e', M.inj (Over.OverMorphism.ext ?_)⟩
      rw [hj, he', hv'l, he, ← Category.assoc, specMap_dualMap_comp, hgen2]
    exact fun e he => LinearMap.mem_range.1 (hle he)
  · rintro _ ⟨e', rfl⟩
    have hx : Spec.map (CommRingCat.ofHom (regIso h p).symm.toRingHom) ≫ regPt h p =
        X.fromSpecStalk p.1 := by
      have hid : (regIso h p).symm.toRingHom.comp (regIso h p).toRingHom = RingHom.id _ := by
        ext a
        simp
      simp only [regPt, spMap]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hid]
      simp
    obtain ⟨v', hv', hv'l⟩ := transport G (regIso h p).symm.toRingHom (regPt h p) (X.fromSpecStalk p.1) hx
      (Mp.pt e') (Mp.tan e')
    exact Submodule.subset_span ⟨v', hv', by rw [hj, hv'l, ← Category.assoc, specMap_dualMap_comp, hgen1]⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValuationAtCentreOrder
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ValuationOrder

theorem specializes_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    (Spec.map φ ≫ z) (IsLocalRing.closedPoint S) ⤳ z (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint
    ((Spec.map φ) (IsLocalRing.closedPoint S))).map z.continuous
  exact (Scheme.Hom.comp_apply (Spec.map φ) z (IsLocalRing.closedPoint S)).symm ▸ h

theorem stalk_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    X.presheaf.stalkSpecializes (specializes_comp z φ) ≫ Scheme.stalkClosedPointTo (Spec.map φ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (z (IsLocalRing.closedPoint R))), Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_spec {p q : X} (hp : genPt ξ ⤳ p) (hpq : p ⤳ q) (s : X.presheaf.stalk q) :
    genMap ξ ⟨p, hp⟩ ((X.presheaf.stalkSpecializes hpq).hom s) = genMap ξ ⟨q, hp.trans hpq⟩ s := by
  have h1 : X.presheaf.stalkSpecializes hpq ≫ X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ =
      X.presheaf.stalkSpecializes (hp.trans hpq) ≫ Scheme.stalkClosedPointTo ξ := by
    rw [← X.presheaf.stalkSpecializes_comp hp hpq]
    exact (Category.assoc _ _ _).symm
  have h2 := congrArg (fun f => CommRingCat.Hom.hom f s) h1
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem valAt_comp {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [IsLocalRing C]
    (φ : V →+* C) {z : Spec (CommRingCat.of V) ⟶ X}
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) {a : Ω} {r : V} (hv : ValAt ξ z a r) :
    ValAt ξ (Spec.map (CommRingCat.ofHom φ) ≫ z) a (φ r) := by
  obtain ⟨_, s, rfl, rfl⟩ := hv
  refine ⟨h, (X.presheaf.stalkSpecializes (specializes_comp z (CommRingCat.ofHom φ))).hom s,
    genMap_spec h _ s, ?_⟩
  exact congrArg (fun f => f.hom s) (stalk_comp z (CommRingCat.ofHom φ))

section

variable {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') :
    r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_pow {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem ne_zero_of_valAt {a : Ω} {r : R} (h : ValAt ξ z a r) (hr : IsUnit r) : a ≠ 0 := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t hr
  exact (ht.map (genMap ξ ⟨centre z, hz⟩)).ne_zero

theorem exists_unit_val (hξ : IsCptGen ξ) {h : genPt ξ ⤳ centre z} {b : Ω} (hb : unitAt ξ ⟨centre z, h⟩ b) :
    ∃ u : Rˣ, ValAt ξ z b u := by
  obtain ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩ := hb
  have h1 : ValAt ξ z b _ := ⟨h, s, hs, rfl⟩
  have h2 : ValAt ξ z b⁻¹ _ := ⟨h, t, ht, rfl⟩
  have h3 := valAt_mul h1 h2
  rw [mul_inv_cancel₀ h0] at h3
  have h4 : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩
  exact ⟨Units.mkOfMulEqOne _ _ (valAt_unique hξ h3 h4), h1⟩

end

end PositivityTheory.Xgn.ValuationOrder

open PositivityTheory.Xgn.ValuationOrder in
theorem PositivityTheory.Xgn.valuation_at_centre_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  intro X Ω _ ξ L σ ϖ M a V C _ _ _ _ z h e γ π hξ hord hgen hγ hπ hπ0
  have hu : unitAt ξ ⟨centre z, h⟩ ((σ / e) ^ M / ϖ ^ a) := (orderAt_iff_div hgen.1 hgen.2).1 hord
  obtain ⟨u, hval⟩ := exists_unit_val hξ hu
  have hc := valAt_comp (algebraMap V C) hγ.1 hval
  have hϖ : ϖ ≠ 0 := ne_zero_of_valAt hπ hπ0.isUnit
  have hM := valAt_pow hγ M
  refine ⟨u, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · have h1 := valAt_mul (valAt_pow hπ n) hc
    rw [zpow_natCast, mul_div_cancel₀ _ (pow_ne_zero n hϖ)] at h1
    rw [zpow_natCast]
    exact valAt_unique hξ hM h1
  · have h1 := valAt_mul hM (valAt_pow hπ n)
    rw [zpow_neg, zpow_natCast, div_inv_eq_mul] at hc
    rw [← valAt_unique hξ h1 hc, zpow_neg, zpow_natCast]
    field_simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValuationCentreExists
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.valuation_centre_exists : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  intro X Ω _ ξ O _ _ _ s _ hξ V hV
  let φ : O →+* V := (algebraMap O Ω).codRestrict V hV
  have hcomp : CommRingCat.ofHom (algebraMap O Ω) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    ext x
    rfl
  have hsq : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hξ, hcomp, Spec.map_comp]
  have hE : ValuativeCriterion.Existence s := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  obtain ⟨l, hl⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l = ξ := by
    obtain ⟨⟨l, hl, -⟩⟩ := (hE ⟨↥V, Ω, ξ, Spec.map (CommRingCat.ofHom φ), ⟨hsq⟩⟩).exists_lift
    exact ⟨l, hl⟩
  subst hl
  have hspec : (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ l (IsLocalRing.closedPoint (CommRingCat.of V)) :=
    (IsLocalRing.specializes_closedPoint
      ((Spec.map (CommRingCat.ofHom (algebraMap V Ω))) (IsLocalRing.closedPoint (CommRingCat.of Ω)))).map
        l.continuous
  have h : TopCat.Presheaf.stalkSpecializes X.presheaf hspec ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l) =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (l (IsLocalRing.closedPoint (CommRingCat.of V))))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have key : ∀ g, GlobalTheory.CompanionTheory.Ar.genMap (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      ⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩ g =
        ((Scheme.stalkClosedPointTo l).hom g : Ω) := by
    intro g
    exact congrArg (fun ψ => ψ.hom g) h
  refine ⟨⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    rw [key g]
    exact ((Scheme.stalkClosedPointTo l).hom g).2
  · intro a ha ha0 hinv
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    refine ⟨g, ?_, rfl⟩
    have hloc := Scheme.isLocalHom_stalkClosedPointTo' l
    apply (isUnit_map_iff (Scheme.stalkClosedPointTo l).hom g).mp
    rw [key g] at ha0 hinv
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPtAfType
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_af_type

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

theorem mem_mul_std (RC : Subalgebra o C) (p : ℕ) {X : Type} (f : X → C) :
    f ∈ mulLat (p : C) (stdLat RC X) ↔ ∀ y, f y ∈ pInt (C := C) RC p := by
  constructor
  · rintro ⟨g, hg, rfl⟩ y
    have hy : g y ∈ RC := hg y (Set.mem_univ y)
    refine Submodule.mem_span_singleton.2 ⟨⟨g y, hy⟩, ?_⟩
    change g y * (p : C) = (p : C) * g y
    ring
  · intro h
    choose a ha using fun y => Submodule.mem_span_singleton.1 (h y)
    refine ⟨fun y => (a y : C), fun y _ => (a y).2, ?_⟩
    funext y
    rw [← ha y]
    change (p : C) * (a y : C) = (a y : C) * (p : C)
    ring

theorem pInt_mem (RC : Subalgebra o C) (p : ℕ) {c : C} (h : c ∈ pInt (C := C) RC p) : c ∈ RC := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
  change (a : C) * (p : C) ∈ RC
  exact RC.mul_mem a.2 (natCast_mem RC p)

theorem coe_mem_pInt (RC : Subalgebra o C) (p : ℕ) {c : RC} (h : c ∈ Ideal.span {(p : RC)}) :
    (c : C) ∈ pInt (C := C) RC p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  change (a : C) * (p : C) = _
  push_cast
  rfl

theorem mem_af (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
    (D : LieLatticeData C F n Sg r s) (χ : F → C) (u : Fin n → C) :
    u ∈ D.af RC p χ ↔ ∃ g ∈ D.M, ∀ y : Fin n → F,
      (∑ k, u k * χ (y k)) - g y ∈ pInt (C := C) RC p := by
  have hl : ∀ y : Fin n → F, linMap n χ u y = ∑ k, u k * χ (y k) := by
    intro y
    simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply]
  change linMap n χ u ∈ D.M ⊔ mulLat (p : C) (stdLat RC _) ↔ _
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, f, hf, h⟩
    refine ⟨g, hg, fun y => ?_⟩
    have := (mem_mul_std RC p f).1 hf y
    rw [← hl, ← h]
    simpa using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, linMap n χ u - g, (mem_mul_std RC p _).2 fun y => ?_, by abel⟩
    rw [Pi.sub_apply, hl]
    exact h y

theorem mem_dotDual (RC : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (u : Fin m → C) :
    u ∈ dotDual RC L ↔ ∀ l ∈ L, l ⬝ᵥ u ∈ RC := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem congr_lin (RC : Subalgebra o C) (p : ℕ) {I : Type} [Fintype I] {n : ℕ}
    (Pm : Matrix (Fin n) I RC) (a : I → RC) (b : Fin n → RC)
    (h : ∀ k, (∑ j, Pm k j * a j) - b k ∈ Ideal.span {(p : RC)}) (l : Fin n → RC) :
    algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C)
      ∈ pInt (C := C) RC p := by
  have h1 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) ∈ Ideal.span {(p : RC)} :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k)
  have h2 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k)
      = (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k := by
    simp only [mul_sub, Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [h2] at h1
  have h3 := coe_mem_pInt RC p h1
  have h4 : (((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k : RC) : C)
      = algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C) := by
    change algebraMap RC C ((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum (algebraMap RC C) (fun k => l k * b k)]
    simp only [map_mul]
    rfl
  rwa [h4] at h3

theorem dot_eq (RC : Subalgebra o C) {I : Type} [Fintype I] {n : ℕ}
    (J : Matrix I (Fin n) RC) (l : I → RC) (u : Fin n → C) :
    (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j)
      = (fun k => ((Matrix.vecMul l J k : RC) : C)) ⬝ᵥ u := by
  have h : ∀ k, ((Matrix.vecMul l J k : RC) : C) = ∑ j, (l j : C) * algebraMap RC C (J j k) := by
    intro k
    change algebraMap RC C (∑ j, l j * J j k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]
    rfl
  simp only [h, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

end PositivityTheory.Xgn.A_pt_af_type

open PositivityTheory.Xgn.A_pt_af_type in
theorem PositivityTheory.Xgn.t_pt_af_type : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC := by
  intro o C _ _ _ RC p _ I _ _ MM hint F _ _ n Sg r s D χ h0 h1 i π hπ hst hM Pm J hPJ hc hAF
  have hMM : ∀ g, g ∈ D.M ↔ ∃ h ∈ MM, (fun y => h (i y)) = g := by
    intro g
    rw [← hM]
    exact Submodule.mem_map
  have P1 : ∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔
      Matrix.vecMul l Pm ∈ afLat p MM := by
    intro l
    rw [mem_af]
    constructor
    · rintro ⟨g, hg, h⟩
      obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
      refine ⟨_, hst h' hh', fun x => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((x j).val : RC)) (fun k => χ (π x k))
        (fun k => hc k x) l
      have e2 := h (π x)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
    · rintro ⟨g, hg, h⟩
      refine ⟨_, (hMM _).2 ⟨g, hg, rfl⟩, fun y => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((i y j).val : RC)) (fun k => χ (π (i y) k))
        (fun k => hc k (i y)) l
      rw [hπ] at e1
      have e2 := h (i y)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
  have hco : ∀ u ∈ D.af RC p (fun a => (χ a : C)), ∀ k, u k ∈ RC := by
    intro u hu k
    obtain ⟨g, hg, h⟩ := (mem_af RC p D _ u).1 hu
    obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
    have e1 := pInt_mem RC p (h (Pi.single k 1))
    have e2 : ∑ j, u j * ((χ ((Pi.single k 1 : Fin n → F) j) : RC) : C) = u k := by
      rw [Finset.sum_eq_single k]
      · simp [h1]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj, h0]
      · simp
    rw [e2] at e1
    have e3 : h' (i (Pi.single k 1)) ∈ RC := by
      have := hint hh'
      obtain ⟨a, ha⟩ := this (i (Pi.single k 1))
      rw [← ha]
      exact a.2
    simpa using RC.add_mem e1 e3
  refine ⟨P1, fun u => ?_⟩
  rw [LieLatticeData.hh, mem_dotDual]
  constructor
  · intro h l hl
    rw [dot_eq]
    refine h _ ((P1 _).2 ?_)
    rw [Matrix.vecMul_vecMul]
    exact hAF l hl
  · intro h l hl
    let l' : Fin n → RC := fun k => ⟨l k, hco l hl k⟩
    have e := h _ ((P1 l').1 hl)
    rw [dot_eq, Matrix.vecMul_vecMul, hPJ, Matrix.vecMul_one] at e
    exact e
end

