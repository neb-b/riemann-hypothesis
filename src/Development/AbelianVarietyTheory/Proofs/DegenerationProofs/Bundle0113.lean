module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ExtLB

open IsLocalRing

variable {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]

abbrev cp (A : Type) [CommRing A] [IsLocalRing A] : Sp A := closedPoint A

theorem top_le [IsLocalRing A] (f : Sp A ⟶ X) {U : X.Opens} (h : f (cp A) ∈ U) : ⊤ ≤ f ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) f h).ge

def ev (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom).hom

def toSt (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sp A).presheaf.germ ⊤ y trivial).hom

theorem gs_eq_toSt (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (y : Sp A) (a : Γ(X, U)) :
    gs f y U a = toSt y (ev f U h a) := by
  rw [gs_eq f y U (h (Set.mem_univ y))]
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
    (Sp A).presheaf.germ ⊤ y trivial).hom a
  rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.appLE, Category.assoc]
  exact (TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE h) y (Set.mem_univ y) _).symm

theorem ev_comp (g : A →+* B) (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U)
    (a : Γ(X, U)) : ev (spMap g ≫ f) U h' a = g (ev f U h a) := by
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ CommRingCat.ofHom g).hom a
  rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun q => (q ≫ (Scheme.ΓSpecIso (.of B)).hom).hom a)
    (Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h le_top).symm

theorem toSt_bijective [IsLocalRing A] : Function.Bijective (toSt (cp A)) := by
  have : toSt (cp A) = (stalkClosedPointIso (.of A)).inv.hom := by
    rw [toSt, ← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  rw [this]
  exact (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective

theorem isUnit_toSt [IsLocalRing A] (a : A) : IsUnit (toSt (cp A) a) ↔ IsUnit a :=
  MulEquiv.isUnit_map (RingEquiv.ofBijective _ toSt_bijective)

theorem exists_lift (g : A →+* B) (hg : Function.Injective g) (x : Sp B ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (hr : ∀ a, ∃ r, g r = ev x U h a) : ∃ χ : Sp A ⟶ X, spMap g ≫ χ = x := by
  let e : A ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hg (congrArg Subtype.val hab), g.rangeRestrict_surjective⟩
  let ρ : Γ(X, U) →+* A := e.symm.toRingHom.comp ((ev x U h).codRestrict g.range hr)
  have hρ : g.comp ρ = ev x U h := RingHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply ((ev x U h).codRestrict g.range hr a))
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ hU.fromSpec, ?_⟩
  have e₁ := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e₁
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ, ev, CommRingCat.ofHom_hom, Spec.map_comp,
    Category.assoc, e₁, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

variable {L : LB X}

theorem le_chart {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

theorem le_chart' {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ (𝟙 (Sp A) : Sp A ⟶ Sp A) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => h hy

def sv {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : A :=
  ev x _ (le_chart h) (s.f fun _ => i)

def gv {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : Aˣ :=
  Units.map (ev (𝟙 (Sp A)) _ (le_chart' h)).toMonoidHom (e.s fun _ => i)

theorem isUnit_sv [IsLocalRing A] {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    IsUnit (sv s x h) ↔ x (cp A) ∈ nonzeroLocus s := by
  rw [mem_nonzeroLocus_iff_pull s x (cp A) (k := fun _ => i) (le_chart h (Set.mem_univ _)), ← isUnit_toSt]
  exact (congrArg IsUnit (gs_eq_toSt x _ (le_chart h) _ _)).to_iff.symm

theorem gs_sv {d : ℕ} (s : H0 L d) (g : A →+* B) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    gs (spMap g ≫ x) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (s.f fun _ => i) = toSt y (g (sv s x h)) :=
  (gs_eq_toSt (spMap g ≫ x) _ (fun z _ => le_chart h (Set.mem_univ (spMap g z))) y _).trans
    (congrArg _ (ev_comp g x _ (le_chart h) _ _))

theorem gm_gv (g : A →+* B) {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    (gm (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (e.s fun _ => i)).val = toSt y (g (gv e h).val) := by
  have hm : ⊤ ≤ (spMap g ≫ 𝟙 _) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
    fun _ _ => le_chart' h (Set.mem_univ _)
  refine (gs_unit (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (hm (Set.mem_univ y)) _).symm.trans ?_
  refine (congrArg (fun q => gs q y _ _) (Category.comp_id (spMap g)).symm).trans ?_
  exact (gs_eq_toSt _ _ hm _ _).trans (congrArg _ (ev_comp g (𝟙 _) _ (le_chart' h) _ _))

theorem quot_eq (hL : L.IsLB) {C : Type} [CommRing C] [IsLocalRing C] (g : A →+* C) (g' : B →+* C)
    {x : Sp A ⟶ X} {χ : Sp B ⟶ X} (hc : spMap g ≫ x = spMap g' ≫ χ) (e : LB.Gen (L.pull x)) (he : e.IsGen)
    (e' : LB.Gen (L.pull χ))
    (hv : ∀ z J, Good L z J → val (L := L) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap g) z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (spMap g') z J)
    {i i' : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (h' : ⊤ ≤ χ ⁻¹ᵁ L.U i') {d : ℕ} (s : H0 L d) :
    g (sv s x h * ((gv e h)⁻¹ ^ d).val) = g' (sv s χ h' * ((gv e' h')⁻¹ ^ d).val) := by
  have m : (spMap g ≫ x) (cp C) ∈ L.U i := h (Set.mem_univ _)
  have m' : (spMap g ≫ x) (cp C) ∈ L.U i' := by rw [hc]; exact h' (Set.mem_univ _)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL (cp C) (fun _ : PUnit => spMap g ≫ x) (fun _ => i') (fun _ _ _ => rfl)
    (fun _ => m')
  have v := hv _ J hJ
  rw [val_of (L := L) (φ := fun _ : PUnit => x) e _ _ J (fun _ => i') (fun _ => hJi PUnit.unit),
    val_of (L := L) (φ := fun _ : PUnit => χ) e' _ _ J (fun _ => i') (fun _ => hc ▸ hJi PUnit.unit),
    gen_trans (L := L) (φ := fun _ : PUnit => x) he (spMap g) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m), trF, Fintype.prod_unique, zpow_one] at v
  have v' := congrArg Units.val v
  rw [Units.val_mul, gm_gv g e h, gm_gv g' e' h'] at v'
  have w := sec_trans s (spMap g ≫ x) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m)
  rw [trF, Fintype.prod_unique, zpow_natCast, Category.comp_id, gs_sv s g x h, Units.val_pow_eq_pow_val] at w
  have w' := gs_sv s g' χ h' (cp C)
  rw [← hc, w] at w'
  apply toSt_bijective.1
  have u : toSt (cp C) (g (gv e h).val) * toSt (cp C) (g (gv e h)⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have u' : toSt (cp C) (g' (gv e' h').val) * toSt (cp C) (g' (gv e' h')⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  simp only [map_mul, map_pow, Units.val_pow_eq_pow_val]
  rw [← w', mul_comm (_ ^ d), _root_.mul_assoc, ← mul_pow]
  congr 2
  rw [← v'] at u'
  linear_combination (-toSt (cp C) (g (gv e h)⁻¹.val)) * u' + ((gm (spMap g ≫ x) (cp C) _ (L.g i' i)).val *
    toSt (cp C) (g' (gv e' h')⁻¹.val)) * u

theorem exists_sv_eq [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) [IsLocalRing A] {d : ℕ} (s : H0 L d)
    (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (hs : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (d * m)), sv t x h = sv s x h ^ m * ev x _ hs a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL d s).1 a
  refine ⟨m, t, toSt_bijective.1 ?_⟩
  have e := congrArg (x.stalkMap (cp A)).hom (ht (x (cp A)) (fun _ => i) (hs (Set.mem_univ _)) (h (Set.mem_univ _)))
  rw [map_mul, map_pow] at e
  have k : ∀ (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(X, U)),
      (x.stalkMap (cp A)).hom (gs (𝟙 X) (x (cp A)) U b) = toSt (cp A) (ev x U hU b) := fun U hU b =>
    (gs_stalkMap x (cp A) U (hU (Set.mem_univ _)) b).symm.trans (gs_eq_toSt x U hU _ b)
  rw [map_mul, map_pow]
  exact (k _ (le_chart h) _).symm.trans (e.trans (congrArg₂ (· * ·) (congrArg (· ^ m) (k _ (le_chart h) _)) (k _ hs _)))

theorem exists_eq_of_traits {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (q : FractionRing R)
    (H : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ w : W, gam q = algebraMap W _ w) : ∃ r : R, algebraMap R _ r = q := by
  refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV h1 _ => ?_
  let W := AdicCompletion (maximalIdeal V) V
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : R →+* W := (algebraMap V W).comp ((algebraMap R (FractionRing R)).codRestrict V h1)
  let gam : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := V) inj
  have hg : ∀ v : V, gam v = algebraMap W _ (algebraMap V W v) := fun v => IsFractionRing.lift_algebraMap inj v
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr V).comp
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := H W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ gam
    (fun r => hg ⟨_, h1 r⟩)
  by_contra hq
  have hq0 : q ≠ 0 := fun h => hq (h ▸ V.zero_mem)
  have hi : q⁻¹ ∈ V := (V.mem_or_inv_mem q).resolve_left hq
  have hu : IsUnit (algebraMap V W ⟨_, hi⟩) := IsUnit.of_mul_eq_one w (IsFractionRing.injective W (FractionRing W) (by
    rw [map_mul, ← hg, ← hw, ← map_mul, map_one]
    exact (congrArg gam (inv_mul_cancel₀ hq0)).trans (map_one _)))
  obtain ⟨b, hb⟩ := ((isUnit_map_iff (algebraMap V W) _).1 hu).exists_right_inv
  have : q⁻¹ * b = 1 := congrArg Subtype.val hb
  have e : (b : FractionRing R) = q := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hq (e ▸ b.2)

theorem exists_extension : ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z] (AA : LB Z), AA.IsLB → (∀ z : Z, ∃ (d : ℕ) (s : H0 AA d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp (FractionRing R) ⟶ Z) (e : LB.Gen (AA.pull x)), e.IsGen → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∃ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ ∧ ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J) → ∃ χ : Sp R ⟶ Z, jK R ≫ χ = x := by
  intro Z _ _ AA hL amp R _ _ _ _ _ _ x e he H
  by_cases hR : IsField R
  · obtain ⟨d, s, -, hz, hs⟩ := amp (x (cp _))
    refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hz) fun a => ?_
    exact (IsField.localization_map_bijective (M := nonZeroDivisors R) zero_notMem_nonZeroDivisors hR).2 _
  obtain ⟨i, hi⟩ := exists_chart hL (x (cp _))
  have h := top_le x hi
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ z : Z, ∀ (d : ℕ) (s : H0 AA d), ∃ w : W, gam (sv s x h * ((gv e h)⁻¹ ^ d).val) = algebraMap W _ w ∧
        (z ∈ nonzeroLocus s → IsUnit w) := by
    intro W _ _ _ hW φ gam hg
    obtain ⟨χ, hc, e', -, hv⟩ := H W hW φ gam hg
    obtain ⟨i', hi'⟩ := exists_chart hL (χ (cp _))
    exact ⟨χ (cp _), fun d s => ⟨_, quot_eq hL gam (algebraMap W _) hc e he e' hv h (top_le χ hi') s,
      fun hz => ((isUnit_sv s χ _).2 hz).mul (Units.isUnit _)⟩⟩
  have int : ∀ (d : ℕ) (s : H0 AA d), ∃ r : R, algebraMap R _ r = sv s x h * ((gv e h)⁻¹ ^ d).val := fun d s =>
    exists_eq_of_traits _ fun W _ _ _ hW φ gam hg => by
      obtain ⟨z, hz⟩ := key W hW φ gam hg
      exact (hz d s).imp fun _ => And.left
  obtain ⟨W, _, _, _, _, φ, hφ, _⟩ := exists_complete_discreteValuationRing_dominating R hR
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  have hg : ∀ r, IsFractionRing.lift (K := FractionRing R) inj (algebraMap R _ r) = algebraMap W _ (φ r) :=
    fun r => IsFractionRing.lift_algebraMap inj r
  obtain ⟨z, hz⟩ := key W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ _ hg
  obtain ⟨d, s, -, hzs, hs⟩ := amp z
  obtain ⟨w, hw, hu⟩ := hz d s
  obtain ⟨r, hr⟩ := int d s
  rw [← hr, hg] at hw
  have hru : IsUnit r := (isUnit_map_iff φ r).1 (IsFractionRing.injective W _ hw ▸ hu hzs)
  have hx : x (cp _) ∈ nonzeroLocus s :=
    (isUnit_sv s x h).1 (isUnit_of_mul_isUnit_left (hr ▸ hru.map (algebraMap R (FractionRing R))))
  refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hx) fun a => ?_
  obtain ⟨m, t, ht⟩ := exists_sv_eq hL s x h (top_le x hx) a
  obtain ⟨r', hr'⟩ := int _ t
  obtain ⟨u, rfl⟩ := hru
  refine ⟨r' * (u⁻¹ ^ m).val, ?_⟩
  rw [map_mul, hr', ht, pow_mul, Units.val_pow_eq_pow_val _ m, mul_right_comm (_ ^ m), ← mul_pow, ← hr, ← map_pow,
    mul_right_comm, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
    Units.val_one, map_one, _root_.one_mul]

end GlobalTheory.ExtLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtGenPullIff
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.WeightPoint

section Sum
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] {Y Y' : Scheme.{0}}

def IsSum (a b c : Y ⟶ B.left) : Prop :=
  ∃ (s : Y ⟶ S) (a₀ b₀ : Over.mk s ⟶ B), a₀.left = a ∧ b₀.left = b ∧ (a₀ * b₀).left = c

variable {B}

theorem isSum_mul {T : Over S} (a b : T ⟶ B) : IsSum B a.left b.left (a * b).left := ⟨T.hom, a, b, rfl, rfl, rfl⟩

theorem IsSum.unique {a b c c' : Y ⟶ B.left} (h : IsSum B a b c) (h' : IsSum B a b c') : c = c' := by
  obtain ⟨s, a₀, b₀, rfl, rfl, rfl⟩ := h
  obtain ⟨s', a₁, b₁, ha, hb, rfl⟩ := h'
  obtain rfl : s = s' := (Over.w a₀).symm.trans ((congrArg (· ≫ B.hom) ha.symm).trans (Over.w a₁))
  rw [Over.OverMorphism.ext ha, Over.OverMorphism.ext hb]

theorem IsSum.comp {a b c : Y ⟶ B.left} (h : IsSum B a b c) (r : Y' ⟶ Y) {a' b' : Y' ⟶ B.left} (ha : a' = r ≫ a)
    (hb : b' = r ≫ b) : IsSum B a' b' (r ≫ c) := by
  obtain ⟨s, a₀, b₀, rfl, rfl, rfl⟩ := h
  let ρ : Over.mk (r ≫ s) ⟶ Over.mk s := Over.homMk r rfl
  exact ⟨r ≫ s, ρ ≫ a₀, ρ ≫ b₀, ha.symm, hb.symm, congrArg (fun q => q.left) (MonObj.comp_mul ρ a₀ b₀).symm⟩

theorem point_eq_of_lbIso {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L) {S' : Scheme.{0}} {f : S' ⟶ S}
    {b : Y ⟶ B.left} {p : Y ⟶ S'} (pb : IsPullback b p B.hom f) {x y : S' ⟶ B.left} (hx : x ≫ B.hom = f)
    (hy : y ≫ B.hom = f) {τ τ' : Y ⟶ B.left} (hτ : IsSum B (p ≫ x) b τ) (hτ' : IsSum B (p ≫ y) b τ')
    (H : LBIso (LB.LinComb L (K := Fin 2) ![τ, b] ![-1, 1]) (LB.LinComb L (K := Fin 2) ![τ', b] ![-1, 1])) :
    x = y := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ H
  let T : Over S := Over.mk f
  let x₀ : T ⟶ B := Over.homMk x hx
  let y₀ : T ⟶ B := Over.homMk y hy
  let w : T ⊗ B ⟶ B := (fst T B ≫ y₀⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have hp : h ≫ p = (fst T B).left := pb.lift_snd _ _ _
  have key : ∀ (d : T ⟶ B) (σ : Y ⟶ B.left), IsSum B (p ≫ d.left) b σ → h ≫ σ = (translPt B (d * y₀⁻¹)).left :=
    fun d σ hσ => by
      have e : (fst T B ≫ d) * w = translPt B (d * y₀⁻¹) := by
        change _ = (fst T B ≫ (d * y₀⁻¹)) * snd T B
        rw [MonObj.comp_mul, _root_.mul_assoc]
      rw [← e]
      exact (hσ.comp h (by rw [← Category.assoc, hp]; rfl) hb.symm).unique (isSum_mul (fst T B ≫ d) w)
  have k₁ : h ≫ τ' = (snd T B).left := by
    rw [key y₀ τ' hτ', mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x₀ * y₀⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> fin_cases k
    exacts [k₁, hb, key x₀ τ hτ, hb]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x₀ * y₀⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1
    (KerPow.eq_one_of_locGen hK (x₀ * y₀⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩))

end Sum

section Wt
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {X : Type} [AddCommGroup X]

def HasWtGen (i : splitTorus S X ⟶ G) (M : LB G.left) (χ : X) : Prop :=
  ∃ u : LB.Gen M, u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ

variable {i : splitTorus S X ⟶ G} {χ : X}

theorem HasWtGen.chartPull {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F)
    {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i) {M : LB G.left} {M' : LB G'.left} (a : ChartPull M' M F)
    (H : HasWtGen i M χ) : HasWtGen i' M' χ := by
  obtain ⟨t, ht, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU F _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_,
    fun j => (hw _).pull hF hi (a.le j)⟩
  have hm : F y ∈ M.U (a.idx i) ⊓ M.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := (gm_res F y _ hm _).symm.trans ((congrArg (gm F y _) (ht (a.idx i) (a.idx j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res F y _ hm _))))
  exact ((gm_res _ y _ hy _).trans (gm_rp₁ F y _ _ (a.le i) hy.1 _)).trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_rp₁ F y _ _ (a.le j) hy.2 _)))).symm)

theorem HasWtGen.chart {M M' : LB G.left} (a : ChartPull M' M (𝟙 _)) (H : HasWtGen i M χ) : HasWtGen i M' χ :=
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  H.chartPull (isGrpPullback_of_iso (Iso.refl G)) (TorusCompat.refl i) a

theorem hasWtGen_pull_iff {A Y : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {F : G.left ⟶ Y} {ψ : K → (G.left ⟶ A)} (e : ∀ k, ψ k = F ≫ φ k) :
    HasWtGen i ((LB.LinComb L φ ε).pull F) χ ↔ HasWtGen i (LB.LinComb L ψ ε) χ := by
  obtain rfl : ψ = fun k => F ≫ φ k := funext e
  exact ⟨.chart (chartPullIn L φ ε F), .chart (chartPullOut L φ ε F _ fun _ => rfl)⟩

theorem HasWtGen.inv {A : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {φ : K → (G.left ⟶ A)} {ε ε' : K → ℤ}
    (e : ∀ k, ε' k = -ε k) (H : HasWtGen i (LB.LinComb L φ ε) (-χ)) : HasWtGen i (LB.LinComb L φ ε') χ := by
  obtain rfl : ε' = fun k => -ε k := funext e
  obtain ⟨t, ht, hw⟩ := H
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun j => neg_neg χ ▸ (hw j).inv⟩

theorem HasWtGen.of_lbIso {Y : Scheme.{0}} {F : G.left ⟶ Y}
    (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
    {N N' : LB Y} (hN : N.IsLB) (hN' : N'.IsLB) (H : LBIso N N') (h : HasWtGen i (N.pull F) χ) :
    HasWtGen i (N'.pull F) χ := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullId N) (Geo.Tor.chartPullPull N' (𝟙 Y) (𝟙 Y) rfl)
  obtain ⟨a, ha, hχ⟩ := h
  obtain ⟨u, hu, hv⟩ := exists_up ((isGen_iff w).1 hw) hN' hN a ha
  rw [← Category.comp_id F]
  refine ⟨u, hu, fun p => isWt_of_gm _ _ fun Z t g z m₂ => ?_⟩
  obtain ⟨q, hq⟩ := exists_chart hN (F (g.left z))
  have e : F (((t ≫ i) * g).left z) = F (g.left z) := congrArg (fun q => q z) (hF Z t g)
  have n₂ : g.left z ∈ (N.pull F).U fun _ => q := mem_pull.2 hq
  have n₁ : ((t ≫ i) * g).left z ∈ (N.pull F).U fun _ => q := mem_pull.2 (e ▸ hq)
  have m₁ : ((t ≫ i) * g).left z ∈ (N'.pull (F ≫ 𝟙 Y)).U p := by
    have : F (g.left z) ∈ N'.U (p PUnit.unit) := mem_pull.1 m₂
    exact mem_pull.2 (show F _ ∈ N'.U (p PUnit.unit) from e ▸ this)
  refine (hv _ _ z p _ m₁ n₁).trans (Eq.trans ?_ (congrArg _ (hv _ _ z p _ m₂ n₂).symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (gm_eq_of_isWt (hχ _) t g z n₁ n₂)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw
  simp only [hF]

end Wt

section Rep
variable {S S' S'' : Scheme.{0}} {B : Over S} [GrpObj B] {G : Over S'} [GrpObj G] {G' : Over S''} [GrpObj G']
  {X : Type} [AddCommGroup X]

def Rep (Q : TQ G X) (L : LB B.left) (b : Q.B.left ⟶ B.left) (x : S' ⟶ B.left) (χ : X) : Prop :=
  ∃ τ, IsSum B (Q.B.hom ≫ x) b τ ∧
    HasWtGen Q.i ((LB.LinComb L (K := Fin 2) ![τ, b] ![-1, 1]).pull Q.q.left) χ

variable {Q : TQ G X} {L : LB B.left} {b : Q.B.left ⟶ B.left} {χ : X}

theorem Rep.unique (hL : L.IsLB) (hK : KTriv B L) {f : S' ⟶ S} (pb : IsPullback b Q.B.hom B.hom f)
    {x y : S' ⟶ B.left} (hx : x ≫ B.hom = f) (hy : y ≫ B.hom = f) (h : Rep Q L b x χ) (h' : Rep Q L b y χ) :
    x = y := by
  obtain ⟨τ, hτ, u, hu⟩ := h
  obtain ⟨τ', hτ', u', hu'⟩ := h'
  exact point_eq_of_lbIso hL hK pb hx hy hτ hτ' (lbIso_of_genWt _ _ _ Q _ _ u u' χ (DVR.linComb_isLB _ hL _ _)
    (DVR.linComb_isLB _ hL _ _) hu hu')

theorem Rep.pull {Q' : TQ G' X} {g : S'' ⟶ S'} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G g F)
    (hi : TorusCompat g F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left} (hβ : β ≫ Q.B.hom = Q'.B.hom ≫ g)
    (hq : Q'.q.left ≫ β = F ≫ Q.q.left) {b' : Q'.B.left ⟶ B.left} (hb : β ≫ b = b') {x : S' ⟶ B.left}
    (h : Rep Q L b x χ) : Rep Q' L b' (g ≫ x) χ := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨β ≫ τ, hτ.comp β (by rw [← Category.assoc, ← hβ, Category.assoc]) hb.symm,
    (hasWtGen_pull_iff fun _ => rfl).2 (((hasWtGen_pull_iff fun _ => rfl).1 h).chartPull hF hi
      (chartPullSame L _ _ _ F fun k => ?_))⟩
  fin_cases k
  · show Q'.q.left ≫ β ≫ τ = F ≫ Q.q.left ≫ τ
    rw [reassoc_of% hq]
  · show Q'.q.left ≫ b' = F ≫ Q.q.left ≫ b
    rw [← hb, reassoc_of% hq]

theorem Rep.section {f : S' ⟶ S} (w : b ≫ B.hom = Q.B.hom ≫ f) (c : 𝟙_ _ ⟶ B) (h : Rep Q L b (f ≫ c.left) χ) :
    HasWtGen Q.i ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)) χ := by
  obtain ⟨τ, hτ, h⟩ := h
  have e : τ = b ≫ ((toUnit B ≫ c) * 𝟙 B).left := hτ.unique ((isSum_mul (toUnit B ≫ c) (𝟙 B)).comp b (by
    rw [Over.comp_left, Rosenlicht.toUnit_left, ← Category.assoc, ← w, Category.assoc]) (Category.comp_id b).symm)
  refine (hasWtGen_pull_iff (ψ := fun k => Q.q.left ≫ ![τ, b] k) fun k => ?_).2
    ((hasWtGen_pull_iff fun _ => rfl).1 h)
  fin_cases k
  · exact (congrArg (Q.q.left ≫ ·) e).trans (Category.assoc _ _ _).symm
  · exact (Category.comp_id _).symm

end Rep

theorem exists_rep (hP : PicardZeroDegenerationCondition) {R A : Type} [CommRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {B : Over (Spec (CommRingCat.of R))} [GrpObj B] [IsCommMonObj B] (M : CP B) (hA : RelAmple B M.L.L)
    (hK : KTriv B M.L.L) {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    (Q : TQ G X) {f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)} {b : Q.B.left ⟶ B.left}
    (pb : IsGrpPullback Q.B B f b) (χ : X) : ∃ x, x ≫ B.hom = f ∧ Rep Q M.L.L b x χ := by
  have hL := M.L.isLB
  have hL' := pull_isLB hL b
  have hw := (isGen_iff _).1 (pullIso_isGen hL b)
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim A Q.B Q.isAb
  have hs : Sym B M.L.L := fun _ => ⟨⊤, trivial, by
    obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![(B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left, (B.hom ⁻¹ᵁ ⊤).ι])
      (ε' := ![1, -1]) hL (fun U _ h => Finset.prod_congr rfl fun k _ => by
        fin_cases k
        exacts [rfl, congrArg (fun q => h q ^ (-1 : ℤ)) (Category.comp_id _)])
      _ (DVR.pullGen_isGen _ _ _ _ M.sym_gen (B.hom ⁻¹ᵁ ⊤).ι)
    exact ⟨u, hu⟩⟩
  let P : PolAV (Spec (CommRingCat.of A)) := ⟨Q.B, Q.isAb, g, hg, M.L.L.pull b, hL',
    PolBaseChange.rigidified_pull pb ⟨M.L.rig, M.L.rigGen⟩, PolBaseChange.sym_pull pb hs,
    relAmple_pull pb.1 hL hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hA, kTriv_pull pb hL hL' hw hK⟩
  obtain ⟨N, t, hN, ht, hΛ⟩ := WtBundle.exists_genWt Q (-χ)
  obtain ⟨x, hx⟩ := hP A P N hN hΛ
  replace hx : LBIso N (LB.LinComb (M.L.L.pull b) (K := Fin 2) ![((toUnit Q.B ≫ x) * 𝟙 Q.B).left, 𝟙 Q.B.left]
    ![1, -1]) := hx
  have H := hx.trans hN (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (iso_linComb hw _ _)
  have H₁ := HasWtGen.of_lbIso (i := Q.i) (fun Z x g => by
    rw [← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]) hN (DVR.linComb_isLB _ hL _ _) H ⟨t, ht⟩
  refine ⟨x.left ≫ b, ?_, ((toUnit Q.B ≫ x) * 𝟙 Q.B).left ≫ b, ?_, (hasWtGen_pull_iff fun _ => rfl).2
    (HasWtGen.inv (ε := ![1, -1]) (fun k => by fin_cases k <;> rfl) ((hasWtGen_pull_iff fun k => ?_).1 H₁))⟩
  · rw [Category.assoc, pb.1.w, ← Category.assoc, Over.w x]
    exact Category.id_comp _
  · refine ⟨_, pushPt pb.1.w (toUnit Q.B ≫ x), pushPt pb.1.w (𝟙 Q.B), ?_, Category.id_comp b,
      pb.2 _ _ _ _ _ rfl rfl⟩
    show (toUnit Q.B ≫ x).left ≫ b = _
    rw [Over.comp_left, Rosenlicht.toUnit_left, Category.assoc]
  · fin_cases k
    exacts [rfl, congrArg (Q.q.left ≫ ·) (Category.id_comp b).symm]

end GlobalTheory.WeightPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedProjectiveCharts_split_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  first | exact @GlobalTheory.ZJ.GenericSplit.split_generic | exact GlobalTheory.ZJ.GenericSplit.split_generic | (intros; apply GlobalTheory.ZJ.GenericSplit.split_generic <;> assumption)
end

