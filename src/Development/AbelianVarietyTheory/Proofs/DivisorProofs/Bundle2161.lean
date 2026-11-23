module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelSectionOfIdealTorsionAtGeometricPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section
open CartesianMonoidalCategory MonObj

namespace GlobalTheory.TorsSpec

theorem exists_etaSecL_of_torsI : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ I hI Ω _ _ x P hP hT
  have cart := TF.Y.m.cart
  have hpb := GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ
  have hQw : (P ≫ GlobalTheory.EqvAct.pullψ TF Z φ) ≫ TF.Y.t.G.hom = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.jQ ≫ pullback.fst _ _) := by
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hP, Category.assoc, reassoc_of% hℓ, Category.assoc, j₀_ι]
    rfl
  let Q := cart.1.lift _ _ hQw
  have hQφ : Q ≫ TF.Y.m.φ = P ≫ GlobalTheory.EqvAct.pullψ TF Z φ := cart.1.lift_fst _ _ hQw
  have hQh : Q ≫ TF.Y.oF.t.G.hom = x ≫ i₀ TF.Y Z := cart.1.lift_snd _ _ hQw
  let Q' : Over.mk (x ≫ i₀ TF.Y Z) ⟶ TF.Y.oF.t.G := Over.homMk Q hQh
  have htu : ∀ {S : Scheme.{0}} (T : Over S), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have hcartη := eta_comp_of_isGrpPullback cart
  have hpbη := eta_comp_of_isGrpPullback hpb
  have htors : ∀ a ∈ I, Q' ≫ TF.Y.oF.t.act.act a = 1 := by
    intro a ha
    apply Over.OverMorphism.ext
    rw [Hom.one_def, Over.comp_left, Over.comp_left, htu]
    show Q ≫ _ = (x ≫ i₀ TF.Y Z) ≫ _
    apply cart.1.hom_ext
    · rw [Category.assoc, TF.Y.m.act, reassoc_of% hQφ, ← GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% (hT a ha),
        hpbη, Category.assoc, Category.assoc, hcartη, reassoc_of% hP]
      simp only [Category.assoc]
      rw [reassoc_of% hℓ, reassoc_of% j₀_ι]
      rfl
    · rw [Category.assoc, Over.w, hQh, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  let s0 : Xo.XF c ⟶ Sp (KA l) := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
  let β : KA l →+* Ω := (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ s0)).hom
  have hβ : (x ≫ i₀ TF.Y Z) ≫ s0 = spMap β :=
    ((congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage _)).symm
  have hg := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z) β hβ
  obtain ⟨TI, -, -, hη⟩ := hg.2
  have hMI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    apply hI
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hpow : Q' ^ l.M = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN, ← act_natCast (E := E) TF.Y.oF.t.act, htors _ hMI]
  obtain ⟨a, ha⟩ := (TI.onto l.M hM0 Q').1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hev : Q' = TI.ev l.M (v • a) := by
    have e1 : TI.ev l.M (u • a) = 1 := by
      rw [TI.lin, ha]
      exact htors u (hI hu)
    have e2 := TI.add l.M (u • a) (v • a)
    rw [← add_smul, huv, one_smul, ha, e1, _root_.one_mul] at e2
    exact e2
  have hvm : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hQeta : Q = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta (v • a)).left := by
    have := congrArg (fun q => q.left) (hev.trans (hη _ hvm).symm)
    simp only [Q', Over.homMk_left, Over.comp_left, htu] at this
    exact this
  refine ⟨Submodule.Quotient.mk (v • a), hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, etaSecL_ψ, ← hQφ, hQeta]
    simp only [Category.assoc]
  · rw [hP, Category.assoc, etaSecL_w]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSystemDefectCocycleGlobalForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Defect

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S S' : Sys I π s₀} (Φ : S.LocIso S')

abbrev al {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)

abbrev be {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)

theorem map_mem {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (f : B →ₐ[R] B')
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : f x ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (f : B →+* B') hx
  rwa [Ideal.map_map, f.comp_algebraMap] at h

theorem mul_eq_zero' (hI : I ^ 2 = 0) {B : Type} [CommRing B] [Algebra R B] {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B] at h
  simpa using h

theorem diff_mem {U V : AffOp X₀} (a : U ⟶ V) (b : S.F.obj U) :
    al Φ a b - be Φ a b ∈ I.map (algebraMap R (S'.F.obj V)) := by
  rw [← S'.ker V, map_sub, sub_eq_zero]
  change S'.p V (mp S'.F a (Φ.φ U b)) = S'.p V (Φ.φ V (mp S.F a b))
  rw [S'.nat, Φ.red, Φ.red, S.nat]

theorem ex (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) :
    ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V, IsTheta I (S.p U) (al Φ a) (be Φ a) θ :=
  (_root_.GlobalTheory.LiftSys.theta_classify R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U)
    (S.surj U) (S.ker U) (al Φ a)).1 (be Φ a) (diff_mem Φ a)

def th (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V :=
  (ex Φ hI hπ a).exists.choose

theorem th_spec (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : IsTheta I (S.p U) (al Φ a) (be Φ a) (th Φ hI hπ a) :=
  (ex Φ hI hπ a).exists.choose_spec

theorem th_comp (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V W : AffOp X₀} (a : U ⟶ V)
    (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]) :
    th Φ hI hπ (a ≫ b) x = mp S'.F b (th Φ hI hπ a x) + th Φ hI hπ b (p1 (OAff s₀) a x) := by
  let θ' : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj W :=
    ((mp S'.F b).toRingHom.toAddMonoidHom.comp (th Φ hI hπ a)) +
      (th Φ hI hπ b).comp (p1 (OAff s₀) a).toAddMonoidHom
  have hA := th_spec Φ hI hπ a
  have hB := th_spec Φ hI hπ b
  have h : IsTheta I (S.p U) (al Φ (a ≫ b)) (be Φ (a ≫ b)) θ' := by
    refine ⟨fun c w ↦ ?_, fun c ↦ ?_, fun w ↦ ?_⟩
    · change mp S'.F b (th Φ hI hπ a (S.p U c • w)) + th Φ hI hπ b (p1 (OAff s₀) a (S.p U c • w)) =
        al Φ (a ≫ b) c * (mp S'.F b (th Φ hI hπ a w) + th Φ hI hπ b (p1 (OAff s₀) a w))
      rw [hA.smul, oneFormsMapOfFunctorMorphism_smul]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.smul, map_mul]
      have hz : (mp S'.F b (al Φ a c) - al Φ b (mp S.F a c)) * th Φ hI hπ b (p1 (OAff s₀) a w) = 0 := by
        refine mul_eq_zero' hI ?_ (hB.mem _)
        have : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
        rw [this, ← map_sub]
        exact map_mem _ (diff_mem Φ a c)
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      rw [e2]
      linear_combination -hz
    · change mp S'.F b (th Φ hI hπ a (D R₀ _ (S.p U c))) + th Φ hI hπ b (p1 (OAff s₀) a (D R₀ _ (S.p U c))) =
        al Φ (a ≫ b) c - be Φ (a ≫ b) c
      rw [hA.der, p1_D]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.der, map_sub]
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      have e3 : be Φ (a ≫ b) c = be Φ b (mp S.F a c) := by
        change Φ.φ W (mp S.F (a ≫ b) c) = Φ.φ W (mp S.F b (mp S.F a c)); rw [mp_comp]
      have e4 : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
      rw [e2, e3, e4]; ring
    · exact Ideal.add_mem _ (map_mem _ (hA.mem w)) (hB.mem _)
  have := (ex Φ hI hπ (a ≫ b)).unique (th_spec Φ hI hπ (a ≫ b)) h
  exact DFunLike.congr_fun this x

def cocyc (hI : I ^ 2 = 0) (hπ : Function.Surjective π) : GlobForm s₀ →+ Z1 S'.F where
  toFun w := ⟨fun U V a ↦ th Φ hI hπ a (w.1 U), fun U V W a b ↦ by
    change th Φ hI hπ (a ≫ b) (w.1 U) = mp S'.F b (th Φ hI hπ a (w.1 U)) + th Φ hI hπ b (w.1 V)
    rw [th_comp, w.2 a]⟩
  map_zero' := Subtype.ext (by funext U V a; exact map_zero _)
  map_add' w w' := Subtype.ext (by funext U V a; exact map_add _ _ _)

theorem th_smul (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) (r : R)
    (x : Ω[Sec s₀ U.unop.1⁄R₀]) : th Φ hI hπ a (π r • x) = r • th Φ hI hπ a x := by
  rw [← algebraMap_smul (Sec s₀ U.unop.1) (π r) x, ← (S.semi U).map_algebraMap, (th_spec Φ hI hπ a).smul,
    AlgHom.commutes, ← Algebra.smul_def]

end GlobalTheory.LiftSys.Defect

theorem GlobalTheory.LiftSys.exists_defect_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  intro R R₀ _ _ I hI π hπ _ X₀ s₀ S S' Φ
  refine ⟨fun U V a ↦ Defect.th Φ hI hπ a, Defect.cocyc Φ hI hπ, fun U V a ↦ Defect.th_spec Φ hI hπ a,
    fun w U V a ↦ rfl, fun w U V a ↦ (Defect.th_spec Φ hI hπ a).mem _, fun r w ↦ ?_⟩
  refine Subtype.ext ?_
  funext U V a
  exact Defect.th_smul Φ hI hπ a r (w.1 U)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformation
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem cechPt_over (P : GPt A) : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
  (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w

@[reducible] def Pt.cst (P : GPt A) : GPt A where
  B := DualNumber P.B
  x := spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x
  w := (congrArg (_ ≫ ·) (Category.comp_id A.hom)).trans (by
    rw [Category.assoc, cechPt_over, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

theorem Pt.In.cst {P : GPt A} {U : A.left.Opens} (h : P.In U) : P.cst.In U :=
  fun _ _ ↦ h (Set.mem_univ _)

theorem cst_base (P : GPt A) :
    (dualMap (algebraMap K P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber P.B) := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_dualMap (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K (DualNumber P.B)) = algebraMap K P.B := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_inl (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem cst_red (P : GPt A) :
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x = P.x := by
  show _ ≫ spMap _ ≫ P.x = P.x
  rw [← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]

theorem cst_val (P : GPt A) {U : A.left.Opens} (hU : P.In U) (g : Γ(A.left, U)) :
    TrivSqZeroExt.fst (valR P.cst.x U g) = valR P.x U g := by
  show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hU]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem cst_trx_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : P.In U)
    (g : Γ(A.left, U)) : TrivSqZeroExt.fst (valR (P.cst.trx v) U g).snd = (valR (P.trx v) U g).snd := by
  have hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U := hU.cst.tr hv
  have hm := (P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  have e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B :=
    fst_comp_dualMap P
  rw [e1, cst_red] at hm
  rw [← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]
  simp [dualMap]

theorem eps_eq (P : GPt A) :
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps = TrivSqZeroExt.inr 1 := by
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, RingHom.algebraMap_toAlgebra]

theorem cechKS_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  intro K _ A _ A' _ i L n u θ hu h
  obtain ⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩ := h
  have hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
      P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) :=
    fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)
  refine ⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x,
    hcov, hWc, ?_, ?_, ?_⟩
  · intro k P hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    obtain ⟨h1, h2, -⟩ := hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst
    refine ⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩
    let I := Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}
    have hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0 := by
      intro a ha
      change a ∈ Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps} at ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [eps_eq P]
      simp
    change spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x =
      spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i at h2
    have hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) =
        (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) := RingHom.ext fun _ ↦ rfl
    calc spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ _
        = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x := by
          rw [← Category.assoc, ← Cris.spMap_comp, hq]
          rfl
      _ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]
      _ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]
      _ = P.x ≫ i := by rw [cst_red]
  · intro k P Q φ hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra
    let ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B :=
      { dualMap (φ.ρ : P.B →+* Q.B) with
        commutes' := fun r ↦ by
          ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }
    have h3 := (hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ
    have hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x := by
      show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
      rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
    exact h3.trans (congrArg _ hc)
  · intro k k' P U f hk hk' hU
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    have ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)))
        P.cst.x (u a) (P.cst.trx (u a)) := fun a ↦ by
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      exact P.cst.isTransl_trx (u a)
    have hd := hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst)
      hU.cst ht
    refine hd.trans ?_
    have hg : P.In (L.U (c k) ⊓ L.U (c k')) := (hk.mono (hWc k)).inf (hk'.mono (hWc k'))
    have e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd =
        (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd := fun a ↦ cst_trx_val P (hu a) hg _
    have e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd =
        (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd := fun a ↦ cst_trx_val P (hu a) hU _
    have e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val :=
      cst_val P hg _
    have e4 : ∀ r : K, TrivSqZeroExt.fst
        (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r := by
      intro r
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [eps_eq P]
    have hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst := fun S ↦ by
      ext <;> simp
    rw [hS]
    congr 1
    change (TrivSqZeroExt.fstHom K P.B P.B) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]
    simp only [e1, e2, e3, e4, dlog, Finset.sum_mul]

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitGeneratorOfLineBundleLocalSection
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

theorem gm_id_val_germ {X : Scheme.{0}} (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)ˣ) :
    (gm (𝟙 X) x U a).val = (X.presheaf.germ U x h).hom a.val := by
  rw [gm_val (𝟙 X) x U h]
  rfl

theorem isUnit_res_basicOpen' {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) :=
  X.toRingedSpace.isUnit_res_basicOpen e

def basicUnit {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) : Γ(X, X.basicOpen e)ˣ :=
  (isUnit_res_basicOpen' e).unit

theorem gm_basicUnit_val {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) (x : X) (hx : x ∈ X.basicOpen e) :
    (gm (𝟙 X) x _ (basicUnit e)).val = (X.presheaf.germ D x (X.basicOpen_le e hx)).hom e := by
  rw [gm_id_val_germ x _ hx]
  show (X.presheaf.germ (X.basicOpen e) x hx).hom ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) = _
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx e

theorem exists_locGen_of_secFam : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL J D k hD e he
  let B : J → X.Opens := fun j => X.basicOpen (e j)
  have hB : ∀ j, B j ≤ D j := fun j => X.basicOpen_le (e j)
  let V : X.Opens := ⨆ j, B j
  have hBV : ∀ j, B j ≤ V := fun j => le_iSup B j

  have ge : ∀ j j' (z : X) (hz : z ∈ B j) (hz' : z ∈ B j'),
      gm (𝟙 X) z (B j) (basicUnit (e j)) =
        gm (𝟙 X) z (L.U (k j) ⊓ L.U (k j')) (L.g (k j) (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro j j' z hz hz'
    apply Units.ext
    rw [Units.val_mul, gm_basicUnit_val _ z hz, gm_basicUnit_val _ z hz',
      gm_id_val_germ z (L.U (k j) ⊓ L.U (k j')) ⟨hD j (hB j hz), hD j' (hB j' hz')⟩]
    exact he j j' z (hB j hz) (hB j' hz')
  let W : L.ι → J → X.Opens := fun i j => B j ⊓ L.U i
  have hWV : ∀ i j, W i j ≤ V ⊓ L.U i := fun i j => inf_le_inf_right _ (hBV j)
  have hWg : ∀ i j, W i j ≤ L.U i ⊓ L.U (k j) := fun i j z hz => ⟨hz.2, hD j (hB j hz.1)⟩
  have hWB : ∀ i j, W i j ≤ B j := fun i j => inf_le_left
  let u : ∀ i j, Γ(X, W i j)ˣ := fun i j => res (hWg i j) (L.g i (k j)) * res (hWB i j) (basicUnit (e j))
  have gu : ∀ i j (z : X) (hz : z ∈ W i j), gm (𝟙 X) z (W i j) (u i j) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) := by
    intro i j z hz
    simp only [u, map_mul]
    rw [gm_res _ z (hWg i j) hz, gm_res _ z (hWB i j) hz]
  have key : ∀ i j j' (z : X), z ∈ L.U i → z ∈ B j → z ∈ B j' →
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j')) (L.g i (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro i j j' z hi hj hj'
    rw [ge j j' z hj hj', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) z hi (hD j (hB j hj)) (hD j' (hB j' hj'))]
  have glued : ∀ i, ∃ s : Γ(X, V ⊓ L.U i)ˣ, ∀ j, res (hWV i j) s = u i j := by
    intro i
    refine glue_unit (V ⊓ L.U i) (W i) (hWV i) (fun z hz => ?_) (u i) (fun j j' z hz => ?_)
    · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hz.2⟩
    · rw [gu i j z hz.1, gu i j' z hz.2]
      exact key i j j' z hz.1.2 hz.1.1 hz.2.1
  choose a ha using glued
  refine ⟨V, a, fun j x hx hu => hBV j ((Scheme.mem_basicOpen X (e j) x hx).2 hu), ?_⟩
  intro y i i' hy hi hi'
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have ga : ∀ i (hi : y ∈ L.U i), gm (𝟙 X) y (V ⊓ L.U i) (a i) =
      gm (𝟙 X) y (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) y (B j) (basicUnit (e j)) := by
    intro i hi
    rw [← gm_res _ y (hWV i j) ⟨hj, hi⟩, ha i j]
    exact gu i j y ⟨hj, hi⟩
  rw [ga i hi, ga i' hi', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) y hi hi' (hD j (hB j hj))]

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_value_one_origin_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.PolDeg.NormIso.exists_normalised_iso | exact GlobalTheory.PolDeg.NormIso.exists_normalised_iso | (intros; apply GlobalTheory.PolDeg.NormIso.exists_normalised_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_dominating_local_domain_complex : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  first | exact @GlobalTheory.DvrDom.exists_place_dominating | exact GlobalTheory.DvrDom.exists_place_dominating | (intros; apply GlobalTheory.DvrDom.exists_place_dominating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end

