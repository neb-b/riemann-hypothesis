module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | exact GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | (intros; apply GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGeneratorCharTrivial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := _root_.GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (_root_.GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction
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

namespace GlobalTheory.TorsSpec

theorem exists_torsion_map_of_isGrpPullback {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {f : X' ⟶ X'}
    {φ : G.left ⟶ G.left} (h : IsGrpPullback G G f φ) (hc : (mulN G n).left ≫ φ = φ ≫ (mulN G n).left) :
    ∃ τ : (torsion G n).left ⟶ (torsion G n).left,
      τ ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ φ ∧ τ ≫ (torsion G n).hom = (torsion G n).hom ≫ f := by
  have hP := GrpTangent.isPullback_torsion G n
  have hw : ((torsion.ι G n).left ≫ φ) ≫ (mulN G n).left =
      ((torsion G n).hom ≫ f) ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have e := eta_comp_of_isGrpPullback h
    rw [Category.assoc, ← hc, ← Category.assoc, hP.w]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((torsion G n).hom ≫ ·) e).trans (Category.assoc _ _ _).symm)
  exact ⟨hP.lift _ _ hw, hP.lift_fst _ _ hw, hP.lift_snd _ _ hw⟩

theorem class_move : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).asIso.hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act Γ _ ρ' ρ hρ ι m hm hmv K _ _ t γ P Q PT QT hPT hQT hPQ
    x cP cQ hcP hcQ
  haveI := mono_torsion_ι G n
  have hpb := hm.1 γ
  obtain ⟨τ, hτι, hτh⟩ := exists_torsion_map_of_isGrpPullback G n hpb
    (by rw [← act_natCast act n]; exact hm.2.1 γ _)
  have hPQT : PT ≫ τ = QT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτι, reassoc_of% hPT, hQT, hPQ]
  have hq : τ (PT x) = QT x := by rw [← hPQT, Scheme.Hom.comp_apply]
  have hιh : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  have hval : ValAt G n ℓ w (PT x) ((ι γ).symm cQ) := by
    intro Ω _ _ y z hyz
    rw [← hq] at hcQ
    have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ (x := PT x)
    have h1 := hcQ Ω (y ≫ Spec.map (τ.stalkMap (PT x))) (z ≫ (ρ γ).asIso.hom) (by
      simp only [Category.assoc, reassoc_of% key, hτh, hρ, reassoc_of% hyz])
    simp only [Category.assoc, reassoc_of% key, hτι] at h1
    refine hpb.1.hom_ext ?_ ?_
    · simp only [Category.assoc, hmv, LinearEquiv.apply_symm_apply]
      exact h1
    · simp only [Category.assoc, hw, hιh]
      exact hyz
  rw [valAt_unique G n hn ℓ w hw hun (PT x) cP _ hcP hval, LinearEquiv.apply_symm_apply]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAdd
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

open CartesianMonoidalCategory MonObj
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_comp_stalk {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) {W : Scheme.{0}} (f : W ⟶ (torsion G n).left) (q : W) (c : M)
    (h : ValAt G n ℓ w (f q) c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (z : Sp Ω ⟶ V)
    (hz : y ≫ W.fromSpecStalk q ≫ f ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ W.fromSpecStalk q ≫ f ≫ (torsion.ι G n).left = z ≫ w c := by
  have e := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
  have h1 := h Ω (y ≫ Spec.map (f.stalkMap q)) z (by rw [Category.assoc, reassoc_of% e]; exact hz)
  rwa [Category.assoc, reassoc_of% e] at h1

theorem comp_torsion_ι_mulN {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ torsion G n) :
    (a ≫ torsion.ι G n) ≫ mulN G n = 1 := by
  have e : torsion.ι G n ≫ mulN G n = toUnit (torsion G n) ≫ (η : 𝟙_ (Over X') ⟶ G) :=
    (pullback.condition (f := mulN G n) (g := (η : 𝟙_ (Over X') ⟶ G))).trans
      (congrArg (· ≫ (η : 𝟙_ (Over X') ⟶ G)) (toUnit_unique _ _))
  rw [Category.assoc, e, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem valAt_mul : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ hun hadd K _ _ t P Q PT QT RT hPT hQT hRT x cP cQ cR hcP hcQ hcR
  haveI : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  let h : pullback (torsion G n).hom (torsion G n).hom ⟶ X' :=
    pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  haveI : Etale h := inferInstance
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  haveI : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x)) :=
    isDomain_stalk_of_etale h (pq x)
  obtain ⟨Ω, _, _, y, hy, -⟩ := _root_.GlobalTheory.exists_geomGeneric_dominant ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x))
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.lift_of_stalk_generic_flat h (pq x) ℓ Ω y hy
  let WO : Over X' := Over.mk h
  let A' : WO ⟶ torsion G n := Over.homMk (pullback.fst (torsion G n).hom (torsion G n).hom) rfl
  let B' : WO ⟶ torsion G n :=
    Over.homMk (pullback.snd (torsion G n).hom (torsion G n).hom) pullback.condition.symm
  let A : WO ⟶ G := A' ≫ torsion.ι G n
  let B : WO ⟶ G := B' ≫ torsion.ι G n
  have hs : (A * B) ≫ mulN G n = 1 := by
    letI : CommGroup (WO ⟶ G) := Hom.commGroup
    rw [GlobalTheory.GrpTangent.comp_mulN, mul_pow, ← GlobalTheory.GrpTangent.comp_mulN, ← GlobalTheory.GrpTangent.comp_mulN,
      comp_torsion_ι_mulN, comp_torsion_ι_mulN, _root_.one_mul]
  obtain ⟨sT, hsT⟩ := exists_lift_torsion n (A * B) hs
  let g : Over.mk t ⟶ WO := Over.homMk pq (by
    show pq ≫ pullback.fst _ _ ≫ _ = t
    rw [pullback.lift_fst_assoc, hPt])
  have hgA : g ≫ A = P := by
    ext1
    simp only [A, A', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_fst_assoc, hPT]
  have hgB : g ≫ B = Q := by
    ext1
    simp only [B, B', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_snd_assoc, hQT]
  have hRT' : pq ≫ sT.left = RT := by
    haveI := mono_torsion_ι G n
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, ← Over.comp_left, hsT, hRT, ← hgA, ← hgB,
      ← MonObj.comp_mul]
    rfl
  have e1 : (pullback.fst (torsion G n).hom (torsion G n).hom) (pq x) = PT x := by
    show (pq ≫ pullback.fst _ _) x = _
    rw [pullback.lift_fst]
  have e2 : (pullback.snd (torsion G n).hom (torsion G n).hom) (pq x) = QT x := by
    show (pq ≫ pullback.snd _ _) x = _
    rw [pullback.lift_snd]
  have e3 : sT.left (pq x) = RT x := by
    show (pq ≫ sT.left) x = _
    rw [hRT']
  rw [← e1] at hcP
  rw [← e2] at hcQ
  rw [← e3] at hcR
  have hP' := valAt_comp_stalk G n ℓ w _ (pq x) cP hcP Ω y z hz
  have hQ' := valAt_comp_stalk G n ℓ w _ (pq x) cQ hcQ Ω y z (by rw [← pullback.condition]; exact hz)
  have hR' := valAt_comp_stalk G n ℓ w sT.left (pq x) cR hcR Ω y z (by rw [Over.w sT]; exact hz)
  let k : Over.mk (z ≫ ℓ) ⟶ WO :=
    Over.homMk (y ≫ (pullback (torsion G n).hom (torsion G n).hom).fromSpecStalk (pq x))
      (by simpa [WO] using hz)
  have hC := hadd Ω z cP cQ (k ≫ A) (k ≫ B) (Over.homMk (z ≫ w (cP + cQ)) (by simp [hw]))
    (by simpa [k, A, A'] using hP') (by simpa [k, B, B'] using hQ') rfl
  rw [← MonObj.comp_mul, ← hsT] at hC
  have hC' := congrArg (fun u => u.left) hC
  simp only [Over.homMk_left, Over.comp_left, k] at hC'
  refine hun Ω z cR (cP + cQ) ?_
  rw [← hR']
  simp only [Category.assoc] at hC'
  exact hC'.symm

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  first | exact @GlobalTheory.PtTrans.ptTrans | exact GlobalTheory.PtTrans.ptTrans | (intros; apply GlobalTheory.PtTrans.ptTrans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingClosedAllFibres
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.CovTop GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibreImm

set_option backward.isDefEq.respectTransparency.types false

theorem isPullback_pullback_map {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsPullback ((Over.pullback a).map v).left (pullback.fst X.hom a) (pullback.fst Y.hom a) v.left := by
  have h1 : ((Over.pullback a).map v).left ≫ pullback.fst Y.hom a = pullback.fst X.hom a ≫ v.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback a).map v).left ≫ pullback.snd Y.hom a = pullback.snd X.hom a :=
    Over.w ((Over.pullback a).map v)
  refine IsPullback.of_right ?_ h1 (IsPullback.of_hasPullback Y.hom a).flip
  have h := (IsPullback.of_hasPullback X.hom a).flip
  rw [h2, Over.w v]
  exact h

theorem closedImm_comp_iff {S S' S'' : Scheme.{0}} (b : S'' ⟶ S') (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsClosedImmersion ((Over.pullback (b ≫ a)).map v).left ↔
      IsClosedImmersion ((Over.pullback b).map ((Over.pullback a).map v)).left := by
  let e := Over.pullbackComp b a
  exact MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk ((Over.forget _).mapIso (e.app X)) ((Over.forget _).mapIso (e.app Y))
      (congrArg (·.left) (e.hom.naturality v).symm))

theorem closedImm_pullback {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y)
    (h : IsClosedImmersion v.left) : IsClosedImmersion ((Over.pullback a).map v).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_pullback_map a v).flip h

theorem closedImm_of_pullback {k Ω : CommRingCat.{0}} (hk : IsField k) (hΩ : IsField Ω) (φ : k ⟶ Ω)
    {X Y : Over (Spec k)} (v : X ⟶ Y)
    (h : IsClosedImmersion ((Over.pullback (Spec.map φ)).map v).left) : IsClosedImmersion v.left := by
  letI := hk.toField
  letI := hΩ.toField
  letI := φ.hom.toAlgebra
  have hd := GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_descendsAlong_fpqc
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map φ) :=
    GlobalTheory.ClosedImmFieldDescent.fpqc_specMap_field k Ω
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_pullback_map _ v)
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback Y.hom (Spec.map φ)).flip hq) h

theorem closedImm_iff_residue {W : Scheme.{0}} {X Y : Over W} (v : X ⟶ Y) (k : Type) [Field k] (w : Sp k ⟶ W) :
    IsClosedImmersion ((Over.pullback w).map v).left ↔
      IsClosedImmersion ((Over.pullback (W.fromSpecResidueField (w (IsLocalRing.closedPoint k)))).map v).left := by
  conv_lhs => rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k W w]
  rw [closedImm_comp_iff]
  exact ⟨closedImm_of_pullback (Field.toIsField _) (Field.toIsField _) _ _, closedImm_pullback _ _⟩

end GlobalTheory.TorusFibreImm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torusExtension_of_descended : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  intro R _ S π hlft hsurj G' _ G _ β h hG' Ω _ _ p
  haveI := hlft
  haveI := hsurj
  obtain ⟨t, rfl⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π p
  have h1 := (isGrpPullback_pullback G' t).comp h
  have h2 := isGrpPullback_pullback G (t ≫ π)
  obtain ⟨e, he, -⟩ := grpPullback_iso h1 h2
  haveI := he
  exact ⟨torusExtOfIso e (hG' Ω t).some⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  first | exact @GlobalTheory.CharValsFixed.main | exact GlobalTheory.CharValsFixed.main | (intros; apply GlobalTheory.CharValsFixed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  first | exact @GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | exact GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | (intros; apply GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

def UAct {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R))
    (act : 𝓞 E → (P.A ⟶ P.A)) (σ : R →+* R') (u : Sp R' ⟶ Xo.XF c) : Prop :=
  ∃ (G : Over (Sp R')) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
    IsGrpPullback G P.A (spMap σ) α ∧ IsGrpPullback G Xo.univ.t.G (u ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∀ a, ∃ f : G ⟶ G, f.left ≫ α = α ≫ (act a).left ∧ f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left

theorem UAct.uOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R R' : Type} [CommRing R] [CommRing R'] {P : PolAV (Sp R)}
    {act : 𝓞 E → (P.A ⟶ P.A)} {σ : R →+* R'} {u : Sp R' ⟶ Xo.XF c} (h : UAct Xo c P act σ u) : UOver Xo c P σ u :=
  let ⟨G, i, α, β, h₁, h₂, h₃, _⟩ := h
  ⟨G, i, α, β, h₁, h₂, h₃⟩

end GlobalTheory.UCovSep
end
end

