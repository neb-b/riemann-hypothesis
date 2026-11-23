module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactLarge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatKerLarge

theorem liftSemi_bijective_of_exact {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] {Z M N Z' M' N' : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N')
    (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M')
    (fN : N →ₛₗ[algebraMap R R'] N')
    (hi : Function.Injective i) (hid : Function.Exact i d) (hi' : Function.Injective i')
    (hid' : Function.Exact i' d') (hZ : ∀ z, i' (fZ z) = fM (i z)) (hN : ∀ x, d' (fM x) = fN (d x))
    (hM : Function.Bijective (liftSemi fM)) (hNi : Function.Injective (liftSemi fN)) :
    Function.Bijective (liftSemi fZ) := by
  have sqZ : ∀ w, i' (liftSemi fZ w) = liftSemi fM (i.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hZ]
  have sqN : ∀ w, d' (liftSemi fM w) = liftSemi fN (d.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hN]
  have hinj : Function.Injective (i.lTensor R') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (i.lTensor R') (d.lTensor R') := Module.Flat.lTensor_exact R' hid
  refine ⟨fun a b hab ↦ hinj (hM.1 ?_), fun z' ↦ ?_⟩
  · rw [← sqZ, ← sqZ, hab]
  · obtain ⟨m, hm⟩ := hM.2 (i' z')
    have h0 : d.lTensor R' m = 0 := hNi (by rw [← sqN, hm, hid'.apply_apply_eq_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hex m).1 h0
    exact ⟨w, hi' (by rw [sqZ, hm])⟩

theorem liftSemi_bijective_of_exact_large : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type 1) [AddCommGroup Z] [Module R Z] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type 1) [AddCommGroup N] [Module R N] (Z' : Type 1) [AddCommGroup Z'] [Module R' Z'] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type 1) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi
  exact liftSemi_bijective_of_exact i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi

end GlobalTheory.FlatKerLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem liftTests_and_mLat_of_ties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hB hG
  obtain ⟨hCore, hOff, hUsed⟩ :=
    GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 _ R F hB.char hB.ex
  obtain ⟨fw, -⟩ := hG.fw
  have hM : R.toRealDat.IsModels := hB.char.base.models
  have hEv : EvInj T R.toRealDat v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R.toRealDat κ v₀ hM fw
  have hRat : GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) :=
    _root_.GlobalTheory.TwistField.ratG_of_clauses D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O _ hB.nV hCore hOff hUsed ⟨fw⟩ hG.pins
      (fun i => hG.phase i hG.unif) hG.ioExt (fun i => (hG.oneMap i).1) hB.guard hG.unif hEv hG.cover
  have hLB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false :=
    GlobalTheory.TwistField.liftTestB_of_ratG D G Pl0 I0 T0 A3 _ R F false hG.unif hRat
  exact ⟨GlobalTheory.LiftTestCompare.liftTest_of_liftTestB _ hLB, hLB,
    GlobalTheory.GoodLat.Obj3.mLat3_of_tie T R F κ v₀ fw⟩

end GlobalTheory.PrimIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongPrincipalSmallExtension
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem liftsAlong_span_singleton : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ U M hM hSL B _ _ t ht hmt T N hN y u₀ h₀
  have calc5 := ((GlobalTheory.FamCalc.famCalc (Sp R) A).2.2.2.2)
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, a * t = 0 := fun a ha ↦ by
    have : a * t ∈ IsLocalRing.maximalIdeal B * Ideal.span {t} :=
      Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self t)
    rwa [hmt, Ideal.mem_bot] at this
  let Y : Over (Sp R) := Over.mk (y ≫ T.hom)
  let yy : Y ⟶ T := Over.homMk y rfl
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ yy)) := (GlobalTheory.FamCalc.famCalc (Sp R) A).1 T Y N yy hN
  have key : ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t})) ≫ yy =
      (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y ≫ T.hom) ⟶ T) := by
    ext1; rfl
  have h₁ : Same A (ev N (fst A Y) (snd A Y ≫ yy)) M (ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t}))) u₀ := by
    rw [calc5 T U Y _ N M yy _ u₀ hN.isLB hM.isLB, key]
    exact h₀
  obtain ⟨u, hu⟩ := hSL B t ht hkill (y ≫ T.hom) _ hN' u₀ h₁
  refine ⟨u, ?_⟩
  have := (calc5 T U Y Y N M yy (𝟙 _) u hN.isLB hM.isLB).1 hu
  rwa [Category.id_comp] at this

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
section
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

theorem symm_bilin_pow_dvd_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    ∀ k : ℕ, ∀ x y, (N : ℤ) ^ k ∣ B x y := by
  have hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y := by
    intro x
    have hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hμ _ i, sub_self]
    choose z hz using hd
    refine ⟨eb.symm z, ?_⟩
    apply eb.injective
    funext i
    rw [map_add (f := _), map_smul, LinearEquiv.apply_symm_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hz i]
  have hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x := by
    intro k hk x
    obtain ⟨y, hy⟩ := hdec x
    have hm := h0 (fun i => (eb x i : ZMod N))
    generalize μ (fun i => (eb x i : ZMod N)) = m at hy hm
    subst hy
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]
    rw [hB y m]
    obtain ⟨a, ha⟩ := hk m y
    obtain ⟨b, hb⟩ := hk y y
    rw [ha, hb]
    exact ⟨2 * a + N * b, by ring⟩
  have hcop : IsCoprime (N : ℤ) 2 := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)
    exact_mod_cast this
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    have h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y := by
      have hxy := hdiag k ih (x + y)
      have hx := hdiag k ih x
      have hy := hdiag k ih y
      have e : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [hB y x]
        ring
      rw [e]
      exact dvd_sub (dvd_sub hxy hx) hy
    exact (hcop.pow_left).dvd_of_dvd_mul_left h2

theorem symm_bilin_eq_zero_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    B = 0 := by
  ext x y
  have h := symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem linForm_eq_sum_lifts : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  intro Y _ n N _ hN hodd eb μ hμ ℓ
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let S : Submodule ℤ (LinearMap.BilinForm ℤ Y) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ) :=
    { toFun := fun b c => b (μ c) (μ c)
      map_add' := by intro a b; funext c; simp
      map_smul' := by intro k b; funext c; simp }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_
    · intro u v
      simp [x.2 u v, y.2 u v]
    · intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp [this]
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyChartOfAffineParameters
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Zar

variable {S : Scheme.{0}} {A : Over S}

theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) : Same A N M (z ≫ y) (z ≫ u) := by
  rw [same_iff hN hM] at h ⊢
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) h
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem same_ev_iff {T U V Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (j : V ⟶ T) (y : Y ⟶ V) (u : Y ⟶ U) :
    Same A (ev N (fst A V) (snd A V ≫ j)) M y u ↔ Same A N M (y ≫ j) u := by
  rw [same_iff (pull_isLB hN _) hM, same_iff hN hM, evc_ev hN]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

theorem exists_restrict {T Y Z : Over S} (y : Y ⟶ T) (z : Z ⟶ T) [IsOpenImmersion z.left] (p : Y.left)
    (hp : y.left p ∈ Set.range z.left) :
    ∃ (Y' : Over S) (i : Y' ⟶ Y) (t : Y' ⟶ Z), IsOpenImmersion i.left ∧ p ∈ Set.range i.left ∧ t ≫ z = i ≫ y := by
  let V := y.left ⁻¹ᵁ z.left.opensRange
  let Y' : Over S := Over.mk (V.ι ≫ Y.hom)
  let i : Y' ⟶ Y := Over.homMk V.ι rfl
  have hr : Set.range (i ≫ y).left ⊆ Set.range z.left := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let t : Y' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ y).left hr) (by
    rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  refine ⟨Y', i, t, inferInstanceAs (IsOpenImmersion V.ι), ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  ext1; exact IsOpenImmersion.lift_fac _ _ _

variable [GrpObj A]

theorem exists_same_of_local (hA : IsAbelianScheme A) {T U Y : Over S} {N : LB (A ⊗ T).left}
    {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M) (hI : Inj A M) (y : Y ⟶ T)
    (loc : ∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y) (u : Z ⟶ U), IsOpenImmersion z.left ∧
      p ∈ Set.range z.left ∧ Same A N M (z ≫ y) u) : ∃ u : Y ⟶ U, Same A N M y u := by
  choose Z z u ho hp hs using loc
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Y.left (fun p ↦ (Z p).left)
    (fun p ↦ (z p).left) (fun p ↦ by obtain ⟨q, hq⟩ := hp p; exact ⟨p, q, hq⟩) ho
  have hc : ∀ p q : Y.left, pullback.fst (z p).left (z q).left ≫ (u p).left =
      pullback.snd (z p).left (z q).left ≫ (u q).left := by
    intro p q
    let P : Over S := Over.mk (pullback.fst (z p).left (z q).left ≫ (Z p).hom)
    let a : P ⟶ Z p := Over.homMk (pullback.fst (z p).left (z q).left) rfl
    let b : P ⟶ Z q := Over.homMk (pullback.snd (z p).left (z q).left) (by
      rw [← Over.w (z q), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w]; rfl)
    have hab : a ≫ z p = b ≫ z q := by ext1; exact pullback.condition
    have h₁ := same_comp hN.isLB hM.isLB (hs p) a
    have h₂ := same_comp hN.isLB hM.isLB (hs q) b
    rw [← Category.assoc, hab, Category.assoc] at h₁
    rw [same_iff hN.isLB hM.isLB] at h₁ h₂
    have h := hI P _ _ ((same_iff hM.isLB hM.isLB _ _).2 (h₁.symm.trans h₂))
    exact congrArg (·.left) h
  have hg : ∀ p, (z p).left ≫ 𝒰.glueMorphisms (fun p ↦ (u p).left) hc = (u p).left :=
    𝒰.ι_glueMorphisms _ hc
  let g : Y ⟶ U := Over.homMk (𝒰.glueMorphisms (fun p ↦ (u p).left) hc) (𝒰.hom_ext _ _ fun (p : Y.left) ↦
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (hg p))).trans
      ((Over.w (u p)).trans (Over.w (z p)).symm))
  refine ⟨g, same_of_local S A T U hA N M hN hM Y y g fun p ↦ ⟨Z p, z p, ho p, hp p, ?_⟩⟩
  have e : z p ≫ g = u p := by ext1; exact hg p
  rw [e]
  exact hs p

theorem fam_ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hM : (AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add _ _ _ _

end GlobalTheory.DualCon.Zar

namespace GlobalTheory.DualCon

theorem chartAt_of_affine : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M →
    (∀ (T : Over S) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) →
    ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A _ hA U M hM hI aff T N hN
  let W : Set T.left := {x | ∃ (Z : Over S) (z : Z ⟶ T) (u : Z ⟶ U), IsOpenImmersion z.left ∧
    x ∈ Set.range z.left ∧ Same A N M z u}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨Z, z, u, ho, hx, hs⟩
    exact ⟨Set.range z.left, fun x' hx' ↦ ⟨Z, z, u, ho, hx', hs⟩, z.left.opensRange.2, hx⟩
  refine ⟨⟨W, hW⟩, fun Y y ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨i, q, hq⟩ := T.left.affineCover.exists_eq (y.left p)
    let V : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
    let j : V ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
    haveI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))
    haveI : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
    obtain ⟨O, hO⟩ := aff V _ (Zar.fam_ev hN j)
    obtain ⟨Y', c, t, -, ⟨r, hr⟩, ht⟩ := Zar.exists_restrict y j p ⟨q, hq⟩
    have h₁ : t.left r ∈ O := (hO Y' t).1 ⟨c ≫ u, by
      rw [Zar.same_ev_iff hN.isLB hM.isLB, ht]
      exact Zar.same_comp hN.isLB hM.isLB hu c⟩ r
    let Z : Over S := Over.mk (O.ι ≫ V.hom)
    let k : Z ⟶ V := Over.homMk O.ι rfl
    haveI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.ι)
    obtain ⟨v, hv⟩ := (hO Z k).2 fun w ↦ w.2
    refine ⟨Z, k ≫ j, v, by rw [Over.comp_left]; infer_instance, ⟨⟨t.left r, h₁⟩, ?_⟩,
      (Zar.same_ev_iff hN.isLB hM.isLB _ _ _).1 hv⟩
    change (t ≫ j).left r = _
    rw [ht, ← hr]
    rfl
  · refine Zar.exists_same_of_local hA hN hM hI y fun p ↦ ?_
    obtain ⟨Z, z, u, ho, hx, hs⟩ := h p
    obtain ⟨Y', c, t, hc, hp, ht⟩ := Zar.exists_restrict y z p hx
    exact ⟨Y', c, t ≫ u, hc, hp, ht ▸ Zar.same_comp hN.isLB hM.isLB hs t⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAbelianSchemeDVROfGenericIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoAb

theorem lbIso_of_generic_pullback : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Scheme.{0}) (a : A ⟶ Sp L) (φ : A ⟶ G.left), IsAbelianScheme G → IsPullback φ a G.hom (spMap (algebraMap W L)) → ∀ M M' : LB G.left, M.IsLB → M'.IsLB → LBIso (M.pull φ) (M'.pull φ) → LBIso M M' := by
  intro W L _ _ _ _ _ _ G _ A a φ hG hφ M M' hM hM' h
  have hi : pullback.fst G.hom (spMap (algebraMap W L)) = hφ.isoPullback.inv ≫ φ := hφ.isoPullback_inv_fst.symm
  have h' : LBIso (M.pull (pullback.fst G.hom (spMap (algebraMap W L))))
      (M'.pull (pullback.fst G.hom (spMap (algebraMap W L)))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.isoPullback.inv hi h
  exact GlobalTheory.GenericIsoConst.lbIso_of_generic W L G hG M M' hM hM' h'

end GlobalTheory.GenericIsoAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackOfLocalUnitGenerators
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem lbIso_pull_of_genOn (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens)
    (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ)
    (hs : ∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x))
    (hg : ∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k →
      gm f t (W x ⊓ W y) (g x y) =
        gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) :
    LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  have le : ∀ p : (PUnit → J) × L.ι, ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 ≤
      L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit) := fun p y h =>
    ⟨h.2, (mem_pull (L := (⟨J, W, g⟩ : LB X)) (F := f)).1 h.1⟩
  refine ⟨⟨fun p => res (le p) (s (p.1 PUnit.unit) p.2)⁻¹⟩, (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have v : ∀ p : (PUnit → J) × L.ι, y ∈ ((⟨J, W, g⟩ : LB X).pull f).U p.1 ⊓ L.U p.2 →
      gm (𝟙 Y) y _ (res (le p) (s (p.1 PUnit.unit) p.2)⁻¹) =
        (gm (𝟙 Y) y (L.U p.2 ⊓ f ⁻¹ᵁ W (p.1 PUnit.unit)) (s (p.1 PUnit.unit) p.2))⁻¹ := fun p hp =>
    (gm_res _ y _ hp _).trans (map_inv _ _)
  have hp' := le p hp
  have hq' := le q hq
  have e1 := gm_pull_g (⟨J, W, g⟩ : LB X) f (𝟙 Y) y p.1 q.1 hp.1 hq.1
  have e2 : gm (𝟙 Y ≫ f) y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) =
      gm f y (W (p.1 PUnit.unit) ⊓ W (q.1 PUnit.unit)) (g _ _) := by
    rw [Category.id_comp]
  have e3 := hg (p.1 PUnit.unit) (q.1 PUnit.unit) y p.2 hp'.2 hq'.2 hp'.1
  have e4 := hs (q.1 PUnit.unit) p.2 q.2 y hp'.1 hq'.1 hq'.2
  have e5 := (e1.trans e2).trans (e3.trans (congrArg (· * _) e4))
  refine (v p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
    ((gm_div' ((⟨J, W, g⟩ : LB X).pull f) L (𝟙 Y) y p q hp hq).trans (congrArg (· * _) e5)) (v q hq)).symm)
  have key : ∀ {G : Type} [CommGroup G] (a b c : G), c⁻¹ = a * b * c⁻¹ * a⁻¹ * b⁻¹ := by
    intro G _ a b c
    rw [mul_assoc (a * b * c⁻¹), ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
  exact key _ _ _

end GlobalTheory.PinchLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteBigCellToBaseProdAffineSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyQuasiFinite_bigCell_to_base_prod_affineSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  first | exact @GlobalTheory.LogPole.locallyQuasiFinite_cellMap | exact GlobalTheory.LogPole.locallyQuasiFinite_cellMap | (intros; apply GlobalTheory.LogPole.locallyQuasiFinite_cellMap <;> assumption)
end

