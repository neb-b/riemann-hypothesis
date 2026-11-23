module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0032
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.EtaleCohomology.EtaleSheaves.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.KummerClassAddOfUnitSecAdd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom x) h

private theorem sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U)
    (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add (F.obj.map g.op).hom x y

private theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (x : Sec F U) : Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul (φ.hom.app (op U)).hom c x

private theorem unitSec_pow_mul {W : Scheme.{0}} (u w : (Γ(W, ⊤))ˣ) (c : ℕ) :
    unitSec (u ^ c * w) = unitSec w + c • unitSec u := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', mul_assoc, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]
    abel

private theorem kumT_pow_mul (q : ℕ) [NeZero q] (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (u w : (Γ(W, ⊤))ˣ)
    (hu : (u : Γ(W, ⊤)) = ζ.1) (c : ℕ) :
    kumT q W (u ^ c * w) = kumT q W w + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (u ^ c * w) (u ^ (c + 1) * w)
      (by rw [pow_succ', mul_assoc, Units.val_mul, hu])
    rw [h, ih, succ_nsmul, add_assoc]

theorem UpperTheory.kummer_class_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (a : Sec (tw q 1) V), unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from a) → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) a := by
  intro q _ V hq v v' a h
  refine (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) _ V).1 _ _ ?_
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V a
  refine ⟨S, hS, fun W g hg => ?_⟩
  show Sec.res g (kumT q V v') = Sec.res g (kumT q V v + Sec.map (resι _ (tw q 1)) a)
  have hK := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g
  let b : Sec (UpperTheory.Deg2.T q) V := a
  let bW : Sec (UpperTheory.Deg2.T q) W := Sec.res g a
  have hb : Sec.res g (Sec.map (UpperTheory.Deg2.kap q) b) = Sec.map (UpperTheory.Deg2.kap q) bW :=
    (sec_map_res (UpperTheory.Deg2.kap q) g b).symm
  have h' : unitSec (Units.map g.appTop.hom.toMonoidHom v') = unitSec (Units.map g.appTop.hom.toMonoidHom v) +
      Sec.map (UpperTheory.Deg2.kap q) bW := by
    have h0 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) b := h
    have h1 := congrArg (Sec.res g) h0
    rw [sec_res_add, UpperTheory.PicD.unitSec_res, UpperTheory.PicD.unitSec_res, hb] at h1
    exact h1
  rw [sec_res_add, hK v hq, hK v' hq, ← sec_map_res]
  rcases hP W g hg with h0 | ⟨ζ, c, hc⟩
  · have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = 0 := by
      have : bW = 0 := h0
      rw [this]
      exact sec_map_zero _
    rw [h0, sec_map_zero, add_zero]
    rw [h2, add_zero] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h']
  · have hun : IsUnit ζ.1 := isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q)]
      exact prim_pow q ζ⟩
    obtain ⟨u, hu⟩ := hun
    have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = c • unitSec u := by
      have : bW = c • (show Sec (UpperTheory.Deg2.T q) W from twGen 1 ζ) := hc
      rw [this, sec_map_nsmul, (UpperTheory.Deg2.kap_spec q).2.2.1 W ζ u hu]
    rw [h2, ← unitSec_pow_mul] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h', kumT_pow_mul q W ζ u _ hu c, hc, sec_map_nsmul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.KummerMapAddOfUnitSecAdd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory

private theorem unitSec_mul {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) :
    unitSec (a * b) = unitSec a + unitSec b :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul a)) (ULift.up (Additive.ofMul b))

private theorem unitSec_pow {U : Scheme.{0}} (a : (Γ(U, ⊤))ˣ) (c : ℕ) :
    unitSec (a ^ c) = c • unitSec a := by
  unfold unitSec ofRings.sec
  exact map_nsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))) c
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩)

private theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  exact (congrArg (fun f => f.hom (ULift.up (Additive.ofMul u))) h).symm

private theorem unitSec_loc {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) :
    Loc U fun _ g => Units.map g.appTop.hom.toMonoidHom a = Units.map g.appTop.hom.toMonoidHom b := by
  have hx := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U
    ((show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩) -
      (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul b⟩)) (by
    rw [map_sub]
    exact sub_eq_zero.mpr h)
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hx ?_
  intro V g hg
  rw [map_sub, sub_eq_zero] at hg
  have h2 := congrArg (fun t => Additive.toMul (ULift.down t)) hg
  exact h2

private theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => f.hom x) (φ.hom.naturality g.op)).symm

private theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := by
  simp only [Sec.res, map_add (f := _)]

private theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (a : Sec F U) : Sec.map φ (c • a) = c • Sec.map φ a :=
  map_nsmul (φ.hom.app (op U)).hom c a

private theorem kum_pow (q : ℕ) [NeZero q] {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (z : (Γ(W, ⊤))ˣ)
    (hz : (z : Γ(W, ⊤)) = ζ.1) (c : ℕ) (v : (Γ(W, ⊤))ˣ) :
    kumT q W (z ^ c * v) = kumT q W v + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (z ^ c * v) (z ^ (c + 1) * v) (by
      rw [← hz, pow_succ']; simp [mul_assoc])
    rw [h, ih, succ_nsmul, add_assoc]

end UpperTheory

private theorem kumT_eq_of_unitSec_eq (q : ℕ) [NeZero q] {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) : kumT q U a = kumT q U b := by
  apply (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) _ U).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (UpperTheory.unitSec_loc a b h) ?_
  intro V g hg
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g a hq, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g b hq, hg]

theorem UpperTheory.kummerMap_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) → ∀ (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V), Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s) + unitSec v = unitSec v' → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) s := by
  intro q _ κ hκ V hq v v' s hs
  apply (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) _ V).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V s) ?_
  intro W g hg
  have hqW : IsUnit (q : Γ(W, ⊤)) := by
    have h1 := hq.map g.appTop.hom
    simpa using h1
  have hsW := congrArg (Sec.res g) hs
  rw [UpperTheory.res_add, UpperTheory.unitSec_res, UpperTheory.unitSec_res,
    UpperTheory.res_map κ g (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s)] at hsW
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v' hq, UpperTheory.res_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v hq, UpperTheory.res_map]
  simp only at hsW
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · have e0 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) = 0 := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s = 0 := h0
      rw [h3]
      simp only [Sec.map, map_zero]
    rw [e0, zero_add] at hsW
    rw [h0]
    simp only [Sec.map, map_zero, add_zero]
    exact (kumT_eq_of_unitSec_eq q hqW _ _ hsW).symm
  · obtain ⟨u, hu⟩ : ∃ u : (Γ(W, ⊤))ˣ, (u : Γ(W, ⊤)) = ζ.1 :=
      ⟨Units.ofPowEqOne ζ.1 q ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).1 ζ) (NeZero.ne q), rfl⟩
    have hk := hκ W ζ u hu
    simp only at hk
    have e1 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) =
        c • unitSec u := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s =
          c • (twGen 1 ζ : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) W) := hc
      rw [h3]
      exact (UpperTheory.map_nsmul' κ c (twGen 1 ζ)).trans (by rw [hk])
    rw [e1, ← UpperTheory.unitSec_pow, ← UpperTheory.unitSec_mul] at hsW
    have h2 := kumT_eq_of_unitSec_eq q hqW _ _ hsW
    rw [UpperTheory.kum_pow q ζ u hu c] at h2
    rw [← h2, hc, UpperTheory.map_nsmul']
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ModuleFiniteIntegralClosureFiniteExtPerfect
section
private theorem UpperTheory.finite_of_finite_comp_injective_noetherian {P B C : Type*} [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing P] (f : P →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  have hC : Module.Finite P C := h
  let gl : B →ₗ[P] C :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply,
          RingHom.id_apply] }
  haveI : IsNoetherian P C := isNoetherian_of_isNoetherianRing_of_finite P C
  haveI : IsNoetherian P B := isNoetherian_of_injective gl hg
  exact Module.IsNoetherian.finite P B

private theorem UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect (k : Type*) [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
    (ι : Type*) [Finite ι] [ExpChar (MvPolynomial ι k) p] (e : ℕ) :
    (iterateFrobenius (MvPolynomial ι k) p e).Finite := by
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_pos k p).ne')
    · simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have hc : (iterateFrobenius (MvPolynomial ι k) p e).comp MvPolynomial.C
        = MvPolynomial.C.comp (iterateFrobenius k p e) := by
      ext a
      simp [iterateFrobenius_def, map_pow]
    rw [hc]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (bijective_iterateFrobenius k p e).2)

private theorem UpperTheory.module_finite_integralClosure_of_frobenius_finite (P L F : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [Field L] [Algebra P L] [IsFractionRing P L] [Field F] [Algebra P F]
    [Algebra L F] [IsScalarTower P L F] [FiniteDimensional L F] (p : ℕ) [ExpChar P p]
    [ExpChar F p] (hσ : ∀ e, (iterateFrobenius P p e).Finite) :
    Module.Finite P (integralClosure P F) := by
  let E := separableClosure L F
  haveI : FiniteDimensional E F := FiniteDimensional.right L E F
  haveI : IsPurelyInseparable E F := separableClosure.isPurelyInseparable L F
  haveI : ExpChar E p := IntermediateField.expChar' E p
  haveI : IsScalarTower P E F := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply P L E r, ← IsScalarTower.algebraMap_apply L E F,
      IsScalarTower.algebraMap_apply P L F])
  set e := IsPurelyInseparable.exponent E F
  have hpow : ∀ x : F, x ^ p ^ e ∈ E := fun x => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p x
    rw [← hy]
    exact y.2
  haveI : Module.Finite P (integralClosure P E) :=
    IsIntegralClosure.finite P L E (integralClosure P E)
  have hq : p ^ e ≠ 0 := pow_ne_zero _ (expChar_pos F p).ne'
  let fr : integralClosure P F →+* integralClosure P E :=
    { toFun := fun b => ⟨⟨b.1 ^ p ^ e, hpow b.1⟩, by
        rw [mem_integralClosure_iff,
          ← isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) (algebraMap E F).injective]
        exact b.2.pow _⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [mul_pow]
      map_zero' := by
        apply Subtype.ext; apply Subtype.ext; simp [zero_pow hq]
      map_add' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [add_pow_expChar_pow] }
  have hinj : Function.Injective fr := by
    intro a b h
    have h' : a.1 ^ p ^ e = b.1 ^ p ^ e :=
      congrArg (fun y : integralClosure P E => ((y.1 : E) : F)) h
    apply Subtype.ext
    apply (iterateFrobenius F p e).injective
    simpa [iterateFrobenius_def] using h'
  have hcomp : fr.comp (algebraMap P (integralClosure P F)) =
      (algebraMap P (integralClosure P E)).comp (iterateFrobenius P p e) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    simp only [fr, iterateFrobenius_def, map_pow, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    have h1 : ((algebraMap P (integralClosure P F) r : integralClosure P F) : F) =
        algebraMap P F r := rfl
    have h2 : (((algebraMap P (integralClosure P E) r : integralClosure P E) : E) : F) =
        algebraMap P F r := by
      rw [IsScalarTower.algebraMap_apply P E F]
      rfl
    simp only [SubmonoidClass.coe_pow, h1, h2]
  have hf := UpperTheory.finite_of_finite_comp_injective_noetherian (algebraMap P (integralClosure P F)) fr hinj (by
    rw [hcomp]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp (hσ e))
  exact RingHom.finite_algebraMap.mp hf

theorem UpperTheory.module_finite_integralClosure_finiteExt_perfect :
    ∀ (k A K F : Type) [Field k] [PerfectField k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
        [Field K] [Algebra A K] [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
        [FiniteDimensional K F], Module.Finite A (integralClosure A F) := by
  intro k A K F
  intros
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨p, hp⟩ := ExpChar.exists k
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAF : Function.Injective (algebraMap A F) := by
    rw [IsScalarTower.algebraMap_eq A K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective A K)
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hAF
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hginj
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) F :=
    (faithfulSMul_iff_algebraMap_injective _ F).mpr (hAF.comp hginj)
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) F := FractionRing.liftAlgebra _ F
  letI : Algebra (FractionRing A) F := FractionRing.liftAlgebra A F
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    FractionRing.liftAlgebra _ (FractionRing A)
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    inferInstance
  haveI : FiniteDimensional (FractionRing A) F := by
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (RingEquiv.refl F) ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) k))
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) F,
      ← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A),
      IsScalarTower.algebraMap_apply _ A (FractionRing A),
      ← IsScalarTower.algebraMap_apply A (FractionRing A) F,
      ← IsScalarTower.algebraMap_apply _ A F]
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) F :=
    Module.Finite.trans (FractionRing A) F
  haveI : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  haveI : ExpChar F p := expChar_of_injective_algebraMap hAF p
  haveI : ExpChar (MvPolynomial (Fin s) k) p :=
    expChar_of_injective_algebraMap (algebraMap k (MvPolynomial (Fin s) k)).injective p
  have hP := UpperTheory.module_finite_integralClosure_of_frobenius_finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) F p
    (UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect k p (Fin s))
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ A
  let φ : integralClosure (MvPolynomial (Fin s) k) F →ₗ[MvPolynomial (Fin s) k]
      integralClosure A F :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun y =>
    ⟨⟨y.1, isIntegral_trans (R := MvPolynomial (Fin s) k) y.1 y.2⟩, rfl⟩
  haveI : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A F) :=
    Module.Finite.of_surjective φ hφ
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A (integralClosure A F)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistGeneratorSmulEqZeroImp
section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.twist_generator_smul_eq_zero_imp :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (C : CommRingCat.{0}) [Nontrivial C] (ζ : Prim q C) (c : ULift.{1} (ZMod q)), c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj C) = 0 → c = 0 := by
  intro q _ i C _ ζ c h
  obtain ⟨f, hf⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i C).2 ζ
  have h' : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) :
      (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) = 0 := h
  have h2 := congrArg f h'
  rw [map_smul, hf, map_zero] at h2
  simpa using h2
end

