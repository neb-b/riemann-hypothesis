module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwMul

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem tw_mul_isTensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  intro q _ i j k hk
  obtain ⟨K, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  have hzK : ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) :=
    _root_.GlobalTheory.EtC.isZero_tensor_of_deg_zero (ZMod q) τ hτ (fun s hs => HomologicalComplex.isZero_single_obj_X _ _ _ _ hs)
      (fun t ht => HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom q i j k hk τ
  have hsurj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective q i j k hk τ hτ φ hφ
  have hinj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective q i j k hk (GlobalTheory.T.tateTwistGenerator_tmul_order_locally q i j) τ hτ φ hφ
  have hM := GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections (ZMod q) φ
  haveI : Mono φ := hM.2.1.2 hinj
  haveI : Epi φ := hM.2.2.1.2 hsurj
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  let u : K ⟶ sgl (tw q k) := HomologicalComplex.mkHomToSingle (inv φ) (fun a ha => (hzK a (by simp at ha; omega)).eq_of_src _ _)
  have hu0 : u.f 0 = inv φ ≫ sglι (tw q k) := HomologicalComplex.mkHomToSingle_f _ _
  haveI : ∀ w, IsIso (u.f w) := by
    intro w
    by_cases hw : w = 0
    · subst hw; rw [hu0]; unfold sglι; exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)
    · exact ⟨⟨0, (hzK w hw).eq_of_src _ _, (HomologicalComplex.isZero_single_obj_X _ _ _ _ hw).eq_of_src _ _⟩⟩
  haveI : IsIso u := HomologicalComplex.Hom.isIso_of_components u
  obtain ⟨ν, hν⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.2 u
  refine ⟨ν, GlobalTheory.T.isTensor_of_compat_isIso_target (ZMod q) τ ν u inferInstance hν hτ, fun U ζ => ?_⟩
  have h := hν U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  simp only [HomologicalComplex.id_f, secMap_id] at h
  rw [← h, ← hφ, hu0, secMap_comp, ← secMap_comp φ (inv φ), IsIso.hom_inv_id, secMap_id]

end GlobalTheory.EtC.TwMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnity
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC


open GlobalTheory.EtC.MuTw in
theorem GlobalTheory.EtC.tw_one_mu : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  intro q _
  have hunit : ∀ (C : Type) [CommRing C], IsUnit (q : C) → IsUnit (q : Γ(Spec (CommRingCat.of C), ⊤)) := by
    intro C _ hC
    have := hC.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simpa using this
  let e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C) :=
    fun C _ hC =>
      ((AddEquiv.ofBijective ((etaS q).hom.app (op (Spec (CommRingCat.of C)))).hom.toAddMonoidHom
        ⟨GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q _ (hunit C hC), GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective q _ (hunit C hC)⟩).trans AddEquiv.ulift).trans
        (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv q).toAdditive
  refine ⟨e, ?_⟩
  intro C D _ _ φ hC hD x
  apply Units.ext
  have h1 := etaS_res q (Spec.map (CommRingCat.ofHom φ)) x
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (muVal q (Sec.map (etaS q) (Sec.res (Spec.map (CommRingCat.ofHom φ)) x))) = φ ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (muVal q (Sec.map (etaS q) x)))
  rw [h1, muVal_res]
  exact congrArg (fun f => f.hom (muVal q (Sec.map (etaS q) x))) h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUnique
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUniq

theorem op_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) →
    ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  intro Q q _ hq i ρ ρ' h E n x
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.EtC.SemiMap.factor_extCx Q q hq _ _ ρ
  obtain ⟨u', hu'⟩ := _root_.GlobalTheory.EtC.SemiMap.factor_extCx Q q hq _ _ ρ'
  have e1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ u hu).1 E n x
  have e2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ' u' hu').1 E n x
  have hε := GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation Q q hq i _ u u' (fun U ζ => by rw [← hu, ← hu', h])
  haveI := _root_.GlobalTheory.EtC.ExtQis.quasiIso_extAug Q q hq i
  haveI : (res (ZMod q) (tw q i)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q i)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).2 u u' hε
  have e3 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 u u' ⟨H⟩ ((chains (ZMod q)).obj E) n).2
  rw [e1, e2, e3]

end GlobalTheory.EtC.RedUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedExists

def constCx {R : Type} [CommRing R] (F : Shv R) : Cx R where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

theorem ext_map (Q q : ℕ) (hq : q ∣ Q) (F : Shv (ZMod Q)) (G : Shv (ZMod q))
    (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hf : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) :
    ∃ α : (extSh (ZMod.castHom hq (ZMod q))).obj F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U),
      Sec.map α (extSh.sec (ZMod.castHom hq (ZMod q)) F U a) = f U a := by
  let ρ : SemiMap (constCx F) (constCx G) :=
    { app := fun U _ => f U
      nat := fun g _ a => hf _ _ g a
      comm := fun U s t a => by
        show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)
        simp [Sec.map]
        exact ((f U).map_zero).symm }
  exact ⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0,
    fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩

def semiOfExt {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) : SemiMap I K where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom.comp ((extπ (ZMod.castHom hq (ZMod q)) I).app U s)
  nat g s a := by
    have h := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op))
      ((extπ (ZMod.castHom hq (ZMod q)) I).app _ s a)).symm
    refine h.trans ?_
    exact congrArg (fun x => ((m.f s).hom.app (op _)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).nat g s a)
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a))) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · exact congrArg (fun x => ((m.f t).hom.app (op U)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).comm U s t a)

theorem semiOfExt_app {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (semiOfExt hq m).app U s a = Sec.map (m.f s) (extSh.sec (ZMod.castHom hq (ZMod q)) (I.X s) U a) := rfl

def powPrim {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.EtC.PrimBasic.prim_basic Q A).2.2.2.2.2 q hq ζ
    rw [← h]
    exact ξ.2⟩

theorem powPrim_map {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (ζ : Prim Q A) : (powPrim hq ζ).map φ = powPrim hq (ζ.map φ) :=
  Subtype.ext (map_pow φ _ _)

theorem nsmul_mod_of {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) (n : ℕ) :
    n • x = (n % q) • x := by
  have hq : q • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (by simp)
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]

theorem twRed_sec : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ), ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → f U (twGen i ζ) = twGen i ξ := by
  intro Q q _ _ hq i
  let M : Shv (ZMod Q) := (GlobalTheory.EtC.restr (ZMod.castHom hq (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)
  have ts := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have := ts.2.2.2.1 V U g (powPrim hq ζ)
    rw [powPrim_map] at this
    exact this
  have hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q := by
    intro u
    show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a h
    have hq1 : (ζ.1 ^ (Q / q)) ^ q = 1 := (GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)
    have hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val := by
      rw [hcast]
      show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)
      rw [h, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]
      rw [pow_add, pow_mul, hq1, one_pow, mul_one]
    have h5 := ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw
    show (twGen i (powPrim hq ξ) : Sec (tw q i) U) =
      ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)
    have hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q := by
      rw [show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]
    rw [h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]
  obtain ⟨β, hβ, -⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2
  refine ⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩,
    fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩
  · intro V U g a
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm
  · intro U ζ ξ h
    have h1 := hβ U ζ
    have h2 : powPrim hq ζ = ξ := Subtype.ext h.symm
    exact h1.trans (congrArg (twGen i) h2)

theorem redMap_exists (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ) :
    ∃ ρ : SemiMap (res _ (tw Q i)) (res _ (tw q i)), ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
      ξ.1 = ζ.1 ^ (Q / q) → ρ.app U 0 (resGen i ζ) = resGen i ξ := by
  obtain ⟨f, hf, hfg⟩ := twRed_sec Q q hq i
  obtain ⟨α, hα⟩ := ext_map Q q hq (tw Q i) (tw q i) f hf
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q i)
  have hQ := _root_.GlobalTheory.EtC.ExtQis.quasiIso_extAug Q q hq i
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))
    (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i))
    (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1
    ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i))
  refine ⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩
  have hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 := by
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        m.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)
  have hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        α ≫ resι _ (tw q i) := by
    rw [HomologicalComplex.comp_f, ← hι]
    change ((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    exact Category.assoc _ _ _
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i) := by
    have e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
        ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 := by rw [hm]
    rw [hv, hw] at e
    exact (cancel_epi _).1 e
  rw [semiOfExt_app]
  change Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)
  rw [← extSh.sec_map, ← hfg U ζ ξ h, ← hα]
  have e2 := congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key
  exact e2

theorem red_exists : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  intro Q q _ _ hq i U ζ ξ h
  exact pick_spec (redMap_exists Q q hq i) U ζ ξ h

end GlobalTheory.EtC.RedExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceIntegralOfPreservedLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatTrace

open Polynomial

theorem aeval_mulVec_of_eigen {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : Type*}
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (hv : Q *ᵥ v = μ • v) (p : R[X]) :
    (aeval Q p) *ᵥ v = (aeval μ p) • v := by
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]

theorem aeval_restrict_coe {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (L : Submodule ℤ (n → S))
    (hQ : ∀ x ∈ L, (Q.mulVecLin.restrictScalars ℤ) x ∈ L) (p : ℤ[X]) (x : L) :
    ((aeval (LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ) p x : L) : n → S) =
      (aeval Q p) *ᵥ (x : n → S) := by
  set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ
  have hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ',
        ← Matrix.mulVec_mulVec, ← ih]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hq,
      Matrix.add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

theorem isIntegral_trace_of_isIntegral {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨p, hpm, hp0⟩ := hM
  have hpM : aeval M p = 0 := by rw [aeval_def]; exact hp0
  set M' := M.map φ
  have hpM' : aeval M' p = 0 := by
    have h := Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hpM, map_zero] at h
    exact h
  have htr : φ M.trace = M'.trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, M', map_sum]
  have hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have h0 : M'.charpoly.eval μ = 0 := (Polynomial.mem_roots'.1 hμ).2
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hev : M' *ᵥ v = μ • v := by
      have h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v := by
        rw [Matrix.sub_mulVec]
        congr 1
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [h1, sub_eq_zero] at hv
      exact hv.symm
    have h2 := aeval_mulVec_of_eigen M' μ v hev p
    rw [hpM', Matrix.zero_mulVec] at h2
    have hz : aeval μ p = 0 := by
      by_contra hne
      exact hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)
    exact ⟨p, hpm, by rw [← aeval_def]; exact hz⟩
  have hsum : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    have := multiset_sum_mem (M'.charpoly.roots)
      (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))
    exact (mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this
  rw [← htr] at hsum
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum

theorem isIntegral_of_preserves_lattice {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hA : ∀ x ∈ Λ, A *ᵥ x ∈ Λ) :
    IsIntegral ℤ A := by
  set Lz := Λ.restrictScalars ℤ
  have : Module.Finite ℤ Lz := Module.Finite.iff_fg.mpr hfg.restrictScalars
  have hAz : ∀ x ∈ Lz, (A.mulVecLin.restrictScalars ℤ) x ∈ Lz := fun x hx => hA x hx
  obtain ⟨p, hpm, hp⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero ℤ
      (LinearMap.restrict (A.mulVecLin.restrictScalars ℤ) hAz)
  have hpA : aeval A p = 0 := by
    have hker : ∀ x ∈ Λ, (aeval A p) *ᵥ x = 0 := by
      intro x hx
      have h := aeval_restrict_coe A Lz hAz p ⟨x, hx⟩
      rw [hp] at h
      rw [← h]; rfl
    have hle : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker (aeval A p).mulVecLin :=
      Submodule.span_le.2 fun x hx => hker x hx
    rw [hsp] at hle
    ext i j
    have h := congrFun (hle (Submodule.mem_top : Pi.single j (1 : E) ∈ ⊤)) i
    simpa [Matrix.mulVec_single] using h
  exact ⟨p, hpm, by rw [← aeval_def]; exact hpA⟩

theorem trace_isIntegral_of_preserves_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, A *ᵥ x ∈ Λ) →
    IsIntegral ℤ A.trace := by
  intro E _ _ r Λ A hfg hsp hA
  exact isIntegral_trace_of_isIntegral A (isIntegral_of_preserves_lattice Λ A hfg hsp hA)

end GlobalTheory.LatTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSkewHermitianReal
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem skew_transpose_mul_add_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    Xᵀ * G + G * X.map (fun x => cc x) = 0 := by
  ext i j
  have h := hX (Pi.single i 1) (Pi.single j 1)
  have c0 : cc (0 : E) = 0 := map_zero _
  have c1 : cc (1 : E) = 1 := map_one _
  have hc : ∀ b : Fin r, cc (if b = j then (1 : E) else 0) = if b = j then 1 else 0 := by
    intro b; split_ifs <;> simp [c0, c1]
  simp [herm, Matrix.mulVec_single, Pi.single_apply, c0, c1, hc, Matrix.mul_apply] at h ⊢
  exact h

theorem conj_eq_of_skew {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    X.map (fun x => cc x) = -(G⁻¹ * Xᵀ * G) := by
  have h := skew_transpose_mul_add_mul_conj G X hX
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have h2 : G * X.map (fun x => cc x) = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right h
  calc X.map (fun x => cc x) = G⁻¹ * (G * X.map (fun x => cc x)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = -(G⁻¹ * Xᵀ * G) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]

theorem trace_mul_skew_mem_maximalRealSubfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  intro E _ _ _ r G X Y _ hG hX hY
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hXc := conj_eq_of_skew G X hG hX
  have hYc := conj_eq_of_skew G Y hG hY
  rw [← IsCMField.complexConj_eq_self_iff]
  change cc (X * Y).trace = (X * Y).trace
  have hmap : cc (X * Y).trace = ((X * Y).map (fun x => cc x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum (IsCMField.complexConj E : E →+* E) _ _
  have hmul : (X * Y).map (fun x => cc x) = X.map (fun x => cc x) * Y.map (fun x => cc x) :=
    Matrix.map_mul (f := ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E))
  rw [hmap, hmul, hXc, hYc, neg_mul_neg]
  have e1 : G⁻¹ * Xᵀ * G * (G⁻¹ * Yᵀ * G) = G⁻¹ * (Xᵀ * Yᵀ * G) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

end GlobalTheory
end

