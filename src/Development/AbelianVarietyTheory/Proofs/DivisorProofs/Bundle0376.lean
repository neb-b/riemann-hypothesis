module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (f ≫ g) x = Sec.res f (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem sec_res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem sec_coprod : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  intro R _ F U ι V j hU
  let e : ∐ V ≅ U := (coproductIsCoproduct V).coconePointUniqueUpToIso hU
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (coproductIsCoproduct V).comp_coconePointUniqueUpToIso_hom hU ⟨i⟩
  have hb := GlobalTheory.T.sec_sigma_res_bijective R F V
  have hiso : Function.Bijective (fun x : Sec F U => Sec.res e.hom x) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun y => Sec.res e.inv y, fun x => ?_, fun y => ?_⟩
    · simp only
      rw [← sec_res_comp', e.inv_hom_id, sec_res_id']
    · simp only
      rw [← sec_res_comp', e.hom_inv_id, sec_res_id']
  have hfun : (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) =
      (fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a) ∘ (fun x : Sec F U => Sec.res e.hom x) := by
    funext x i
    simp only [Function.comp_apply]
    rw [← sec_res_comp', he i]
  rw [hfun]
  exact hb.comp hiso

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_descend_along_locallyBijective : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  first | (exact @GlobalTheory.EtC.desc_loc) | (exact GlobalTheory.EtC.desc_loc) | (intros; apply GlobalTheory.EtC.desc_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultiple
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open ChangeOfRings in
theorem unit_eq_zero_dvd {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) (N : ModuleCat.{1} (ULift.{1} (ZMod Q))) (y : N)
    (h : ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app N).hom y = 0) :
    ∃ z : N, y = q • z := by
  change (1 : ULift.{1} (ZMod q)) ⊗ₜ[ULift.{1} (ZMod Q), uliftHom (ZMod.castHom hq (ZMod q))] y = 0 at h
  let K : AddSubgroup N := (DistribSMul.toAddMonoidHom N q).range
  let gZ : ℤ →+ (N →+ N ⧸ K) := zmultiplesHom _ (QuotientAddGroup.mk' K)
  have hgZ : gZ q = 0 := by
    ext m
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply,
      QuotientAddGroup.mk'_apply]
    rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let g : ZMod q →+ (N →+ N ⧸ K) := ZMod.lift q ⟨gZ, hgZ⟩
  let f : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q))))
      →+ (N →+ N ⧸ K) := g.comp (AddEquiv.ulift : ULift.{1} (ZMod q) ≃+ ZMod q).toAddMonoidHom
  have hf : ∀ (r : ULift.{1} (ZMod Q)) s (n : N), f (r • s) n = f s (r • n) := by
    intro r s n
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (ULift.down r)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (ULift.down (s : ULift.{1} (ZMod q)))
    have hr : r • n = a • n := by
      rw [show r = ((a : ℤ) : ULift.{1} (ZMod Q)) from ULift.ext (by simp [ha]), Int.cast_smul_eq_zsmul]
    change g (ZMod.castHom hq (ZMod q) (ULift.down r) * ULift.down (s : ULift.{1} (ZMod q))) n =
      g (ULift.down (s : ULift.{1} (ZMod q))) (r • n)
    rw [hr, ← ha, ← hb, map_intCast, ← Int.cast_mul, ZMod.lift_coe, ZMod.lift_coe]
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply,
      map_zsmul, mul_comm a b, mul_zsmul]
    exact smul_comm b a _
  let one : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))) :=
    (1 : ULift.{1} (ZMod q))
  have e : f one y = 0 :=
    (TensorProduct.liftAddHom_tmul f hf one y).symm.trans ((congrArg (TensorProduct.liftAddHom f hf) h).trans (map_zero _))
  have e1 : f one = QuotientAddGroup.mk' K := by
    change g ((1 : ZMod q)) = _
    rw [← Int.cast_one, ZMod.lift_coe]
    simp [gZ]
  rw [e1, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at e
  obtain ⟨z, hz⟩ := e
  exact ⟨z, hz.symm⟩

theorem extSh_sec_eq_zero_loc : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U),
    extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q _ hq M U x hx
  have hloc := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).2.1 U
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app (M.obj.obj (op U))).hom x) hx
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ hloc ?_
  intro V g hg
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.naturality (M.obj.map g.op)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) x
  exact unit_eq_zero_dvd hq (M.obj.obj (op V)) (Sec.res g x) (h2.trans hg)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmul
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped ChangeOfRings

namespace GlobalTheory.EtC.ExtOnto

theorem unit_surjective {R S : Type 1} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (N : ModuleCat.{1} R) (z : (ModuleCat.extendScalars.{1,1,1} f).obj N) :
    ∃ m : N, ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f).unit.app N).hom m = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • m, ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.unit_app, map_smul, ModuleCat.restrictScalars.smul_def]
    exact (ModuleCat.ExtendScalars.smul_tmul (M := N) f (f r) 1 m).trans
      (congrArg (fun t : S => t ⊗ₜ[R,f] m) (mul_one _))
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), ha, hb]; rfl⟩

theorem uliftHom_surjective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (uliftHom φ) := by
  intro s
  obtain ⟨r, hr⟩ := hφ s.down
  exact ⟨⟨r⟩, ULift.ext hr⟩

theorem ext_onto : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0})
    (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U),
    Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  intro Q q _ hq M U y
  have hs := uliftHom_surjective (ZMod.castHom hq (ZMod q)) (ZMod.ringHom_surjective _)
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q)
    (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).1 U y
  refine GlobalTheory.EtC.loc_calculus.2.1 _ _ _ h1 ?_
  rintro V g ⟨z, hz⟩
  obtain ⟨m, hm⟩ := unit_surjective _ hs (M.obj.obj (op V)) z
  refine ⟨m, ?_⟩
  subst hm
  exact hz

end GlobalTheory.EtC.ExtOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocally
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exactIff_loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem exactIff_map_comp {R : Type} [CommRing R] {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem exactIff_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun m => m.hom x) (φ.hom.naturality g.op)
  simpa using this

theorem exactIff_kernel_sec {R : Type} [CommRing R] {G K : Shv R} (ψ : G ⟶ K) {U : Scheme.{0}}
    (b : Sec G U) (hb : Sec.map ψ b = 0) : ∃ k : Sec (kernel ψ) U, Sec.map (kernel.ι ψ) k = b := by
  let Φ : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
    sheafToPresheaf Scheme.etaleTopology _ ⋙ (evaluation _ _).obj (op U)
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel ψ)
  have hTm : Mono T.f := inferInstanceAs (Mono (kernel.ι ψ))
  have hP : PreservesLimit (parallelPair T.g 0) Φ := inferInstanceAs (PreservesLimit (parallelPair ψ 0) Φ)
  have h2 := (ShortComplex.moduleCat_exact_iff _).1 (hT.map_of_mono_of_preservesKernel Φ hTm hP) b hb
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, hk⟩

theorem exactIff : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  intro R _ S
  have hME : ∀ {F G : Shv R} (φ : F ⟶ G), _ := fun {F G} φ => GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R φ
  rw [ShortComplex.exact_iff_epi_kernel_lift, (hME (kernel.lift S.g S.f S.zero)).2.2.1]
  have hinj : ∀ U, Function.Injective (Sec.map (kernel.ι S.g) (U := U)) :=
    ((hME (kernel.ι S.g)).1).1 inferInstance
  have hfac : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := fun a => by
    rw [← exactIff_map_comp, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := exactIff_kernel_sec S.g b hb
    refine exactIff_loc_mono (h U k) fun V g ⟨a, ha⟩ => ⟨a, ?_⟩
    rw [← hfac, ha, exactIff_map_res]
  · intro h U k
    have hk : Sec.map S.g (Sec.map (kernel.ι S.g) k) = 0 := by
      rw [← exactIff_map_comp, kernel.condition]; rfl
    refine exactIff_loc_mono (h U _ hk) fun V g ⟨a, ha⟩ => ⟨a, hinj V ?_⟩
    rw [hfac, ha, exactIff_map_res]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCofan

theorem comm_el {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) : φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  have := ConcreteCategory.congr_hom (φ.comm i j) x
  simp only [ConcreteCategory.comp_apply] at this
  exact this.symm

theorem cochains_bij (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E)
    (hc : ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k)))))
    (n : ℤ) : Function.Bijective (fun (x : ((HC R F).obj (op E)).X n) (i : ι) => ((HC R F).map (a i).op).f n x) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  have nat : ∀ (k : ℕ) (i : ι) (x : ((HC R F).obj (op E)).X n),
      (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) =
        (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x := by
    intro k i x
    have := ConcreteCategory.congr_hom ((π k).naturality (a i).op) x
    exact this
  let hk := fun k : ℕ => (hc (op (SimplexCategory.mk k))).some
  constructor
  · intro x y hxy
    apply (hπ (op E)).1
    funext k
    apply Cofan.IsColimit.hom_ext (hk k)
    intro i
    have h : ((HC R F).map (a i).op).f n x = ((HC R F).map (a i).op).f n y := congrFun hxy i
    change (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x =
      (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) y
    rw [← nat, ← nat, h]
  · intro y
    obtain ⟨x, hx⟩ := (hπ (op E)).2 (fun k => Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)))
    refine ⟨x, funext fun i => ?_⟩
    apply (hπ (op (Q i))).1
    funext k
    have e : (π k).app (op E) x = Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)) := congrFun hx k
    show (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) = (π k).app (op (Q i)) (y i)
    rw [nat, e]
    exact Cofan.IsColimit.fac (hk k) _ i

end GlobalTheory.EtC.HCofan

theorem GlobalTheory.EtC.HCofan.main : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  intro R _ F E ι Q a hc n
  obtain ⟨-, cl, hsurj, heq, -, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  have hb := fun m => GlobalTheory.EtC.HCofan.cochains_bij R F E ι Q a hc m
  constructor
  · intro x x' hxx
    obtain ⟨z, hz, rfl⟩ := hsurj E n x
    obtain ⟨z', hz', rfl⟩ := hsurj E n x'
    rw [heq]
    have hi : ∀ i, ∃ y, ((HC R F).map (a i).op).f n z =
        ((HC R F).map (a i).op).f n z' + ((HC R F).obj (op (Q i))).d (n - 1) n y := by
      intro i
      have h : pull R (a i) F n (cl E n z hz) = pull R (a i) F n (cl E n z' hz') := congrFun hxx i
      obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n z hz
      obtain ⟨h2, e2⟩ := hpull (Q i) E (a i) n z' hz'
      rw [e1, e2] at h
      exact (heq _ _ _ h1 _ h2).1 h
    choose y hy using hi
    obtain ⟨w, hw⟩ := (hb (n - 1)).2 y
    have hw' : ∀ i, ((HC R F).map (a i).op).f (n - 1) w = y i := fun i => congrFun hw i
    refine ⟨w, (hb n).1 (funext fun i => ?_)⟩
    show ((HC R F).map (a i).op).f n z = ((HC R F).map (a i).op).f n (z' + ((HC R F).obj (op E)).d (n - 1) n w)
    rw [map_add (f := _), GlobalTheory.EtC.HCofan.comm_el, hw' i]
    exact hy i
  · intro x
    choose z hz hzx using fun i => hsurj (Q i) n (x i)
    obtain ⟨w, hw⟩ := (hb n).2 z
    have hw' : ∀ i, ((HC R F).map (a i).op).f n w = z i := fun i => congrFun hw i
    have hdw : ((HC R F).obj (op E)).d n (n + 1) w = 0 := by
      apply (hb (n + 1)).1
      funext i
      show ((HC R F).map (a i).op).f (n + 1) (((HC R F).obj (op E)).d n (n + 1) w) = ((HC R F).map (a i).op).f (n + 1) 0
      rw [GlobalTheory.EtC.HCofan.comm_el, hw' i, hz i, map_zero]
    refine ⟨cl E n w hdw, funext fun i => ?_⟩
    obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n w hdw
    show pull R (a i) F n (cl E n w hdw) = x i
    rw [e1, ← hzx i]
    exact (heq _ _ _ h1 _ (hz i)).2 ⟨0, by rw [hw' i, map_zero, add_zero]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.PrHomotopy

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  simp [Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma aw_zero_eq_wa_zero : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]


open Classical in
noncomputable def step (N : ℕ) (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ :=
  if H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c then H.choose else 0

noncomputable def hom : ∀ N, Pr N →₀ ℤ
  | 0 => 0
  | N + 1 => step N (hom N)

lemma step_spec (N : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (N + 1) c)
    (hd : Pr.bd (Pr.d N c) = Pr.bd (Pr.aw N - Pr.wa N)) :
    Pr.Deg (N + 2) (step N c) ∧ Pr.d (N + 1) (step N c) = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
  obtain ⟨-, -, -, hbdeg, -, hdbd, haw⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
  have H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
    apply GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N
    · exact deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)
    · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.EtC.AWChain.aw_wa_chain N
      rw [map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]
  unfold step
  rw [dite_eq_left H]
  exact H.choose_spec

lemma hom_spec (N : ℕ) : Pr.Deg (N + 1) (hom N) ∧ Pr.bd (Pr.d N (hom N)) = Pr.bd (Pr.aw N - Pr.wa N) := by
  induction N with
  | zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩
  | succ N ih =>
    obtain ⟨h1, h2⟩ := step_spec N (hom N) ih.1 ih.2
    obtain ⟨-, -, -, -, hbb, -, -⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
    refine ⟨h1, ?_⟩
    show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _
    rw [h2, bd_sub, hbb, sub_zero]

end GlobalTheory.EtC.PrHomotopy

theorem GlobalTheory.EtC.pr_aw_wa_homotopy :
    ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
      ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  refine ⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩
  · simp [PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]
  · have := (PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2
    show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _
    rw [this, sub_add_cancel]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetractionStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_fittingDatum_retraction : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (exact GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetractionStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closureBaseChange_maps_and_retraction : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] (f : A →+* A₁), Function.Injective f →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (S : Type) [CommRing S] [Algebra R₁ S],
    letI := closureAlg A R DA
    letI : Algebra R S := ((algebraMap R₁ S).comp κ).toAlgebra
    letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
    ∃ (φ : S ⊗[R] closure A R DA →ₐ[S] S ⊗[R₁] BC β DA)
      (ψ : S ⊗[R₁] BC β DA →ₐ[S] Localization (Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA)
          ((nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁))))),
      ψ.comp φ = IsScalarTower.toAlgHom S _ _ ∧
      (∀ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        IsUnit (algebraMap S (S ⊗[R₁] BC β DA) m)) ∧
      ∀ x : S ⊗[R₁] BC β DA, ∃ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        x * algebraMap S _ m ∈ φ.range := by
  first | (exact @GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (exact GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (intros; apply GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLiftStatement
section
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | exact GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | (intros; apply GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift <;> assumption)
end

