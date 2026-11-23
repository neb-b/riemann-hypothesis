module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ResBasic

variable {C : Type*} [Category C] [Abelian C] {X : C} (I : InjectiveResolution X)

end GlobalTheory.EtC.ResBasic

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private theorem injectiveResolution_cochainComplex_exact_and_exactAt {C : Type*} [Category C] [Abelian C]
    {X : C} (I : InjectiveResolution X) :
    (∀ n : ℤ, Injective (I.cochainComplex.X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero (I.cochainComplex.X n)) ∧
    Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ∧
    (∃ w : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → I.cochainComplex.ExactAt n) := by
  refine ⟨fun n => inferInstance, fun n hn => ?_, ?_, ?_, fun n hn => ?_⟩
  · exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have h : (ComplexShape.embeddingUpNat.f i : ℤ) = i := rfl
      omega)
  · rw [I.ι'_f_zero]
    erw [Iso.inv_hom_id_assoc]
    exact mono_comp (I.ι.f 0) _
  · have hw : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0 := by
      rw [I.ι'_f_zero, I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, I.ι_f_zero_comp_complex_d_assoc, zero_comp]
      rfl
    refine ⟨hw, ?_⟩
    refine (ShortComplex.exact_iff_of_iso ?_).mpr I.exact₀
    refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) ?_ ?_
    · dsimp only
      rw [I.ι'_f_zero]
      erw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc]
    · dsimp only
      rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp
  · exact (quasiIsoAt_iff_exactAt I.ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)).mp
      inferInstance


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.res_basic : ∀ (R : Type) [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R), (∀ n : ℤ, Injective ((_root_.GlobalTheory.EtC.res R F).X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((_root_.GlobalTheory.EtC.res R F).X n)) ∧ Mono (_root_.GlobalTheory.EtC.resι R F) ∧
    (∃ w : _root_.GlobalTheory.EtC.resι R F ≫ (_root_.GlobalTheory.EtC.res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → (_root_.GlobalTheory.EtC.res R F).ExactAt n) ∧
    ∀ (E : _root_.GlobalTheory.EtC.Spc) (n : ℤ), 0 < n → IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X n) := by
  intro R _ F
  unfold _root_.GlobalTheory.EtC.res _root_.GlobalTheory.EtC.resι _root_.GlobalTheory.EtC.chains
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := injectiveResolution_cochainComplex_exact_and_exactAt (injectiveResolution F)
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun E n hn => ?_⟩
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    have h : (ComplexShape.embeddingDownNat.f i : ℤ) = -i := rfl
    omega)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cocycle_comp_assoc_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  intro R _ K L M N a b c ab bc abc h1 h2 h3 h4
  have hA : a + b + c = abc := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [cpre_mk, cpre_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [cpre_mk, cpost_mk, cpost_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpost_mk, cpost_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ShiftCocycle

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K L n →+ CohomologyClass K (L⟦a⟧) n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K (L⟦a⟧) n').comp (Cocycle.rightShiftAddEquiv n a n' h).toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + -a, by omega, a.negOnePow • β.rightShift a (m + -a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightShift β a (m + -a) n' (by omega) n h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

def runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K (L⟦a⟧) n' →+ CohomologyClass K L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K L n).comp (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm.toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + a, by omega, a.negOnePow • β.rightUnshift (m + a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift β (m + a) (by omega) n n' h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem runsh_rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    runsh K L a n n' h (rsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm_apply_apply x

theorem rsh_runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    rsh K L a n n' h (runsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).apply_symm_apply x

def sgn (d : ℤ) : ℤˣ := ((-d) * 0 + ((-d) * (-d - 1)) / 2).negOnePow

theorem zcomp_rightShift_homOf_leftShift {K L M : CochainComplex C ℤ} (d n : ℤ) (α : Cocycle K L (n - d)) (ψ : Cocycle L M d) :
    zcomp (sgn d • α.rightShift (-d) n (by omega)) (Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega))))
      (add_zero n) = zcomp α ψ (by omega) := by
  ext p q hpq
  have e1 : (↑(Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)))) : Cochain (L⟦-d⟧) M 0) =
      (ψ.leftShift (-d) 0 (by omega) : Cochain _ _ 0) := by
    rw [Cocycle.ofHom_coe, Cocycle.cochain_ofHom_homOf_eq_coe]
  simp only [zcomp, Cocycle.mk_coe, e1, Cocycle.coe_units_smul, Cochain.units_smul_comp,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (show n - d + d = n by omega) p (p + (n - d)) q rfl (by omega),
    Cochain.units_smul_v, Cocycle.rightShift_coe, Cocycle.leftShift_coe,
    Cochain.rightShift_v _ (-d) n (show n + -d = n - d by omega) p q hpq (p + (n - d)) rfl,
    Cochain.leftShift_v _ (-d) 0 (show d + -d = 0 by omega) q q (add_zero q) (p + (n - d)) (by omega)]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Category.assoc, Iso.inv_hom_id_assoc]
  have hs : sgn d * (-d * 0 + -d * (-d - 1) / 2).negOnePow = 1 := Int.units_mul_self _
  rw [hs, one_smul]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem smul_mk {K L : CochainComplex C ℤ} {n : ℤ} (u : ℤˣ) (z : Cocycle K L n) :
    CohomologyClass.mk (u • z) = u • CohomologyClass.mk z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, CohomologyClass.mk_neg]

theorem smul_smul_self {G : Type*} [AddCommGroup G] (u : ℤˣ) (x : G) : u • u • x = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

theorem map_units_smul' {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (u : ℤˣ) (x : G) :
    f (u • x) = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC

open ShiftCocycle in
theorem cocycle_as_chainMap_of_shift : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d),
    ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧
      ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧
      ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n,
        ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  intro R _ L C d ψ
  refine ⟨L⟦-d⟧, Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)), ?_, ?_, ?_⟩
  · intro m hm
    exact L.isStrictlyGE_shift m (-d) (m + d) (by omega)
  · intro hI n
    exact Injective.of_iso (L.shiftFunctorObjXIso (-d) n (n + -d) rfl).symm (hI _)
  · intro K n
    refine ⟨{ toFun := fun x => sgn d • rsh K L (-d) (n - d) n (by omega) x
              invFun := fun y => sgn d • runsh K L (-d) (n - d) n (by omega) y
              left_inv := fun x => by
                simp only [map_units_smul', runsh_rsh, smul_smul_self]
              right_inv := fun y => by
                simp only [map_units_smul', rsh_runsh, smul_smul_self] }, ?_⟩
    intro a
    obtain ⟨α, rfl⟩ := a.mk_surjective
    show cpush K _ n (sgn d • CohomologyClass.mk (α.rightShift (-d) n (by omega))) = _
    rw [← smul_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (zcomp_rightShift_homOf_leftShift d n α ψ)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCElements

theorem chains_X_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) :=
  ((chainsN R).obj E).isZero_extend_X ComplexShape.embeddingDownNat n (fun i hi => by
    change -(i : ℤ) = n at hi; omega)

theorem res_X_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  intro R _ F
  have zero_iff : ∀ (E : Spc) (n : ℤ) (c : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk c = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), (show ((HC R F).obj (op E)).X n from c.1) = ((HC R F).obj (op E)).d (n - 1) n y := by
    intro E n c
    rw [CohomologyClass.mk_eq_zero_iff]
    constructor
    · rintro ⟨m, hm, β, hβ⟩
      obtain rfl : m = n - 1 := by omega
      exact ⟨β, hβ.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨n - 1, by omega, y, hy.symm⟩
  refine ⟨?_, fun E n z hz => CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz), ?_, ?_, ?_, ?_⟩
  · intro E n hn
    refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => ?_⟩
    change Cochain ((chains R).obj E.unop) (res R F) n at a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : 0 < p
    · exact (chains_X_isZero R E.unop p hp).eq_of_src _ _
    · exact (res_X_isZero R F q (by omega)).eq_of_tgt _ _
  · intro E n x
    obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c.1, c.2, rfl⟩
  · intro E n z hz z' hz'
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _ at hy
      rw [← hy]; abel
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _
      rw [hy]; abel
  · intro E n z hz
    exact zero_iff E n _
  · intro E E' f n z hz
    refine ⟨(zcomp (Cocycle.ofHom ((chains R).map f)) (Cocycle.mk z (n + 1) rfl hz) (zero_add n)).2, ?_⟩
    rfl

end GlobalTheory.EtC.HCElements
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwist
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem mem_coinv_of_finset_sum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by
  set H : GL (Fin a) k → Matrix (Fin a) (Fin (a + b)) k → ℂ :=
    fun r Y => χ Y * (tw ν (a + b) r * Φ (r.val * Y)) with hH
  have hHSB : ∀ r, H r ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
    intro r
    have hs : (fun Y => Φ (r.val * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
      have := comp_mul_mem_SB r 1 hΦ
      simp only [Units.val_one, Matrix.mul_one] at this
      exact this
    obtain ⟨hs1, hs2⟩ := hs
    have e : H r = χ * ((fun _ => tw ν (a + b) r) * fun Y => Φ (r.val * Y)) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · exact hχ.mul ((IsLocallyConstant.const _).mul hs1)
    · exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hs2)
  have hom : ∀ r, omA ν β r 1 (H r) = fun Y => χ ((r⁻¹).val * Y) * Φ Y := by
    intro r
    funext Y
    rw [omA_one_apply]
    simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    field_simp [tw_ne_zero ν (a + b) r]
  have hsumH : ∑ r ∈ R, H r = 0 := by
    funext Y
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [hH, ← Finset.mul_sum]
    exact h2 Y
  have hΦeq : Φ = ∑ r ∈ R, (omA ν β r 1 (H r) - H r) := by
    rw [Finset.sum_sub_distrib, hsumH, sub_zero]
    funext Y
    rw [Finset.sum_apply]
    simp only [hom]
    exact h1 Y
  rw [hΦeq]
  refine Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨r, H r, hHSB r, rfl⟩

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.ColGramPos

open scoped ComplexOrder

theorem blkW_upper {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i j : Fin (r - 1)) (h : i < j) :
    blkW p0 w i j = 0 := by
  have h' : (i : ℕ) < j := h
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dite_eq_right (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
  · unfold lowMat
    rw [dite_eq_right (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]

theorem blkW_diag {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  · unfold lowMat
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]

theorem lowerTri_det_one {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by
  rw [Matrix.det_of_lowerTriangular T (fun i j hij => hu i j hij)]
  simp [hd]

theorem colGram_blkW_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  intro r p0 w k
  set B := blkW p0 w with hB
  have hk : (k : ℕ) ≤ r - 1 := Nat.le_of_lt_succ k.isLt
  set N : Matrix (Fin (r - 1)) (Fin k) ℂ := B.submatrix id (Fin.castLE hk) with hN
  have hsub : (Bᴴ * B).submatrix (Fin.castLE hk) (Fin.castLE hk) = Nᴴ * N := by
    ext a b
    simp [N, Matrix.mul_apply, Matrix.conjTranspose_apply]
  set T : Matrix (Fin k) (Fin k) ℂ := B.submatrix (Fin.castLE hk) (Fin.castLE hk) with hT
  have hTdet : T.det = 1 := by
    apply lowerTri_det_one
    · intro i j hij
      exact blkW_upper p0 w _ _ (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    · intro i
      exact blkW_diag p0 w _
  have hinj : Function.Injective N.mulVec := by
    intro u v huv
    have h0 : N *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have hT0 : T *ᵥ (u - v) = 0 := by
      ext i
      have := congrFun h0 (Fin.castLE hk i)
      simpa [T, N, Matrix.mulVec, dotProduct] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hTdet]; exact one_ne_zero) hT0
    exact sub_eq_zero.mp this
  have hpd : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hinj
  have hdet : (Nᴴ * N).det ≠ 0 := hpd.det_pos.ne'
  unfold colGram lminor
  rw [hsub]
  exact norm_pos_iff.mpr hdet

end GlobalTheory.IntBall.ColGramPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimitStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finite_baseChange_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
        Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A)) := by
  exact @GlobalTheory.FiniteColim.eventually_finite_baseChange
end

