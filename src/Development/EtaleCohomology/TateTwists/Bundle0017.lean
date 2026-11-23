module

public import Development.EtaleCohomology.TateTwists.Bundle0010
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0013

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsResolutionHomExistsOfEx
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_ex_hom_ext_of_qis {C : Type*} [Category C] [Abelian C] {K K' L : CochainComplex C ℤ}
    [L.IsKInjective] (s : K ⟶ K') [QuasiIso s] (f : K ⟶ L) :
    ∃ g : K' ⟶ L, Nonempty (Homotopy (s ≫ g) f) := by
  have hL := CochainComplex.IsKInjective.rightOrthogonal L
  rw [← ObjectProperty.isLocal_trW] at hL
  have hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  obtain ⟨g', hg'⟩ := (hL _ hs).2 ((HomotopyCategory.quotient C _).map f)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g'
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using hg'

def EtaleSheafRestrictScalarsFunctorExact : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S),
    PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ)

theorem etaleSheaf_restrictScalars_resolution_hom_exists_of_exact (hE : EtaleSheafRestrictScalarsFunctorExact) : EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  intro R S _ _ φ F
  obtain ⟨h1, h2⟩ := hE R S φ
  let G := restr φ
  have : G.Additive := G.additive_of_preserves_binary_products
  let IS := injectiveResolution F
  let IR := injectiveResolution (G.obj F)
  have : (res R (G.obj F)).IsKInjective := inferInstanceAs IR.cochainComplex.IsKInjective
  have : (res R (G.obj F)).IsStrictlyGE 0 := inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)
  let s := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'
  have : QuasiIso s := inferInstance
  let f0 := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'
  obtain ⟨g, ⟨h⟩⟩ := restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0
  refine ⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩
  have hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1) :=
    G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))
  have key : (s ≫ g).f 0 = f0.f 0 := by
    rw [h.comm 0]
    have e1 : dNext 0 h.hom = 0 := by
      have e : h.hom 1 0 = 0 := hz1.eq_of_src _ _
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]
    have e2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]
    rw [e1, e2, zero_add, zero_add]
  have key2 := congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key
  simp only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2
  have key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0 := by
    refine key2.trans ?_
    have c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 =
        G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv :=
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
    calc _ = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv) ≫ IR.ι'.f 0) := by
          exact congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)
      _ = _ := by
          have aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z),
              G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v := by
            intro A B Y Z e u v
            rw [← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
          exact aux _ _ _
  simp only [resι]
  erw [Functor.map_comp, Category.assoc]
  exact key3

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafTensorComplexExists
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma sec_map_res {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map f (Sec.res g a) = Sec.res g (Sec.map f a) := by
  change ((F.obj.map g.op ≫ f.hom.app (op V)).hom a) = ((f.hom.app (op U) ≫ G.obj.map g.op).hom a)
  rw [f.hom.naturality]

lemma sec_map_dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  change ((I.d i j ≫ I.d j k).hom.app (op U)).hom a = 0
  rw [HomologicalComplex.d_comp_d]; rfl

def etaleTensorPresheafOfComplexes (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  map_comp f g := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]

def dB (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U →ₗ[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩)).compl₁₂
      ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩)).compl₁₂
      LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (dB I J U w p)

lemma dT_pure (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (tensPure s t w h a b) =
      tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b +
      s.negOnePow • tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b) := by
  simp [dT, tensPure, dB, DirectSum.toModule_lof, Units.smul_def, Sec.map]

lemma tensPure_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res g w (tensPure s t w h a b) = tensPure s t w h (Sec.res g a) (Sec.res g b) := by
  simp [Tens.res, tensPure, Sec.res]

lemma tens_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (H : ∀ s t (h : s + t = w) a b, f (tensPure s t w h a b) = g (tensPure s t w h a b)) : f = g := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  exact H p.1.1 p.1.2 p.2 a b

def dP (I J : Cx R) (w : ℤ) : etaleTensorPresheafOfComplexes I J w ⟶ etaleTensorPresheafOfComplexes I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality V U g := by
    ext1
    refine tens_ext fun s t h a b => ?_
    change dT I J U.unop w (Tens.res g.unop w (tensPure s t w h a b)) =
      Tens.res g.unop (w + 1) (dT I J V.unop w (tensPure s t w h a b))
    simp only [tensPure_res, dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_res]

lemma tensPure_zero_left (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (b : Sec (J.X t) U) :
    tensPure (I := I) s t w h 0 b = 0 := by simp [tensPure]

lemma tensPure_zero_right (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) :
    tensPure (J := J) s t w h a 0 = 0 := by simp [tensPure]

lemma tensorDifferential_comp_tensorDifferential (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  apply NatTrans.ext; funext U; apply ModuleCat.hom_ext
  refine tens_ext (M := Tens I J U.unop (w + 1 + 1)) fun s t h a b => ?_
  change dT I J U.unop (w + 1) (dT I J U.unop w (tensPure s t w h a b)) = 0
  simp only [dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_dd, tensPure_zero_left, tensPure_zero_right,
    smul_zero, zero_add, add_zero, Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

end

theorem etale_sheaf_tensor_complex_exists : EtaleSheafTensorComplexExists := by
  intro R _ I J
  let K : Cx R := CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (etaleTensorPresheafOfComplexes I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_tensorDifferential, Functor.map_zero])
  refine ⟨K, fun U w => ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U)).hom, ?_, ?_, ?_, ?_⟩
  · intro V U g w x
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U) ≫ (sheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).map g.op).hom x = _
    rw [← (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).naturality]; rfl
  · intro U s t w h a b
    have hd : K.d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map (dP I J w) := by
      simp [K, CochainComplex.of_d]
    rw [hd]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w) ≫ sheafifyMap Scheme.etaleTopology (dP I J w)).app (op U)).hom (tensPure s t w h a b) = _
    rw [← toSheafify_naturality]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J (w + 1))).app (op U)).hom (dT I J U w (tensPure s t w h a b)) = _
    simp only [dT_pure, Units.smul_def]
    exact (LinearMap.map_add _ _ _).trans (congrArg _ (map_zsmul _ _ _))
  · intro U w y
    obtain h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (U := op U) y
    exact ⟨_, h, fun V g hg => hg⟩
  · intro U w x hx
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx)
    exact ⟨_, h, fun V g hg => (show Tens.res g w x = Tens.res g w 0 from hg).trans (map_zero _)⟩

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsCochainMkOfCompatibleSectio
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}

noncomputable def eta (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (Sx E p U.unop))
    (M := (I.X s).obj.obj U) (TypeCat.ofHom fun (y : ULift.{1} (Sx E p U.unop)) => a p s h U.unop y.down)
  naturality U V f := by
    refine ModuleCat.free_hom_ext (X := ULift.{1} (Sx E p U.unop)) (fun y => ?_)
    have := ha p s h V.unop U.unop f.unop y.down
    simp only [Sec.res, Sx.res, Quiver.Hom.op_unop] at this
    change (ModuleCat.freeDesc (M := (I.X s).obj.obj V)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p V.unop)) => a p s h V.unop z.down))
        ((ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) =>
          ULift.up.{1} ((E.obj (op (SimplexCategory.mk p))).map f z.down)) (ModuleCat.freeMk y)) =
      ((I.X s).obj.map f) (ModuleCat.freeDesc (M := (I.X s).obj.obj U)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) => a p s h U.unop z.down) (ModuleCat.freeMk y))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

noncomputable def mF (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ (I.X s)).symm
    (eta a ha p s h)

lemma mF_gen (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((mF a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology.{0} (eta a ha p s h) (I.X s).property
  have e2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) e
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e2
  exact e2.trans (ModuleCat.freeDesc_apply _ _)

noncomputable def mC (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun i j hij => if hi : i ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-i).toNat).hom ≫ mF a ha (-i).toNat j (by omega)
  else 0

lemma mC_v (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (mC a ha).v _ _ h = (chainsXIso R E p).hom ≫ mF a ha p s h := by
  have key : ∀ (q : ℕ), q = p → ∀ (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ (chainsXIso R E q).hom ≫ mF a ha q s h' =
        (chainsXIso R E p).hom ≫ mF a ha p s h := by
    rintro q rfl e h'
    simp
  rw [mC, Cochain.mk_v, dite_eq_left (by omega)]
  exact key _ (by omega) _ _

end LateralTheory.EtaleFoundations.MkPf

open LateralTheory.EtaleFoundations LateralTheory.EtaleFoundations.MkPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections : EtaleSimplicialCochainExistsFromNaturalSections := by
  intro R _ E I n a ha
  refine ⟨mC a ha, fun p s h U x => ?_⟩
  unfold ev
  rw [mC_v, Iso.inv_hom_id_assoc]
  exact mF_gen a ha p s h U x
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainEvaluationPrecompSpaceMap
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainEvaluationAdditive : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x

def EtaleSimplicialCochainEvaluationRestrictionNaturality : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

def EtaleSimplicialCochainExtOfEvaluation : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β

def EtaleSimplicialCochainEvaluationPrecompSpaceMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)

def EtaleSimplicialCochainEvaluationPostcompComplexMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations.BasicPf
variable {R : Type} [CommRing R]

lemma app_add {A B : Shv R} (φ ψ : A ⟶ B) (U : Scheme.{0}) (y : Sec A U) :
    ((φ + ψ).hom.app (op U)).hom y = (φ.hom.app (op U)).hom y + (ψ.hom.app (op U)).hom y := by
  rfl

noncomputable def evH {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (by
    intro α β
    show ((((chainsXIso R E p).inv ≫ (α + β).v _ _ h).hom.app (op U))).hom _ = _
    rw [Cochain.add_v, Preadditive.comp_add, app_add]
    rfl)

theorem lin : EtaleSimplicialCochainEvaluationAdditive := by
  intro R _ E I n α β p s h U x
  exact ⟨map_add (evH p s h U x) α β, map_sub (evH p s h U x) α β, map_zero (evH p s h U x),
    fun c => map_zsmul (evH p s h U x) c α⟩

theorem cx : EtaleSimplicialCochainEvaluationPostcompComplexMap := by
  intro R _ E I n J m α p s h U x
  show ((((chainsXIso R E p).inv ≫ (α.comp (Cochain.ofHom m) (add_zero n)).v _ _ h).hom.app (op U))).hom _ = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

lemma freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  erw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem nat : EtaleSimplicialCochainEvaluationRestrictionNaturality := by
  intro R _ E I n α p s h V U g x
  show Sec.res g ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom (freeGen R _ U x)) =
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom (freeGen R _ V (x.res g)))
  rw [show x.res g = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← freeGen_res]
  simp only [Sec.res]
  exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R _ U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)).symm

lemma freeGen_map {P Q : PSh} (η : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map η).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (η.app (op U) x) := by
  unfold freeGen
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality, NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem spc : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationPrecompSpaceMap := by
  intro R _ E I n E' f α p s h U x
  have key : (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
    simp only [chains, chainsXIso, Functor.comp_map]
    erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl, Iso.inv_hom_id_assoc]
    rfl
  show ((((chainsXIso R E' p).inv ≫ ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v _ _ h).hom.app (op U))).hom _ = ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U))).hom (freeGen R _ U (x.map f))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, key, Category.assoc]
  show (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom ((((free R).map (f.app (op (SimplexCategory.mk p)))).hom.app (op U)).hom (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ext : LateralTheory.EtaleFoundations.EtaleSimplicialCochainExtOfEvaluation := by
  intro R _ E I n α β hev
  apply Cochain.ext
  intro a b hab
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k:ℤ) := ⟨a.natAbs, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    apply (sheafToPresheaf _ _).map_injective
    apply sheafify_hom_ext _ _ _ (I.X b).property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨y⟩
    exact hev k b hab U.unop y
  · apply (HomologicalComplex.isZero_extend_X _ _ a _).eq_of_src
    intro i hi
    change -(i:ℤ) = a at hi
    omega

end LateralTheory.EtaleFoundations.BasicPf

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components : EtaleSimplicialCochainEvaluationProperties := by
  intro R _ E I n
  exact ⟨BasicPf.lin R, BasicPf.nat R, BasicPf.ext R, BasicPf.spc R, BasicPf.cx R⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSingleSheafHomotopicMapsEqualHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  intro R _ F I _ a b ⟨h⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [h.comm 0]
    have h1 : dNext 0 h.hom = 0 := by
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
      rw [show (sgl F).d 0 1 = 0 from
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]
      simp
    have h2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]
      simp
    rw [h1, h2]; simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapIsIsoOfInjSurj
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (b : Sec T U), Loc U fun V g => ∃ a : Sec (tw q k) V, Sec.map φ a = Sec.res g b

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_isIso_of_inj_surj (hme : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hs : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective) (hi : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso := by
  intro q _ i j k T μ hμ hk φ hφ
  have h := hme (ZMod q) φ
  have hm : Mono φ := h.2.1.2 (hi q i j k T μ hμ hk φ hφ)
  have he : Epi φ := h.2.2.1.2 (hs q i j k T μ hμ hk φ hφ)
  exact isIso_of_mono_of_epi φ
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryPartBasic
section
namespace LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
theorem etale_torsion_cohomology_primary_part_basic : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  apply LateralTheory.EtaleFoundations.PrimPf.cyclotomic_primitive_root_product_identities_of_adjoin_root
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := etale_torsion_cohomology_primary_part_basic
end LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
end

-- bundled from Development.EtaleCohomology.TateTwists.TTwpairExPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
end

