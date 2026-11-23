module

public import Development.EtaleCohomology.KummerTheory.FinalTheorems
public import Development.EtaleCohomology.KummerTheory.Bundle0002
public import Development.EtaleCohomology.KummerTheory.Bundle0003
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0011

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.ConeCxPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def shvHomOf {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F G : SlShv Λ S)
    (f : ∀ U : Over S, F.obj.obj (op U) →ₗ[ULift.{1} Λ] G.obj.obj (op U))
    (hf : ∀ (V U : Over S) (g : V ⟶ U) x, f V ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom (f U x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom (f U.unop)
     naturality := by intro U V g; ext x; exact hf V.unop U.unop g.unop x }⟩

lemma sec_sub {Λ : Type} [CommRing Λ] {F : Shv Λ} (hF : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor
  intro a b
  have h := hF.eq_of_src (𝟙 F) 0
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, h]
  rfl

lemma isZero_of_sub {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F : SlShv Λ S)
    (h : ∀ U : Over S, Subsingleton (F.obj.obj (op U))) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

theorem coneCx_of (h1 : ConeObj) (h2 : ConeAlg) : ConeCx := by
  intro Λ _ I J K μ hJ hK X S p r M γ hγ
  choose T hT e he using fun j : ℤ => h1 Λ J K hJ.1 hK.1 p r M j
  have hA := fun j : ℤ => h2 Λ μ p r M γ hγ j (j + 1) rfl
  let D : ∀ (j : ℤ) (U : Over S), (T j).obj.obj (op U) →ₗ[ULift.{1} Λ] (T (j + 1)).obj.obj (op U) :=
    fun j U => (e (j + 1) U).symm.toLinearMap ∘ₗ IsLinearMap.mk' _ (hA j U).1 ∘ₗ (e j U).toLinearMap
  have hD : ∀ (j : ℤ) (U : Over S) x, e (j + 1) U (D j U x) = cD μ p γ j (j + 1) rfl U (e j U x) := by
    intro j U x
    simp [D]
  let d : ∀ j : ℤ, T j ⟶ T (j + 1) := fun j => shvHomOf (T j) (T (j + 1)) (D j) (by
    intro V U g x
    refine (e (j + 1) V).injective ?_
    rw [hD, he, he, hD, ((hA j U).2.2 V g).2.1])
  have sq : ∀ j : ℤ, d j ≫ d (j + 1) = 0 := by
    intro j
    ext U x
    change D (j + 1) U.unop (D j U.unop x) = 0
    refine (e (j + 1 + 1) U.unop).injective ?_
    rw [hD, hD, (hA j U.unop).2.1, map_zero]
  refine ⟨CochainComplex.of T d sq, fun j => hT j, ?_, fun j U => (e j U).toAddEquiv, fun j V U g x => he j V U g x, ?_⟩
  · intro j hj
    apply isZero_of_sub
    intro U
    have : Subsingleton (Cone J K p r M j U) := by
      have h3 : ∀ (a : Fin (M + 1)) (s : Fin (r a)), Subsingleton (Sec (J.X (j + 1 - ((a : ℕ) : ℤ))) U.left) :=
        fun a s => sec_sub (hJ.2 _ (by omega)) _
      have h4 : Subsingleton (Sec (K.X j) (pullback p U.hom)) := sec_sub (hK.2 _ (by omega)) _
      constructor
      intro x y
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext a s
      exact (h3 a s).elim _ _
    exact (e j U).injective.subsingleton
  · intro j j' h U x
    subst h
    have hd : (CochainComplex.of T d sq).d j (j + 1) = d j := CochainComplex.of_d _ _ _
    rw [hd]
    exact hD j U x

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.ConeObjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem sym_tot {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫ (tot p).map g := by
  change rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫
    pullback.lift (pullback.fst V.hom p ≫ g.left) (pullback.snd V.hom p)
      (by rw [Category.assoc, Over.w g]; exact pullback.condition)
  apply pullback.hom_ext <;> simp only [rst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]; simp only [pullback.map]; erw [pullback.lift_snd]
  · erw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]; simp only [pullback.map, Category.comp_id]; erw [pullback.lift_fst]

def prodSec {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    (∏ᶜ G).obj.obj (op U) →ₗ[ULift.{1} Λ] (∀ i, (G i).obj.obj (op U)) :=
  LinearMap.pi fun i => ((Pi.π G i).hom.app (op U)).hom

theorem prodSec_bij {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    Function.Bijective (prodSec G U) := by
  let F : SlShv Λ S ⥤ ModuleCat.{1} (ULift.{1} Λ) := sheafToPresheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) ⋙
    (evaluation (Over S)ᵒᵖ (ModuleCat.{1} (ULift.{1} Λ))).obj (op U)
  let e := PreservesProduct.iso F G ≪≫ ModuleCat.piIsoPi.{1, 1, 0} (fun i => F.obj (G i))
  have : ∀ x, prodSec G U x = e.hom x := by
    intro x; funext i
    have h := congrArg (fun φ => φ.hom x) (congrArg (fun ψ => (PreservesProduct.iso F G).hom ≫ ψ)
      (ModuleCat.piIsoPi_hom_ker_subtype.{1, 1, 0} (fun i => F.obj (G i)) i))
    simp only [← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π] at h
    exact h.symm
  have hb : Function.Bijective e.hom := e.toLinearEquiv.bijective
  have h2 : (prodSec G U : _ → _) = fun x => e.hom x := funext this
  rw [h2]; exact hb

theorem coneObj_of (h : InjSlice) : ConeObj := by
  intro Λ _ J K hJ hK X S p r M j
  let σ := Σ a : Fin (M + 1), Fin (r a)
  have hs : ∀ a : Fin (M + 1), ∃ hh : Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      ((Over.forget S).op ⋙ (J.X (j + 1 - ((a : ℕ) : ℤ))).obj),
      Injective (⟨_, hh⟩ : SlShv Λ S) := fun a => (h Λ (J.X _) p).2
  obtain ⟨hk, ik⟩ := (h Λ (K.X j) p).1
  let G : ULift.{1} (Option σ) → SlShv Λ S := fun o => match o.down with
    | none => ⟨_, hk⟩
    | some ⟨a, _⟩ => ⟨_, (hs a).choose⟩
  have hG : ∀ o, Injective (G o) := by
    rintro ⟨o⟩; rcases o with _ | ⟨a, s⟩
    · exact ik
    · exact (hs a).choose_spec
  refine ⟨∏ᶜ G, inferInstance, ?_⟩
  let sy : ∀ U : Over S, (K.X j).obj.obj (op ((tot p).obj U)) ≃ₗ[ULift.{1} Λ] Sec (K.X j) (pullback p U.hom) :=
    fun U => ((K.X j).obj.mapIso (pullbackSymmetry p U.hom).op).toLinearEquiv
  let f2 : ∀ U : Over S, (∀ o, (G o).obj.obj (op U)) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U := fun U =>
    { toFun := fun x => (fun a s => x ⟨some ⟨a, s⟩⟩, sy U (x ⟨none⟩))
      invFun := fun y o => match o with
        | ⟨none⟩ => (sy U).symm y.2
        | ⟨some ⟨a, s⟩⟩ => y.1 a s
      map_add' := fun x y => Prod.ext rfl ((sy U).map_add _ _)
      map_smul' := fun c x => Prod.ext rfl ((sy U).map_smul _ _)
      left_inv := by
        intro x; funext o; rcases o with ⟨_ | ⟨a, s⟩⟩
        · exact (sy U).symm_apply_apply _
        · rfl
      right_inv := by
        intro y; ext a s
        · rfl
        · exact (sy U).apply_symm_apply _ }
  refine ⟨fun U => (LinearEquiv.ofBijective (prodSec G U) (prodSec_bij G U)).trans (f2 U), ?_⟩
  intro V U g x
  have nat : ∀ o, ((Pi.π G o).hom.app (op V)).hom (((∏ᶜ G).obj.map g.op).hom x) =
      ((G o).obj.map g.op).hom (((Pi.π G o).hom.app (op U)).hom x) := fun o => by
    have := congrArg (fun φ => φ.hom x) ((Pi.π G o).hom.naturality g.op)
    simpa using this
  refine Prod.ext ?_ ?_
  · funext a s; exact nat ⟨some ⟨a, s⟩⟩
  · change (sy V) (((Pi.π G ⟨none⟩).hom.app (op V)).hom _) = Sec.res (rst p g) ((sy U) _)
    rw [nat ⟨none⟩]
    have key : (K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom =
        (K.X j).obj.map ((pullbackSymmetry p U.hom).op.hom ≫ (rst p g).op) := by
      refine ((K.X j).obj.map_comp _ _).symm.trans ?_; congr 1; apply Quiver.Hom.unop_inj
      simp only [unop_comp, Iso.op_hom, Quiver.Hom.unop_op, Functor.op_map]
      exact (sym_tot p g).symm
    change ((K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom).hom
      (((Pi.π G ⟨none⟩).hom.app (op U)).hom x) = _
    rw [key, (K.X j).obj.map_comp]; rfl

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DerDictPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DerDictPf

def hc {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C} (i : X ≅ X') (j : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { i.homCongr j with map_add' := fun f g => by simp [Iso.homCongr_apply] }

lemma zcomp_ofHom {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {n : ℤ}
    (c : Cocycle K L n) (g : L ⟶ M) : zcomp c (Cocycle.ofHom g) (add_zero n) = c.postcomp g := by
  ext p q hpq
  simp [zcomp, Cocycle.postcomp]

section
variable (R : Type) [CommRing R] [HasDerivedCategory (Shv R)]

def isoL (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) : DerivedCategory.Q.obj (res R F) ≅ (DerivedCategory.singleFunctor (Shv R) 0).obj F :=
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  (asIso (DerivedCategory.Q.map (resAug F))).symm ≪≫ (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).symm.app F

lemma isoL_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) :
    DerivedCategory.Q.map (resMap R φ) ≫ (isoL R hres G).hom =
      (isoL R hres F).hom ≫ (DerivedCategory.singleFunctor (Shv R) 0).map φ := by
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  haveI : IsIso (DerivedCategory.Q.map (resAug G)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug G)).2 (hres R G).2.2.2.1
  have h1 := congrArg DerivedCategory.Q.map (((hres R F).2.2.2.2.2.2.2 G φ).1)
  simp only [Functor.map_comp] at h1
  have h2 := (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).inv.naturality φ
  simp only [isoL, Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom]
  rw [Category.assoc, IsIso.eq_inv_comp, ← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc]
  exact h2

def jIso (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) (n : ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Shv R) _).obj ((res R F)⟦n⟧)) ≅
      ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧ :=
  (DerivedCategory.quotientCompQhIso (Shv R)).app _ ≪≫ (DerivedCategory.Q.commShiftIso n).app (res R F) ≪≫
    (CategoryTheory.shiftFunctor _ n).mapIso (isoL R hres F)

lemma jIso_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map ((resMap R φ)⟦n⟧')) ≫ (jIso R hres G n).hom =
      (jIso R hres F n).hom ≫ ((DerivedCategory.singleFunctor (Shv R) 0).map φ)⟦n⟧' := by
  have h1 := (DerivedCategory.quotientCompQhIso (Shv R)).hom.naturality ((resMap R φ)⟦n⟧')
  have h2 := (DerivedCategory.Q.commShiftIso n).hom.naturality (resMap R φ)
  have h3 := congrArg (fun f => f⟦n⟧') (isoL_nat R hres φ)
  simp only [Functor.map_comp] at h3
  simp only [jIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.comp_map] at h1 h2
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (DerivedCategory.Q.map _), h2, Category.assoc, h3,
    Category.assoc]
  simp only [Category.assoc]

def dict (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) :
    HK R K F n ≃+ (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧) :=
  haveI := (hres R F).1
  (CohomologyClass.homAddEquiv).trans <|
    (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKInjective.Qh_map_bijective _ ((res R F)⟦n⟧))).trans <|
    hc ((DerivedCategory.quotientCompQhIso (Shv R)).app K) (jIso R hres F n)

lemma dict_mk (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) (c : Cocycle K (res R F) n) :
    dict R hres K F n (CohomologyClass.mk c) =
      (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫
          (jIso R hres F n).hom := by
  simp [dict, hc, Iso.homCongr_apply, CohomologyClass.toHom_mk]; rfl

end

theorem DerDict_of (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : LateralTheory.KummerTheory.BockCut.DerDict := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  refine ⟨dict R hres K, ?_⟩
  intro F G φ n x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  have hp : HK.post R K φ n (CohomologyClass.mk c) = CohomologyClass.mk (c.postcomp (resMap R φ)) := by
    rw [← zcomp_ofHom]; rfl
  rw [hp, dict_mk, dict_mk, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t => (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫ t)
    (jIso_nat R hres φ n)

end LateralTheory.KummerTheory.DerDictPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DictExistPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DE
variable {R : Type} [CommRing R] {I : Cx R} {X : Scheme.{0}} {n : ℤ}

def eta (a : Sec (I.X n) X) : (freeP R).obj (yoneda.obj X) ⟶ (I.X n).obj where
  app U := ModuleCat.freeDesc (↾fun y : ULift.{1} (U.unop ⟶ X) => ((I.X n).obj.map y.down.op).hom a)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    erw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl

theorem eta_app (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((eta a).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = Sec.res x a := by
  erw [eta, ModuleCat.freeDesc_apply]
  rfl

def phi (a : Sec (I.X n) X) : (free R).obj (yoneda.obj X) ⟶ I.X n :=
  ⟨sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property⟩

theorem phi_gen (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    Sec.map (phi a) (freeGen R (yoneda.obj X) U x) = Sec.res x a := by
  have key := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.trans (eta_app a U x)

def coch (a : Sec (I.X n) X) : Cochain ((chains R).obj (sch.obj X)) I n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (sch.obj X) 0).hom ≫ phi a) n

theorem coch_zero (a : Sec (I.X n) X) (h : -((0 : ℕ) : ℤ) + n = n) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (R := R) (coch a) 0 n h U x = Sec.res x a := by
  change Sec.map ((chainsXIso R _ 0).inv ≫ (coch a).v _ _ h) (freeGen R ((sch.obj X).obj (op (SimplexCategory.mk 0))) U x) = _
  rw [coch, Cochain.single_v]
  erw [Iso.inv_hom_id_assoc]
  exact phi_gen a U x

theorem coch_succ (a : Sec (I.X n) X) (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx (sch.obj X) (p + 1) U) : ev (R := R) (coch a) (p + 1) s h U x = 0 := by
  rw [AW.ev_eq, coch, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero]
  rfl

theorem ev_zero_cochain {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem coch_delta (a : Sec (I.X n) X) (ha : Sec.map (I.d n (n + 1)) a = 0) : δ n (n + 1) (coch a) = 0 := by
  apply AW.ev_ext
  intro p s h U x
  rw [ev_zero_cochain]
  rcases p with _ | p
  · obtain rfl : s = n + 1 := by omega
    rw [AW.ev_delta_zero rfl (coch a) n (n + 1) (by simp) h U x, coch_zero a (by simp) U x]
    have e := AW.sec_map_res (I.d n (n + 1)) (show U ⟶ X from x) a
    rw [ha] at e
    exact e.symm.trans (LinearMap.map_zero _)
  · rw [AW.ev_delta_succ rfl (coch a) p (-((p + 1 : ℕ) : ℤ) + n) s rfl h U x, coch_succ]
    rw [show Sec.map (I.d (-((p + 1 : ℕ) : ℤ) + n) s) (0 : Sec (I.X (-((p + 1 : ℕ) : ℤ) + n)) U) = 0 from LinearMap.map_zero _, zero_add]
    rcases p with _ | p
    · have hs : n = s := by omega
      subst hs
      rw [Fin.sum_univ_two]
      have e : ∀ i : Fin 2, ev (R := R) (coch a) 0 n (by omega) U (x.face i) =
          Sec.res (show U ⟶ X from x) a := fun i => coch_zero a _ U _
      rw [e 0, e 1]
      simp
    · simp only [coch_succ, smul_zero, Finset.sum_const_zero]

theorem dictExist : DictExist := by
  intro R _ I X n a ha
  refine ⟨⟨coch a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_delta a ha)⟩, ?_, ?_⟩
  · exact (coch_zero a (by simp) X (𝟙 X)).trans (by rw [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl)
  · intro p s h U y
    exact coch_succ a p s h U y

end LateralTheory.KummerTheory.DE

namespace LateralTheory.KummerTheory

theorem DictExist_of : DictExist := DE.dictExist
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DictPfEv
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem ev_add (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev, Cochain.add_v, Preadditive.comp_add]

theorem ev_neg (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (-α) p s h U x = -ev α p s h U x := by
  have h0 : ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← ev_add, neg_add_cancel, h0]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem val_res' (R : Type) [CommRing R] {P : PSh} {F : Shv R} (φ : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : P.obj (op U)) :
    Sec.res g ((φ.hom.app (op U)).hom (freeGen R P U x)) = (φ.hom.app (op V)).hom (freeGen R P V (P.map g.op x)) := by
  have e1 := congrArg (fun (f : ((free R).obj P).obj.obj (op U) ⟶ F.obj.obj (op V)) => f.hom (freeGen R P U x)) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  refine e1.symm.trans (congrArg _ ?_)
  have e2 := congrArg (fun (f : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj P).obj.obj (op V)) => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at e2
  unfold freeGen
  refine e2.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_res (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) :=
  val_res' R _ V U g x

theorem free_gen_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have e := congrArg (fun (φ : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj Q).obj.obj (op U)) =>
    φ.hom (ModuleCat.freeMk (ULift.up x))) (congrArg (fun η => η.app (op U)) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)))
  erw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at e
  unfold freeGen
  refine e.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single

theorem chainsXIso_nat (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) = (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, chainsN, Functor.comp_map, ComplexShape.embeddingDownNat, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  erw [Iso.inv_hom_id_assoc]
  rfl
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_pre (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E)
    (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_nat, Category.assoc]
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom y) (free_gen_map R _ U x)

theorem evLin : EvLin := fun R _ E I n =>
  ⟨fun α β p s h U x => ⟨ev_add R α β p s h U x, ev_neg R α p s h U x⟩,
   fun α p s h V U g x => ev_res R α p s h V U g x,
   fun f α p s h U x => ev_pre R f α p s h U x⟩
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem Dict_of' (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := Dict_of evLin hE hN hZ
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DictZeroPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DZ

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have e := LateralTheory.KummerTheory.AW.ev_add (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rw [add_zero] at e
  simpa using e.symm

end LateralTheory.KummerTheory.DZ

open LateralTheory.KummerTheory.DZ LateralTheory.EtaleFoundations in
theorem LateralTheory.KummerTheory.DictZero_of : LateralTheory.KummerTheory.DictZero := by
  intro R _ I X n α hα
  refine ⟨?_, ?_⟩
  · rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n + 1) rfl α.1 n (n + 1) (by simp) (by simp) X (𝟙 X), Cocycle.δ_eq_zero]
    exact ev_zero' R _ _ _ _ _
  · rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α (n - 1) (by omega)]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 (n - 1) (by simp) X (𝟙 X), ?_⟩
      rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n) (by omega) β (n - 1) n (by simp) (by simp) X (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (a0 X I (n - 1) y) (etaleSimplicialCochain_scheme_section_extension_naturality X I (n - 1) y)
      refine ⟨γ, LateralTheory.KummerTheory.AW.ev_ext _ _ ?_⟩
      intro p s h U x
      cases p with
      | zero =>
        obtain rfl : s = n := by omega
        rw [LateralTheory.KummerTheory.AW.ev_delta_zero (m := s) (by omega) γ (s - 1) s (by simp) h U x, hγ, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        refine (map_res _ _ _).trans ?_
        exact (congrArg (Sec.res _) hy).trans (LateralTheory.KummerTheory.AW.ev_res α.1 0 s _ x (𝟙 X))
      | succ p =>
        rw [hα p s h U x, LateralTheory.KummerTheory.AW.ev_delta_succ (m := n) (by omega) γ p (-((p + 1 : ℕ) : ℤ) + (n - 1)) s rfl h U x]
        simp only [hγ]
        cases p with
        | zero =>
          obtain rfl : s = n - 1 := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
end
end

