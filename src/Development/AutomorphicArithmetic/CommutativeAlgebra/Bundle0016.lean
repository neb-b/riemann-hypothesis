module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma scal {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) =
      (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appLE ⊤ W le_top ≫ C.germToFunctionField W =
      CommRingCat.ofHom (algebraMap k C.functionField) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k C.functionField))
  rw [h, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h1
  have hm : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map_id _
  have h2 : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv]
    refine h1.trans ?_
    simp only [Category.assoc]
    erw [hm, Category.comp_id]
  rw [h2]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact C.presheaf.germ_res (homOfLE le_top) (genericPoint C) _

theorem UpperTheory.baseChange_affine_sections_subalgebra_tensor :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsAffineOpen (u ⁻¹ᵁ W) ∧ ∃ e : L ⊗[k] B ≃+* Γ(X, u ⁻¹ᵁ W), (∀ (a : Γ(C, W)) (b : B), (b : C.functionField) = C.germToFunctionField W a → e ((1 : L) ⊗ₜ[k] b) = u.app W a) ∧ ∀ l : L, e (l ⊗ₜ[k] (1 : B)) = x.appLE ⊤ (u ⁻¹ᵁ W) le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) := by
  intro k L _ _ _ C X _ c u x H _ hK W _ hW B hB
  have hu : IsAffineHom u := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine ⟨hW.preimage u, ?_⟩
  let g0 : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hinj : Function.Injective g0 := C.germToFunctionField_injective W
  have hmem : ∀ a, g0 a ∈ B := fun a => by
    have : g0 a ∈ (B : Set C.functionField) := by rw [hB]; exact ⟨a, rfl⟩
    exact this
  let g1 : Γ(C, W) →+* B := g0.codRestrict B hmem
  have hbij : Function.Bijective g1 := by
    refine ⟨fun a a' h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    have : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
    rw [hB] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  let gB : Γ(C, W) ≃+* B := RingEquiv.ofBijective g1 hbij
  let iB : CommRingCat.of B ≅ Γ(C, W) := gB.symm.toCommRingCatIso
  have hP := (GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback H hW).flip
  have hT := CommRingCat.isPushout_tensorProduct k L B
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap k L)) (CommRingCat.ofHom (algebraMap k B))
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appLE ⊤ (u ⁻¹ᵁ W) le_top)
      (iB.hom ≫ u.app W) := by
    refine hP.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) iB.symm (Iso.refl _)
      (Scheme.ΓSpecIso_naturality _) ?_ (by simp) (by simp)
    rw [← Iso.inv_comp_eq]
    ext r
    exact congr($(scal c hK W).hom r)
  let E := IsPushout.isoIsPushout _ _ hT hP'
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro a b hab
    have h1 := congr($(IsPushout.inr_isoIsPushout_hom _ _ hT hP').hom b)
    have h2 : iB.hom b = a := by
      apply hinj
      have h3 := congrArg Subtype.val (gB.apply_symm_apply b)
      exact h3.trans hab
    rw [← h2]
    exact h1
  · intro l
    have h1 := congr($(IsPushout.inl_isoIsPushout_hom _ _ hT hP').hom l)
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeFunctionFieldHomGenericPointComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOfLocallySurjectiveOnCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.ConeLoc

open CochainComplex.mappingCone

private theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W t => P' W (t ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => k V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun V g hg => hT V g hg)
  · rintro W t ⟨V, e, g, hg, he, rfl⟩
    exact hT' V g hg W e he

private theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => k V g (hP V g hg)⟩

section
variable {R : Type} [CommRing R]

private theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

private theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ + ψ) a = Sec.map φ a + Sec.map ψ a := rfl

private theorem sm_sub {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ - ψ) a = Sec.map φ a - Sec.map ψ a := rfl

private theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (-φ) a = - Sec.map φ a := rfl

private theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have hn := φ.hom.naturality g.op
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hn]

private theorem ms_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem ms_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

private theorem ms_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b :=
  map_sub (φ.hom.app (op U)).hom a b

private theorem ms_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a :=
  map_neg (φ.hom.app (op U)).hom a

private theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ a b

private theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (h ≫ g) a = Sec.res h (Sec.res g a) := by
  simp [Sec.res]

end

variable {K M : Cx ℤ} (φ : K ⟶ M)

private theorem fst_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((fst φ).1.v j k hjk) (Sec.map ((mappingCone φ).d i j) s) =
      - Sec.map (K.d j k) (Sec.map ((fst φ).1.v i j hij) s) := by
  rw [← sm_comp, d_fst_v φ i j k hij hjk, sm_neg, sm_comp]

private theorem snd_d (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((snd φ).v j j (add_zero _)) (Sec.map ((mappingCone φ).d i j) s) =
      Sec.map (φ.f j) (Sec.map ((fst φ).1.v i j hij) s) + Sec.map (M.d i j) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  rw [← sm_comp, d_snd_v φ i j hij, sm_add, sm_comp, sm_comp]

private theorem decomp (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    s = Sec.map ((inl φ).v j i (by omega)) (Sec.map ((fst φ).1.v i j hij) s) +
      Sec.map ((inr φ).f i) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  have hid := id_X φ i j hij
  calc s = Sec.map (𝟙 _) s := rfl
    _ = _ := by rw [← hid]; rfl

private theorem d_inl (n : ℤ) {T : Scheme.{0}} (a : Sec (K.X n) T) (ha : Sec.map (K.d n (n + 1)) a = 0) :
    Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) := by
  rw [← sm_comp, inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, ha, ms_zero, sub_zero]

private theorem d_inr (i j : ℤ) {T : Scheme.{0}} (c : Sec (M.X i) T) :
    Sec.map ((mappingCone φ).d i j) (Sec.map ((inr φ).f i) c) = Sec.map ((inr φ).f j) (Sec.map (M.d i j) c) := by
  rw [← sm_comp, inr_f_d, sm_comp]

private theorem core (Q : Scheme.{0} → Prop) (hQ : ∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V)
    (H1 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (M.X n) T), Sec.map (M.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (K.X n) V) (c : Sec (M.X (n - 1)) V), Sec.map (K.d n (n + 1)) a = 0 ∧
        Sec.map (φ.f n) a = Sec.res g b + Sec.map (M.d (n - 1) n) c)
    (H2 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (K.X n) T), Sec.map (K.d n (n + 1)) a = 0 →
      (∃ c : Sec (M.X (n - 1)) T, Sec.map (φ.f n) a = Sec.map (M.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) a' = Sec.res g a)
    (U : Scheme.{0}) (hU : Q U) (n : ℤ) (b : Sec ((mappingCone φ).X n) U)
    (hb : Sec.map ((mappingCone φ).d n (n + 1)) b = 0) :
    Loc U fun V g => ∃ c : Sec ((mappingCone φ).X (n - 1)) V,
      Sec.map ((mappingCone φ).d (n - 1) n) c = Sec.res g b := by
  have hdec := decomp φ n (n + 1) rfl b
  have hfd := fst_d φ n (n + 1) (n + 1 + 1) rfl rfl b
  have hsd := snd_d φ n (n + 1) rfl b
  set x := Sec.map ((fst φ).1.v n (n + 1) rfl) b with hx
  set y := Sec.map ((snd φ).v n n (add_zero n)) b with hy
  have hxd : Sec.map (K.d (n + 1) (n + 1 + 1)) x = 0 := by
    rw [hb, ms_zero] at hfd
    exact neg_eq_zero.mp hfd.symm
  have hxy : Sec.map (φ.f (n + 1)) x + Sec.map (M.d n (n + 1)) y = 0 := by
    rw [hb, ms_zero] at hsd
    exact hsd.symm
  have hyx : Sec.map (M.d n (n + 1)) y + Sec.map (φ.f (n + 1)) x = 0 := (add_comm _ _).trans hxy
  have hcob : ∃ c : Sec (M.X (n + 1 - 1)) U,
      Sec.map (φ.f (n + 1)) x = Sec.map (M.d (n + 1 - 1) (n + 1)) c := by
    refine ⟨Sec.map (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (-y), ?_⟩
    rw [← sm_comp (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (M.d (n + 1 - 1) (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ms_neg]
    exact eq_neg_of_add_eq_zero_left hxy
  apply loc_bind (H2 U hU (n + 1) x hxd hcob)
  rintro V g ⟨a', ha'⟩
  set a := Sec.map (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom a' with ha
  have had : Sec.map (K.d n (n + 1)) a = Sec.res g x := by
    rw [ha, ← sm_comp (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom (K.d n (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ha']
  set y' := Sec.res g y + Sec.map (φ.f n) a with hy'
  have hy'd : Sec.map (M.d n (n + 1)) y' = 0 := by
    rw [hy', ms_add, ← sm_res, ← sm_comp (φ.f n) (M.d n (n + 1)), φ.comm n (n + 1), sm_comp, had,
      ← sm_res, ← res_add, hyx, res_zero]
  have hdc1 : Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) - Sec.map ((inl φ).v (n + 1) n (by omega)) (Sec.res g x) := by
    rw [← sm_comp ((inl φ).v n (n - 1) (by omega)) ((mappingCone φ).d (n - 1) n),
      inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, had]
  apply loc_mono (H1 V (hQ g hU) n y' hy'd)
  rintro W t ⟨a₂, c₂, ha₂, hφ⟩
  refine ⟨Sec.map ((inl φ).v n (n - 1) (by omega)) a₂ - Sec.map ((inr φ).f (n - 1)) c₂ -
    Sec.res t (Sec.map ((inl φ).v n (n - 1) (by omega)) a), ?_⟩
  rw [res_comp, hdec, ms_sub, ms_sub, d_inl φ n a₂ ha₂, d_inr, ← sm_res, hdc1, hφ, hy']
  simp only [sm_res, map_sub, map_add (f := _)]
  abel

end UpperTheory.ConeLoc

theorem UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
            ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec ((mappingCone ρ.toZ).X n) U), Sec.map ((mappingCone ρ.toZ).d n (n + 1)) b = 0 →
          Loc U fun V g => ∃ c : Sec ((mappingCone ρ.toZ).X (n - 1)) V, Sec.map ((mappingCone ρ.toZ).d (n - 1) n) c = Sec.res g b := by
  intro R _ L B ρ Q hQ H1 H2 U hU n b hb
  exact UpperTheory.ConeLoc.core ρ.toZ Q hQ (fun T hT m c hc => H1 T hT m c hc)
    (fun T hT m a ha hc => H2 T hT m a ha hc) U hU n b hb
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteExtPullbackIntegralClosureEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.PullbackAlongInclusion

section
variable (A K L : Type) [CommRing A] [Field K] [Algebra A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

private abbrev Idx : Type := {E : IntermediateField K L // FiniteDimensional K E}

omit [Algebra A K] in
private theorem idx_directed : IsDirected (Idx K L) (· ≤ ·) :=
  ⟨fun a b => by
    haveI := a.2
    haveI := b.2
    exact ⟨⟨a.1 ⊔ b.1, inferInstance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

private noncomputable def incl {E F : IntermediateField K L} (h : E ≤ F) :
    integralClosure A E →ₐ[A] integralClosure A F :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

private noncomputable def toL (E : IntermediateField K L) :
    integralClosure A E →ₐ[A] integralClosure A L :=
  (E.val.restrictScalars A).mapIntegralClosure

private noncomputable def ringD : Idx K L ⥤ CommRingCat.{0} where
  obj E := CommRingCat.of (integralClosure A E.1)
  map f := CommRingCat.ofHom (incl A K L (leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def ringC : Cocone (ringD A K L) where
  pt := CommRingCat.of (integralClosure A L)
  ι := { app := fun E => CommRingCat.ofHom (toL A K L E.1).toRingHom
         naturality := fun _ _ _ => by ext; rfl }

private theorem ringC_isColimit [Algebra.IsAlgebraic K L] : Nonempty (IsColimit (ringC A K L)) := by
  haveI := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := inferInstance
  haveI : ReflectsColimitsOfShape (Idx K L) (forget CommRingCat) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    have hx : IsIntegral K (x.1 : L) := Algebra.IsIntegral.isIntegral _
    let E : Idx K L := ⟨IntermediateField.adjoin K {x.1}, IntermediateField.adjoin.finiteDimensional hx⟩
    have hm : x.1 ∈ E.1 := IntermediateField.mem_adjoin_simple_self K x.1
    have hi : IsIntegral A (⟨x.1, hm⟩ : E.1) :=
      (isIntegral_algHom_iff (E.1.val.restrictScalars A) E.1.val.toRingHom.injective).1 x.2
    exact ⟨E, ⟨⟨x.1, hm⟩, hi⟩, rfl⟩
  · intro a b xa xb h
    haveI := a.2
    haveI := b.2
    refine ⟨⟨a.1 ⊔ b.1, inferInstance⟩, homOfLE (le_sup_left (a := a.1)),
      homOfLE (le_sup_right (b := b.1)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integralClosure A L => (z : L)) h

omit [Algebra A K] [IsScalarTower A K L] [Field K] [Algebra K L] in
private theorem aic [IsAlgClosed L] : AIC (integralClosure A L) := by
  intro p hp hdeg
  have hd : (p.map (algebraMap (integralClosure A L) L)).degree ≠ 0 := by
    rw [hp.degree_map]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral (integralClosure A L) a := ⟨p, hp, by rw [← Polynomial.eval_map]; exact ha⟩
  have hA : IsIntegral A a := isIntegral_trans a hint
  refine ⟨⟨a, hA⟩, ?_⟩
  have h2 : algebraMap (integralClosure A L) L (Polynomial.eval ⟨a, hA⟩ p) = 0 := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact ha
  exact Subtype.ext h2

end

private theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

private theorem pull_of_comp (q : ℕ) (m i : ℤ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (e : g.comp f = h) (x : Ht q (sp R) m i) :
    pull _ (spMap g) _ m (pull _ (spMap f) _ m x) = pull _ (spMap h) _ m x := by
  rw [← pull_comp, spMap_comp, e]

end UpperTheory.PullbackAlongInclusion

open UpperTheory.PullbackAlongInclusion in
theorem UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero :
    Hyps → ∀ (q : ℕ) [NeZero q] (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
        [IsFractionRing A K], IsUnit (q : A) → ∀ (m i : ℤ), 0 < m → ∀ x : Ht q (sp A) m i,
        ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F) (_ : IsScalarTower A K F) (_ : FiniteDimensional K F),
          pull _ (spMap (algebraMap A (integralClosure A F))) _ m x = 0 := by
  intro h q _ A K _ _ _ _ _ hq m i hm x
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB1, -, -, -, hB5, -⟩ := h
  let L := AlgebraicClosure K
  haveI : IsDirected (Idx K L) (· ≤ ·) := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := isFiltered_of_directed_le_nonempty _
  obtain ⟨hc⟩ := ringC_isColimit A K L
  let j0 : Idx K L := ⟨⊥, inferInstance⟩
  have hqE : ∀ E : IntermediateField K L, IsUnit ((q : integralClosure A E)) := fun E => by
    simpa using hq.map (algebraMap A (integralClosure A E))
  have hqL : IsUnit ((q : integralClosure A L)) := by
    simpa using hq.map (algebraMap A (integralClosure A L))
  have e1 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1)) (toL A K L j0.1).toRingHom
    (algebraMap A (integralClosure A L)) (toL A K L j0.1).comp_algebraMap x
  haveI := hB5 q (integralClosure A L) (aic A L) hqL m i hm
  have hzero : pull _ (spMap ((ringC A K L).ι.app j0).hom) _ m
      (pull _ (spMap (algebraMap A (integralClosure A j0.1))) _ m x) = 0 :=
    e1.trans (Subsingleton.elim _ _)
  obtain ⟨k, f, hk⟩ := (hB1 q (ringD A K L) (ringC A K L) hc m i).2 j0 _ (hqE _) hzero
  refine ⟨k.1, inferInstance, inferInstance, inferInstance, inferInstance, k.2, ?_⟩
  have e2 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1))
    (incl A K L (leOfHom f)).toRingHom (algebraMap A (integralClosure A k.1))
    (incl A K L (leOfHom f)).comp_algebraMap x
  exact e2.symm.trans hk
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteNonemptyAffineCoverOfIntegral
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_finite_nonempty_affine_cover_of_integral :
    ∀ (C : Scheme.{0}) [CompactSpace C] [IsIntegral C], ∃ (n : ℕ) (U : Fin n → C.Opens), (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Nonempty (U i)) ∧ (0 < n) ∧ ∀ y : C, ∃ i, y ∈ U i := by
  intro C _ _
  have hex : ∀ y : C, ∃ W : C.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hWa hyW using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set C))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨y0⟩ := (inferInstance : Nonempty C)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y0))
    exact ⟨i, hi⟩
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWa _,
    fun i => ⟨⟨_, hyW _⟩⟩, Finset.card_pos.2 htne, fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
  simpa using hy
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFunctionFieldHomGermOfSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
end

