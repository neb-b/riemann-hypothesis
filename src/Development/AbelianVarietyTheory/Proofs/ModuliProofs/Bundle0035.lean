module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.ConstThickening

theorem existsUnique_of_isPushout {K : Type} [Field K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra K A := c.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber K) A' := s.toAlgebra
  let _ : Algebra K A' := (s.comp (algebraMap K (DualNumber K))).toAlgebra
  have : IsScalarTower K (DualNumber K) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout K A (DualNumber K) A' := CommRingCat.isPushout_iff_isPushout.mp H
  let b : Module.Basis (Fin 2) K (DualNumber K) := Module.Basis.finTwoProd K
  have b0 : b 0 = 1 := Module.Basis.finTwoProd_zero K
  have b1 : b 1 = DualNumber.eps := Module.Basis.finTwoProd_one K
  let B := h.out.basis b
  have B0 : B 0 = 1 := by
    rw [h.out.basis_apply, b0]; exact map_one s
  have B1 : B 1 = s DualNumber.eps := by
    rw [h.out.basis_apply, b1]; rfl
  have key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y] := fun x y => by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one,
      _root_.mul_comm (s _)]
    rfl
  refine ⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩
  · change F = _
    rw [key, LinearEquiv.eq_symm_apply]
    ext i; fin_cases i <;> rfl
  · replace hab : F = _ := hab
    rw [key, LinearEquiv.eq_symm_apply] at hab
    rw [hab]; rfl

variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem existsUnique_affine (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {U : Y.Opens}
    (hU : IsAffineOpen U) (F : Γ(Y', ρ ⁻¹ᵁ U)) : ∃! ab : Γ(Y, U) × Γ(Y, U),
      F = (ρ.app U).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app U).hom ab.2 := by
  refine existsUnique_of_isPushout (constHom q U) (ρ.app U) (constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ DualNumber.eps * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ DualNumber.eps * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add (f := _), map_mul, res_app ρ h, res_app ρ h, res_constFn]

theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem unique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {O : Y.Opens} {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (existsUnique_affine H U.2.1 _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

theorem existsUnique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (existsUnique_affine H U.2.1 ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber K)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem structure_dualNumber : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro K _ Y Y' q π ρ j H hj hq
  have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hp : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hq H
    rw [hj, e]
    exact IsPullback.id_horiz q
  refine ⟨fun O => ?_, hp, existsUnique_comb H⟩
  have hs : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) hp.flip surjective_spMap_fst
  ext x
  obtain ⟨y, rfl⟩ := hs.surj x
  change j (ρ (j y)) ∈ O ↔ j y ∈ O
  rw [← Scheme.Hom.comp_apply j ρ, hj]
  rfl

end GlobalTheory.ConstThickening
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtSetOfLists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem etSet_of_lists : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S') ⟶ G')) (K : Set G.left), IsAbelianScheme G → IsGrpPullback G' G f φ → IsUnit (N : Γ(S, ⊤)) → IsFinite f → Etale f → Surjective f → Lists N σ (φ ⁻¹' K) → EtSet G K := by
  intro S S' f G G' _ _ φ N n σ K hG h hN hfin het hsurj hL
  obtain ⟨hpow, hK, -⟩ := hL
  obtain ⟨-, hWf, hWe⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  have := hG.proper
  let T : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hTf : IsFinite T.hom := by
    change IsFinite (𝟙 S' ≫ f); infer_instance
  have hTe : Etale T.hom := by
    change Etale (𝟙 S' ≫ f); infer_instance
  let ρ : (𝟙_ (Over S') ⟶ G') →* (T ⟶ G) :=
    MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl))
      fun x y => Over.OverMorphism.ext (h.2 _ x y _ _ rfl rfl).symm
  have hρ : ∀ j, ρ (σ j) ^ N = 1 := fun j => by rw [← map_pow, hpow, map_one]
  choose τ hτ using fun j => (LatticeTorsion.existsUnique_torsion G N (ρ (σ j)) (hρ j)).exists
  have hτl : ∀ j, (τ j).left ≫ (torsion.ι G N).left = (σ j).left ≫ φ := fun j =>
    congrArg (fun z => z.left) (hτ j)
  have hτf : ∀ j, IsFinite (τ j).left := fun j => by
    have : IsFinite ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTf
    exact IsFinite.of_comp _ (torsion G N).hom
  have hτe : ∀ j, Etale (τ j).left := fun j => by
    have : Etale ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTe
    exact Etale.of_comp _ (torsion G N).hom
  have hop : IsOpen (⋃ j, Set.range (τ j).left) :=
    isOpen_iUnion fun j => (τ j).left.isOpenMap.isOpen_range
  have hcl : IsClosed (⋃ j, Set.range (τ j).left) :=
    isClosed_iUnion_of_finite fun j => (τ j).left.isClosedMap.isClosed_range
  let U : (torsion G N).left.Opens := ⟨_, hop⟩
  have hU : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl)
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp _ G.hom
  have hι : IsClosedImmersion (torsion.ι G N).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion G N).flip hη
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hsurj
  refine ⟨Over.mk (U.ι ≫ (torsion G N).hom), Over.homMk (U.ι ≫ (torsion.ι G N).left) (by simp), ?_, ?_, ?_, ?_⟩
  · change IsFinite (U.ι ≫ _); infer_instance
  · change Etale (U.ι ≫ _); infer_instance
  · change IsClosedImmersion (U.ι ≫ _); infer_instance
  · change Set.range (U.ι ≫ (torsion.ι G N).left) = K
    rw [← Set.image_preimage_eq K φ.surjective, hK, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    change _ '' (⋃ j, Set.range (τ j).left) = _
    rw [Set.image_iUnion, Set.image_iUnion]
    refine Set.iUnion_congr fun j => ?_
    rw [← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← Scheme.Hom.comp_base, hτl]

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
theorem _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  intro R B C _ _ _ _ _ φ D hadd hmul
  have h0 : D 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have h1 : D 1 = 0 := by
    have h11 := hmul 1 1
    have e : (1 : R) * 1 = 1 := mul_one 1
    rw [e, map_one, map_one, _root_.one_mul] at h11
    linear_combination -h11
  let ψ : R →+* TrivSqZeroExt C C :=
    { toFun := fun r => TrivSqZeroExt.inl (φ (algebraMap R B r)) + TrivSqZeroExt.inr (D r)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun a b => by ext <;> simp [hmul] <;> ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun a b => by ext <;> simp [hadd] }
  letI : Algebra R (TrivSqZeroExt C C) := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let g : TrivSqZeroExt C C →ₐ[R] C :=
    { (TrivSqZeroExt.fstHom C C C).toRingHom with
      commutes' := fun r => by
        show (ψ r).fst = φ (algebraMap R B r)
        simp [ψ] }
  let f : B →ₐ[R] C :=
    { φ with
      commutes' := fun r => rfl }
  have hg : Function.Surjective g := fun c => ⟨TrivSqZeroExt.inl c, by simp [g]⟩
  have hker : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hker
  refine ⟨fun b => (L b).snd, fun a b => ?_, fun a b => ?_, fun r => ?_⟩
  · simp
  · have hfa : (L a).fst = φ a := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker a
    have hfb : (L b).fst = φ b := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker b
    simp [hfa, hfb]
    ring
  · show (L (algebraMap R B r)).snd = D r
    rw [L.commutes r]
    show (ψ r).snd = D r
    simp [ψ]

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDualFamilyModSubspace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_dual_family_mod_subspace (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (B : Submodule K V) (g : ℕ) (φ : Fin g → V)
    (h : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) :
    ∃ β : Fin g → Module.Dual K V, (∀ b, B ≤ LinearMap.ker (β b)) ∧
      ∀ b a, β b (φ a) = if a = b then 1 else 0 := by
  classical

  have hli : LinearIndependent K (fun a => B.mkQ (φ a)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : B.mkQ (∑ a, c a • φ a) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_smul] using hc
    have hc0 := h c ((Submodule.Quotient.mk_eq_zero B).mp h0)
    intro i
    simp [hc0]

  let e := Module.Basis.span hli
  choose ext hext using fun b => LinearMap.exists_extend (e.coord b)
  refine ⟨fun b => (ext b).comp B.mkQ, fun b x hx => ?_, fun b a => ?_⟩
  · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
  · have hmem : B.mkQ (φ a) ∈ Submodule.span K (Set.range fun a => B.mkQ (φ a)) :=
      Submodule.subset_span ⟨a, rfl⟩
    have he : (⟨B.mkQ (φ a), hmem⟩ : Submodule.span K (Set.range fun a => B.mkQ (φ a))) = e a :=
      (Module.Basis.span_apply hli a).symm
    have hb := LinearMap.congr_fun (hext b) ⟨B.mkQ (φ a), hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hb
    rw [LinearMap.comp_apply, hb, he, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem exists_symm_matrix_mod_subspace :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (B : Submodule K V) (g : ℕ) (θ φ : Fin g → V), (∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) → (∀ α β : Module.Dual K V, B ≤ LinearMap.ker α → B ≤ LinearMap.ker β → ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, θ b - ∑ a, Θ b a • φ a ∈ B := by
  intro K V _ _ _ B g θ φ hind hsym
  classical
  obtain ⟨β, hβB, hβφ⟩ := exists_dual_family_mod_subspace K V B g φ hind

  have key : ∀ α : Module.Dual K V, B ≤ LinearMap.ker α →
      ∀ b, α (θ b) = ∑ a, α (φ a) * β b (θ a) := by
    intro α hα b
    rw [← hsym α (β b) hα (hβB b)]
    simp [hβφ]
  refine ⟨Matrix.of fun b a => β b (θ a), Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · simp only [Matrix.of_apply]
    rw [key (β i) (hβB i) j]
    simp [hβφ]
  · simp only [Matrix.of_apply]
    by_contra hx
    have hq : B.mkQ (θ b - ∑ a, β b (θ a) • φ a) ≠ 0 :=
      fun h0 => hx ((Submodule.Quotient.mk_eq_zero B).mp h0)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual K (V ⧸ B), f (B.mkQ (θ b - ∑ a, β b (θ a) • φ a)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff K _).mp hall)
    apply hf
    have hα : B ≤ LinearMap.ker (f.comp B.mkQ) := fun x hx =>
      by simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
    have hk := key (f.comp B.mkQ) hα b
    simp only [LinearMap.comp_apply] at hk
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, smul_eq_mul, hk]
    simp [mul_comm]

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteAffineCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.FinAffineCharts

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem cocycle_on {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  rwa [map_mul, res_res, res_res, res_res] at this

noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩

theorem refineLB_isLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB := {
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm) }

theorem iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by
  refine ⟨⟨fun p => res (inf_le_inf_right _ (h p.1) : W p.1 ⊓ L.U p.2 ≤ L.U (c p.1) ⊓ L.U p.2)
    (L.g (c p.1) p.2)⟩, ?_⟩
  have key : ∀ (a b : κ) (i j : L.ι),
      res (inf_le_left : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ L.U i)
        (res (inf_le_inf_right _ (h a) : W a ⊓ L.U i ≤ L.U (c a) ⊓ L.U i) (L.g (c a) i)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ W b)
        (res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ L.U i ⊓ L.U j) (L.g i j))⁻¹ *
      res (inf_le_right : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W b ⊓ L.U j)
        (res (inf_le_inf_right _ (h b) : W b ⊓ L.U j ≤ L.U (c b) ⊓ L.U j) (L.g (c b) j)) := by
    intro a b i j
    rw [res_res, res_res, res_res, mul_right_comm, cocycle_on hL (c a) (c b) j _ _
      (le_inf (inf_le_left.trans (inf_le_left.trans (h a))) (inf_le_right.trans inf_le_right)),
      eq_mul_inv_iff_mul_eq]
    exact cocycle_on hL _ _ _ _ _ _
  exact fun p q => key p.1 q.1 p.2 q.2

theorem exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a,
    top_le_iff.1 ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem exists_finite_affine_charts : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L' := by
  intro X L _ hL
  obtain ⟨κ, hκ, W, c, hW, h, hc⟩ := exists_finite_affine_cover L hL
  exact ⟨refineLB L W c h, hκ, refineLB_isLB hL W c h hc, hW, iso_refineLB hL W c h⟩

end GlobalTheory.FinAffineCharts
end

