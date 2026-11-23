module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0021
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0018
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0016
public import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityEqLocallyConstantPowersSpectrum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ClosedFiberAffineSurjectiveKerMaximalIdeal
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {X F : Scheme.{0}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of A)) (r : F ⟶ X) (c : F ⟶ Spec (CommRingCat.of (ResidueField A))),
      IsPullback r c p (cpt A) → IsAffine F ∧ Function.Surjective r.appTop.hom ∧ RingHom.ker r.appTop.hom = (maximalIdeal A).map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p).appTop).hom) := by
  intro A _ _ X F _ p r c h
  have hcpt : IsClosedImmersion (cpt A) :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective)
  have hr : IsClosedImmersion r := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hcpt
  obtain ⟨hF, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine r
  refine ⟨hF, hsurj, ?_⟩
  have hinv : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ r.appTop =
      CommRingCat.ofHom (residue A) ≫ (Scheme.ΓSpecIso _).inv ≫ c.appTop := by
    rw [← Scheme.Hom.comp_appTop, h.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  set φ := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom with hφ
  set I := (maximalIdeal A).map φ with hI
  apply le_antisymm
  · intro b hb
    rw [RingHom.mem_ker] at hb
    let π : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let χ0 : A ⧸ maximalIdeal A →+* Γ(X, ⊤) ⧸ I :=
      Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk I).comp φ)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ ha))
    let χ : CommRingCat.of (ResidueField A) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom χ0
    let z : Spec (CommRingCat.of (Γ(X, ⊤) ⧸ I)) ⟶ X := Spec.map π ≫ X.isoSpec.inv
    have hz : z ≫ p = Spec.map χ ≫ cpt A := by
      apply ext_of_isAffine
      rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv,
        ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom]
      simp only [z, cpt, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        Scheme.ΓSpecIso_naturality_assoc, reassoc_of% hinv, Iso.inv_hom_id_assoc, Category.id_comp]
      ext a
      rfl
    let u := h.lift z (Spec.map χ) hz
    have hu : u ≫ r = z := h.lift_fst _ _ _
    have hzt : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom = π := by
      simp only [z, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        reassoc_of% hinv, Category.id_comp]
    have e1 : z.appTop = r.appTop ≫ u.appTop := by
      rw [← Scheme.Hom.comp_appTop, hu]
    have e2 := congrArg (fun f => f.hom b) hzt
    rw [e1] at e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hb, map_zero] at e2
    exact Ideal.Quotient.eq_zero_iff_mem.1 e2.symm
  · refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f => f.hom a) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    rw [hφ, CommRingCat.hom_comp, RingHom.comp_apply, e, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero, map_zero]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.DescentOfIntegralDescentTruncation
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

theorem UpperTheory.descent_of_integral_descent_truncation :
    LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels → LateralTheory.E.t_E2Cut.Desc := by
  intro hT hH q i A _ _ hq P p hyp
  have neg : ∀ n : ℤ, n < 0 → ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A))) := by
    intro n hn X g
    refine ⟨fun m hm => ?_, fun x y _ => ?_⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1
        (sch.obj (pullback g (LateralTheory.E.t_E2Cut.cpt A))) m (by omega)
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj X) n hn
      exact Subsingleton.elim _ _
  let C : ℤ → Prop := fun n => ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      (∃ h : X ⟶ P, IsIntegralHom h ∧ g = h ≫ p) →
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))
  have step : ∀ n : ℤ, (∀ m, m < n → C m) → C n := by
    intro n ih X g hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨Y, k, hk, hks, hpb⟩ := hyp X h hh
    haveI := hk
    haveI := hks
    obtain ⟨U, E, u, a', a, hcomm, ha, ha', hall, h0⟩ :=
      UpperTheory.cohomology_base_change_integral_surjective_cech hH.b4 q i k (h ≫ p) (LateralTheory.E.t_E2Cut.cpt A)
        (LateralTheory.E.t_E2Cut.unit_of hq (h ≫ p))
    have hu : RelZS (ZMod q) (tw q i) n u := by
      refine hT (ZMod q) (tw q i) u n (fun p' m hm => ?_) ?_
      · obtain ⟨L, l, hl, hL⟩ := hall p'
        apply hL m
        haveI := hl
        haveI := hh
        exact ih m hm (l ≫ h ≫ p) ⟨l ≫ h, inferInstance, by simp [Category.assoc]⟩
      · apply h0 n
        exact ⟨fun m' _ => (hpb m').2, (hpb n).1⟩
    exact transfer (ZMod q) (tw q i) u _ a' a hcomm ha ha' n hu
  have all : ∀ n, C n := by
    have key : ∀ k : ℕ, ∀ n : ℤ, n < k → C n := by
      intro k
      induction k with
      | zero =>
        intro n hn X g _
        exact neg n (by exact_mod_cast hn) g
      | succ k ihk =>
        intro n hn
        by_cases hn' : n < k
        · exact ihk n hn'
        · exact step n (fun m hm => ihk m (by push_cast at hn ⊢; omega))
    intro n
    exact key (n.toNat + 1) n (by omega)
  have hp : ∃ h : P ⟶ P, IsIntegralHom h ∧ p = h ≫ p := ⟨𝟙 P, inferInstance, by simp⟩
  intro n
  exact ⟨(all n p hp).2, (all (n + 1) p hp).1 n rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCupProductHomOfCocycleVanishingOnOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem leib {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (W : Scheme.{0})
    (s s' t w w' : ℤ) (h : s + t = w) (h' : s' + t = w') (hs : s' = s + 1)
    (a : Sec (I.X s) W) (b : Sec (J.X t) W) (hb : Sec.map (J.d t (t + 1)) b = 0) :
    Sec.map (K.d w w') (μ.mul W s t w h a b) = μ.mul W s' t w' h' (Sec.map (I.d s s') a) b := by
  subst hs
  obtain rfl : w' = w + 1 := by omega
  rw [μ.leibniz W s t w h a b, hb, map_zero, smul_zero, add_zero]

private theorem res_usmul {R : Type} [CommRing R] {F : Shv R} {V W : Scheme.{0}} (g : V ⟶ W)
    (u : ℤˣ) (x : Sec F W) : Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Sec.res, Units.smul_def, map_zsmul]

private theorem map_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {W : Scheme.{0}}
    (u : ℤˣ) (x : Sec F W) : Sec.map φ (u • x) = u • Sec.map φ x := by
  simp only [Sec.map, Units.smul_def, map_zsmul]

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {V W X : Scheme.{0}} (g : V ⟶ W)
    (f : W ⟶ X) (x : Sec F X) : Sec.res (g ≫ f) x = Sec.res g (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp]
  rfl

private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V W : Scheme.{0}}
    (g : V ⟶ W) (x : Sec F W) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op) x

private noncomputable def prodFam {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K)
    {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X)
    (hU : Sec.res U.ι β = 0) (p : ℕ) (s : ℤ) :
    Fam (Sub.bot E) p (I.X (s + 0)) →+
      Fam (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) p (K.X (s + m)) where
  toFun a := ⟨fun W z => (m * (p : ℕ)).negOnePow •
      μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β), fun V W g z => by
      beta_reduce
      rw [res_usmul, μ.nat, a.2.1 V W g z, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.1 V g, res_comp],
    fun W z h => by
      obtain ⟨w, hw⟩ := (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1.1 h
      beta_reduce
      rw [← hw, res_comp, hU]
      simp⟩
  map_zero' := by ext W z; simp
  map_add' a b := by ext W z; simp

theorem UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X), Sec.map (J.d m (m + 1)) β = 0 → Sec.res U.ι β = 0 →
    ∃ Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m), IsProd μ π β Φ ∧ Φ.Ok := by
  intro R _ I J K μ X U E π m β hd hU
  refine ⟨fun p s => prodFam μ U π m β hU p s, fun p s a W z => rfl, ?_, ?_⟩
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    change (m * (p : ℕ)).negOnePow • μ.mul W (s + 1 + 0) m (s + 1 + m) (by omega)
        (Sec.map (I.d (s + 0) (s + 1 + 0)) (a.1 W z)) (Sec.res (under π z) β) =
      Sec.map (K.d (s + m) (s + 1 + m)) ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β))
    rw [map_usmul, leib μ W (s + 0) (s + 1 + 0) m (s + m) (s + 1 + m) (by omega) (by omega) (by omega)
      _ _ (by rw [map_res, hd]; simp)]
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    have hf : ∀ i : Fin (p + 2), under π (z.face i) = under π z := fun i =>
      (UpperTheory.mem_pullbackImage_iff_factors_through_open U π (p + 1) W z).2.2 p (SimplexCategory.δ i)
    change ((m * ((p + 1 : ℕ) : ℤ))).negOnePow • μ.mul W (s + 0) m (s + m) (by omega)
        ((0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W (z.face i)) (Sec.res (under π z) β) =
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W (z.face i)) (Sec.res (under π (z.face i)) β))
    simp only [hf]
    have hsign : (m * ((p + 1 : ℕ) : ℤ)).negOnePow = m.negOnePow * (m * (p : ℕ)).negOnePow := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm, Int.negOnePow_add]
    generalize Sec.res (under π z) β = b
    let f := ((μ.mul W (s + 0) m (s + m) (by omega)).flip b).toAddMonoidHom
    change _ • f _ = _ • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (_ • f _)
    have e : ∀ (u : ℤˣ) (i : Fin (p + 2)) (y : Sec (K.X (s + m)) W),
        (-1 : ℤ) ^ (i : ℕ) • (u • y) = u • ((-1 : ℤ) ^ (i : ℕ) • y) := by
      intro u i y
      simp only [Units.smul_def]
      exact smul_comm _ _ _
    simp only [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hsign, mul_smul, Int.negOnePow_zero, one_smul, map_sum]
    simp only [map_zsmul]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiberPullbackSquareOfOpenImmersions
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.exists_fiber_pullback_square_of_open_immersions :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
      ∃ (r : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ pullback ι₁ ι₂) (c : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ Spec (CommRingCat.of (ResidueField A))),
        IsPullback r c (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.fst ι₁ ι₂ = pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.snd ι₁ ι₂ = pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) := by
  intro A _ _ Z U V p ι₁ ι₂
  have m1 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.fst p (cpt A) = pullback.fst (ι ≫ p) (cpt A) ≫ ι := by
    intro Y ι
    exact pullback.lift_fst _ _ _
  have m2 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.snd p (cpt A) = pullback.snd (ι ≫ p) (cpt A) := by
    intro Y ι
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have m1' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : Z ⟶ W), fibMap p ι ≫ pullback.fst p (cpt A) ≫ k = pullback.fst (ι ≫ p) (cpt A) ≫ ι ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m1, Category.assoc]
  have m2' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : _ ⟶ W), fibMap p ι ≫ pullback.snd p (cpt A) ≫ k = pullback.snd (ι ≫ p) (cpt A) ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m2]
  have hr1 : (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A)) ≫ ι₁ =
      (pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A)) ≫ ι₂ := by
    rw [Category.assoc, Category.assoc, ← m1, ← m1, ← Category.assoc, pullback.condition, Category.assoc]
  let r := pullback.lift _ _ hr1
  let c := pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A)
  refine ⟨r, c, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have cond : pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p = pullback.snd (ι₁ ≫ p) (cpt A) ≫ cpt A := by
    exact pullback.condition
  have w : r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = c ≫ cpt A := by
    simp only [r, c, pullback.lift_fst_assoc, Category.assoc, cond]
  have cond2 : pullback.fst ι₁ ι₂ ≫ ι₁ = pullback.snd ι₁ ι₂ ≫ ι₂ := pullback.condition
  have L : ∀ (s : PullbackCone (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A)),
      ∃ l : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), l ≫ r = s.fst ∧ l ≫ c = s.snd ∧
        ∀ m : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), m ≫ r = s.fst → m ≫ c = s.snd → m = l := by
    intro s
    have hs : s.fst ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = s.snd ≫ cpt A := s.condition
    have hs1 : (s.fst ≫ pullback.fst ι₁ ι₂) ≫ ι₁ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc]
      exact hs
    have hs2 : (s.fst ≫ pullback.snd ι₁ ι₂) ≫ ι₂ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc, ← Category.assoc (pullback.snd ι₁ ι₂), ← cond2, Category.assoc]
      exact hs
    let x₁ := pullback.lift _ _ hs1
    let x₂ := pullback.lift _ _ hs2
    have hx : x₁ ≫ fibMap p ι₁ = x₂ ≫ fibMap p ι₂ := by
      apply pullback.hom_ext
      · simp only [x₁, x₂, Category.assoc, m1, pullback.lift_fst_assoc, cond2]
      · simp only [x₁, x₂, Category.assoc, m2, pullback.lift_snd]
    refine ⟨pullback.lift x₁ x₂ hx, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [r, x₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [r, x₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [c, x₁, pullback.lift_fst_assoc, pullback.lift_snd]
    · intro m hm1 hm2
      have e1 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) = s.fst ≫ pullback.fst ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_fst]
      have e2 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) = s.fst ≫ pullback.snd ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_snd]
      have e3 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A) = s.snd := hm2
      have e4 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₂ ≫ p) (cpt A) = s.snd := by
        rw [← m2 ι₂, ← pullback.condition_assoc, m2 ι₁]
        exact e3
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, x₁, e1]
        · simp only [Category.assoc, pullback.lift_fst, x₁, e3, pullback.lift_snd]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd, x₂, e2, pullback.lift_fst]
        · simp only [Category.assoc, pullback.lift_snd, x₂, e4]
  choose l hl1 hl2 hl3 using L
  exact IsPullback.of_isLimit (c := PullbackCone.mk r c w)
    (PullbackCone.IsLimit.mk w l hl1 hl2 (fun s m h1 h2 => hl3 s m h1 h2))

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSpecializationOfEvalNeZero
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.exists_specialization_of_eval_ne_zero :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] (n : ℕ) (x : Fin n → L) (s : Finset L), ∃ g : MvPolynomial (Fin n) k, MvPolynomial.aeval x g ≠ 0 ∧ ∀ c : Fin n → k, (∀ p : MvPolynomial (Fin n) k, MvPolynomial.aeval x p = 0 → MvPolynomial.eval c p = 0) → MvPolynomial.eval c g ≠ 0 → ∃ (R : Subalgebra k L) (hx : ∀ i, x i ∈ R) (φ : R →ₐ[k] k), (s : Set L) ⊆ R ∧ ∀ i, φ ⟨x i, hx i⟩ = c i := by
  intro k L _ _ _ _ n x s
  let f : MvPolynomial (Fin n) k →ₐ[k] L := MvPolynomial.aeval x
  let J : Ideal (MvPolynomial (Fin n) k) := RingHom.ker f
  haveI : J.IsPrime := RingHom.ker_isPrime _
  let ξ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] L := Ideal.kerLiftAlg f
  have hξinj : Function.Injective ξ := Ideal.kerLiftAlg_injective f
  have hξmk : ∀ p, ξ (Ideal.Quotient.mk J p) = MvPolynomial.aeval x p := fun p => rfl
  haveI : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)
  obtain ⟨a, S, hξ, ha, hs, H⟩ := GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k
    (MvPolynomial (Fin n) k ⧸ J) L ξ hξinj s
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.2 h0), fun c hc hg => ?_⟩
  let e : MvPolynomial (Fin n) k →ₐ[k] k := MvPolynomial.aeval c
  have he : ∀ p, e p = MvPolynomial.eval c p := fun p => by
    simp [e, MvPolynomial.coe_aeval_eq_eval]
  let φ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] k :=
    Ideal.Quotient.liftₐ J e (fun p hp => by
      rw [he]
      exact hc p hp)
  have hφmk : ∀ p, φ (Ideal.Quotient.mk J p) = e p := fun p => rfl
  obtain ⟨ψ, hψ⟩ := H φ (by rw [hφmk, he]; exact hg)
  have hxS : ∀ i, x i ∈ S := fun i => by
    have := hξ (Ideal.Quotient.mk J (MvPolynomial.X i))
    rwa [hξmk, MvPolynomial.aeval_X] at this
  refine ⟨S, hxS, ψ, fun t ht => hs t ht, fun i => ?_⟩
  have h1 : (⟨x i, hxS i⟩ : S) = ⟨ξ (Ideal.Quotient.mk J (MvPolynomial.X i)), hξ _⟩ :=
    Subtype.ext (((hξmk _).trans (MvPolynomial.aeval_X x i)).symm)
  rw [h1, hψ, hφmk, he, MvPolynomial.eval_X]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsChartAffineSectionsOfIsCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem ded_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [IsDedekindDomain S] :
    IsDedekindDomain R := by
  have : IsDomain R := Function.Injective.isDomain (e : R →+* S) e.injective
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact { }

private theorem base_comp {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k C.functionField) =
      c.appLE ⊤ W le_top ≫ C.germToFunctionField W := by
  rw [← Scheme.ΓSpecIso_naturality, hgen]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem pre_ne {X Y : Scheme.{0}} (u : X ⟶ Y) (hu : Surjective u) (W : Y.Opens)
    (h : (W : Set Y).Nonempty) : ((u ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, rfl⟩ := hu.surj w
  exact ⟨y, hw⟩

theorem UpperTheory.isChart_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsChart B := by
  intro k _ _ C _ c hc _ hgen W _ hW B hB
  have hWne : (W : Set C).Nonempty := ⟨_, (Classical.arbitrary W).2⟩
  obtain ⟨hC1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc
  obtain ⟨hded, hnf⟩ := hC1 W hW hWne
  let f : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hmem : ∀ a, f a ∈ B := by
    intro a
    have : f a ∈ (B : Set C.functionField) := by
      rw [hB]; exact ⟨a, rfl⟩
    exact this
  let h : Γ(C, W) ≃+* B := RingEquiv.ofBijective
    (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem)
    ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab),
     fun b => by
      have hb : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
      rw [hB] at hb
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩
  have hh : ∀ a, (h a : C.functionField) = f a := fun a => rfl
  unfold IsChart
  refine ⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩
  · haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1
    have g0 := c.finiteType_appLE (isAffineOpen_top (Sp k)) hW le_top
    have gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)
    have g2 := (g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective
    rw [← RingHom.finiteType_algebraMap]
    convert g2
    ext x
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hh] at this
    simpa using this
  · have hfr := functionField_isFractionRing_of_isAffineOpen C W hW
    have := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr
    have heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra =
        (inferInstance : Algebra B C.functionField) := by
      apply Algebra.algebra_ext
      intro b
      obtain ⟨a, rfl⟩ := h.surjective b
      show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)
      rw [h.symm_apply_apply]
      rfl
    rw [heq] at this
    exact this
  · intro L _ _ _
    have hp := IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    obtain ⟨hX, e, -, -⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB
    have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp
    obtain ⟨hX1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)
    obtain ⟨hd2, hn2⟩ := hX1 _ hX (pre_ne _ hsurj W hWne)
    exact ⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SchemeRootsOfUnityEqLocallyConstantPowers
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
end

