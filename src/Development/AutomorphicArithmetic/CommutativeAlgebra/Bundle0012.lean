module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIso

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyDescentOfCechCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

private theorem conn_neg (a9 : A9) {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) :
    Conn R f F (-1) := by
  have hs := (a9 R F).1
  refine ⟨fun j hj => ?_, ?_⟩
  · haveI := hs E j (by omega)
    haveI := hs E' j (by omega)
    exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · haveI := hs E' (-1) (by omega)
    exact Function.injective_of_subsingleton _

private theorem conn_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (n : ℤ) :
    Conn R (disc.map f) F n ↔ Conn R (disc.map g) F n := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact conn_sq R w (eqv_iso R _ F) (eqv_iso R _ F) n

private theorem eqv_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (h : Eqv R (disc.map g) F) : Eqv R (disc.map f) F := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact fun n => ((sq R w (eqv_iso R _ F) (eqv_iso R _ F) n).1).2 (h n)

private theorem conn_all (a1 : A1) (a9 : A9) (b1 : B1) (b2 : B2) (b4 : B4) (hC : Cover) (hE : EqvQA)
    (hD : DescStep) (hL : CechLevels) (q : ℕ) [NeZero q] (i : ℤ) (m : ℕ) :
    ∀ (B : Type) [CommRing B] (J : Ideal B), IsUnit (q : B) →
      (∀ (C : Type) [CommRing C] (χ : B →+* C), χ.IsIntegral → Good C (J.map χ)) →
      Conn (ZMod q) (spMap (Ideal.Quotient.mk J)) (tw q i) ((m : ℤ) - 1) := by
  induction m with
  | zero =>
    intro B _ J _ _
    rw [Nat.cast_zero, zero_sub]
    exact conn_neg a9 _ _
  | succ m ih =>
    intro B _ J hq hG
    obtain ⟨A', _, φ, hφ, hsurj, hQA⟩ := hC B
    obtain ⟨⟨h1, h2, h3, h4⟩, ψ, hψ, hlev, h0⟩ := hL B A' φ J hφ hsurj
    have hψc : Conn (ZMod q) ψ (tw q i) ((m : ℤ) - 1 + 1) := by
      apply hD a1 (ZMod q) (tw q i) ψ ((m : ℤ) - 1)
      · intro p
        obtain ⟨C, _, χ, hχ, ⟨e⟩⟩ := hlev p
        rw [conn_level e]
        apply ih C (J.map χ) (by simpa using hq.map χ)
        intro C' _ χ' hχ'
        rw [Ideal.map_map]
        exact hG C' (χ'.comp χ) (RingHom.IsIntegral.trans _ _ hχ hχ')
      · obtain ⟨e⟩ := h0
        apply eqv_level e
        exact hE a1 a9 b1 b2 q A' (J.map φ) hQA (hG A' φ hφ) (by simpa using hq.map φ) i
    have hmm : ((m : ℤ) - 1 + 1) = ((m + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [hmm] at hψc
    have hqJ : IsUnit ((q : ℕ) : B ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
    have ea := @b4 q _ _ (Spec.map (CommRingCat.ofHom φ)) h1 h2 (unit_spec (A := B) hq) i
    have eb := @b4 q _ _ _ h3 h4 (unit_spec (A := B ⧸ J) hqJ) i
    exact (conn_sq (ZMod q) hψ eb ea _).1 hψc

theorem UpperTheory.etaleCohomology_descent_of_cech_cover :
    A1 → A9 → B1 → B2 → B4 → Cover → HensIdem → EqvQA → DescStep → CechLevels → E1 := by
  intro a1 a9 b1 b2 b4 hC hH hE hD hL q A _ I _ hq i
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : A) = 1 := isUnit_zero_iff.mp (by simpa using hq)
    haveI : Subsingleton A := subsingleton_of_zero_eq_one h01
    have hb : Function.Bijective (Ideal.Quotient.mk I) :=
      ⟨fun x y _ => Subsingleton.elim x y, Ideal.Quotient.mk_surjective⟩
    haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
      (RingEquiv.ofBijective (Ideal.Quotient.mk I) hb).toCommRingCatIso.isIso_hom
    exact eqv_iso _ _ _
  · haveI : NeZero q := ⟨hq0⟩
    intro n
    have hc := conn_all a1 a9 b1 b2 b4 hC hE hD hL q i (n.toNat + 2) A I hq
      (fun C _ χ hχ => hH A I C χ hχ)
    exact hc.1 n (by push_cast; omega)

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupHomExistsUniqueOfUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.GqPt

private theorem hom_ext (q : ℕ) {R : Type} [CommRing R] {f g : LqR q →+* R}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g :=
  _root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) :
    sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private theorem val_map_tq (q : ℕ) {T : Scheme.{0}} (s : T ⟶ Gq q) :
    ((Units.map s.appTop.hom.toMonoidHom (tq q) : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) =
      (sec s).hom (LaurentPolynomial.T 1) := rfl

end UpperTheory.GqPt

open UpperTheory.GqPt in
theorem UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit ((q : ℕ) : Γ(T, ⊤)) → ∀ t : (Γ(T, ⊤))ˣ, ∃! s : T ⟶ Gq q, Units.map s.appTop.hom.toMonoidHom (tq q) = t := by
  intro q _ T hq t
  let lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)
  let φ : LqR q →+* Γ(T, ⊤) := LaurentPolynomial.eval₂ lam t
  have hφ : φ (LaurentPolynomial.T 1) = t := by
    simp only [φ, LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · refine Units.ext ?_
    rw [val_map_tq, sec_to]
    exact hφ
  · intro s hs
    refine sec_inj ?_
    rw [sec_to]
    refine CommRingCat.hom_ext (hom_ext q ?_)
    have h1 := val_map_tq q s
    rw [hs] at h1
    exact h1.symm.trans hφ.symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedCohomologySpecProdBijectiveProd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.SectionRestriction

variable {R : Type} [CommRing R]

private theorem pl_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem pl_id {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_zero {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_add {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (f + g) F n x = HK.pull R f F n x + HK.pull R g F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [HK.pull, HK.pull, HK.pull, HK.pre, HK.pre, HK.pre, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem split_bij {K₁ K₂ L : Cx R} (c₁ : K₁ ⟶ L) (c₂ : K₂ ⟶ L) (hd : IsIso (biprod.desc c₁ c₂))
    (F : Shv R) (n : ℤ) :
    Function.Bijective fun x : HK R L F n => (HK.pull R c₁ F n x, HK.pull R c₂ F n x) := by
  set d := biprod.desc c₁ c₂ with hdd
  let r₁ : L ⟶ K₁ := inv d ≫ biprod.fst
  let r₂ : L ⟶ K₂ := inv d ≫ biprod.snd
  have e₁ : c₁ = biprod.inl ≫ d := by simp [hdd]
  have e₂ : c₂ = biprod.inr ≫ d := by simp [hdd]
  have h11 : c₁ ≫ r₁ = 𝟙 _ := by simp [r₁, e₁]
  have h12 : c₁ ≫ r₂ = 0 := by simp [r₂, e₁]
  have h21 : c₂ ≫ r₁ = 0 := by simp [r₁, e₂]
  have h22 : c₂ ≫ r₂ = 𝟙 _ := by simp [r₂, e₂]
  have hs : r₁ ≫ c₁ + r₂ ≫ c₂ = 𝟙 _ := by
    have : d = biprod.fst ≫ c₁ + biprod.snd ≫ c₂ := biprod.desc_eq
    calc r₁ ≫ c₁ + r₂ ≫ c₂ = inv d ≫ (biprod.fst ≫ c₁ + biprod.snd ≫ c₂) := by
          simp [r₁, r₂, Preadditive.comp_add]
      _ = 𝟙 _ := by rw [← this]; simp
  have hx : ∀ x : HK R L F n, x = HK.pull R r₁ F n (HK.pull R c₁ F n x) + HK.pull R r₂ F n (HK.pull R c₂ F n x) := by
    intro x
    rw [← pl_comp, ← pl_comp, ← pl_add, hs, pl_id]
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [hx x, hx y, h1, h2]
  · rintro ⟨a, b⟩
    refine ⟨HK.pull R r₁ F n a + HK.pull R r₂ F n b, Prod.ext ?_ ?_⟩
    · simp only [map_add (f := _)]
      rw [← pl_comp, ← pl_comp, h11, h12, pl_id, pl_zero, add_zero]
    · simp only [map_add (f := _)]
      rw [← pl_comp, ← pl_comp, h21, h22, pl_id, pl_zero, zero_add]

private theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op).symm x

private theorem sec_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

private theorem sec_bij (F : Shv R) (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) =>
      ((Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s : Sec F (Spec (CommRingCat.of A))),
       (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s : Sec F (Spec (CommRingCat.of B)))) := by
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (forget _)).obj F).property)
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.fst A B))
  let b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.snd A B))
  have ea : coprod.inl ≫ coprodSpec A B = a := coprodSpec_inl A B
  have eb : coprod.inr ≫ coprodSpec A B = b := coprodSpec_inr A B
  have hop : IsLimit (BinaryFan.mk a.op b.op) := by
    refine BinaryFan.IsLimit.mk _ (fun f g => (inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop).op) ?_ ?_ ?_
    · intro T f g
      apply Quiver.Hom.unop_inj
      change a ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = f.unop
      rw [← ea, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]
    · intro T f g
      apply Quiver.Hom.unop_inj
      change b ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = g.unop
      rw [← eb, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]
    · intro T f g m h₁ h₂
      apply Quiver.Hom.unop_inj
      have h₁' : a ≫ m.unop = f.unop := congrArg Quiver.Hom.unop h₁
      have h₂' : b ≫ m.unop = g.unop := congrArg Quiver.Hom.unop h₂
      rw [Quiver.Hom.unop_op, IsIso.eq_inv_comp]
      apply coprod.hom_ext
      · rw [coprod.inl_desc, reassoc_of% ea]
        exact h₁'
      · rw [coprod.inr_desc, reassoc_of% eb]
        exact h₂'
  have hl := (isLimitMapConeBinaryFanEquiv G a.op b.op) (isLimitOfPreserves G hop)
  let e := hl.conePointUniqueUpToIso (Types.binaryProductLimit _ _)
  have he := (isIso_iff_bijective e.hom).1 inferInstance
  exact he

private theorem free_iso {X Y Z : Scheme.{0}} (a : Y ⟶ X) (b : Z ⟶ X)
    (hb : ∀ F : Shv R, Function.Bijective fun s : Sec F X => ((Sec.res a s : Sec F Y), (Sec.res b s : Sec F Z))) :
    IsIso (biprod.desc ((free R).map (yoneda.map a)) ((free R).map (yoneda.map b))) := by
  let P₁ : PSh := yoneda.obj Y
  let P₂ : PSh := yoneda.obj Z
  let Q : PSh := yoneda.obj X
  let a' : (free R).obj P₁ ⟶ (free R).obj Q := (free R).map (yoneda.map a)
  let b' : (free R).obj P₂ ⟶ (free R).obj Q := (free R).map (yoneda.map b)
  let T : Shv R := (free R).obj P₁ ⊞ (free R).obj P₂
  let g₁ : Sec ((free R).obj P₁) Y := freeGen R P₁ _ (𝟙 _)
  let g₂ : Sec ((free R).obj P₂) Z := freeGen R P₂ _ (𝟙 _)
  let gQ : Sec ((free R).obj Q) X := freeGen R Q _ (𝟙 _)
  obtain ⟨s, hs⟩ := (hb T).2 (Sec.map biprod.inl g₁, Sec.map biprod.inr g₂)
  have hs₁ : Sec.res a s = Sec.map biprod.inl g₁ := congrArg Prod.fst hs
  have hs₂ : Sec.res b s = Sec.map biprod.inr g₂ := congrArg Prod.snd hs
  obtain ⟨hex, hext, hres, hmap⟩ := free_hom_sections R Q T
  obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res x s) (fun V U g x => (res_comp g x s).symm)
  have gen₁ : ∀ (U : Scheme.{0}) (x : U ⟶ Y), freeGen R P₁ U x = Sec.res x g₁ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₁ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have gen₂ : ∀ (U : Scheme.{0}) (x : U ⟶ Z), freeGen R P₂ U x = Sec.res x g₂ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₂ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have genQ : ∀ (U : Scheme.{0}) (x : U ⟶ X), freeGen R Q U x = Sec.res x gQ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R Q T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have ma : ∀ (U : Scheme.{0}) (x : U ⟶ Y), Sec.map a' (freeGen R P₁ U x) = freeGen R Q U (x ≫ a) :=
    fun U x => (free_hom_sections R P₁ T).2.2.2 Q (yoneda.map a) U x
  have mb : ∀ (U : Scheme.{0}) (x : U ⟶ Z), Sec.map b' (freeGen R P₂ U x) = freeGen R Q U (x ≫ b) :=
    fun U x => (free_hom_sections R P₂ T).2.2.2 Q (yoneda.map b) U x
  have hdφ₁ : a' ≫ φ = biprod.inl := by
    refine (free_hom_sections R P₁ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, ma, hφ, res_comp, hs₁, sec_nat, ← gen₁]
  have hdφ₂ : b' ≫ φ = biprod.inr := by
    refine (free_hom_sections R P₂ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, mb, hφ, res_comp, hs₂, sec_nat, ← gen₂]
  have hsQ : Sec.map (biprod.desc a' b') s = gQ := by
    refine (hb ((free R).obj Q)).1 (Prod.ext ?_ ?_)
    · change Sec.res a (Sec.map (biprod.desc a' b') s) = Sec.res a gQ
      rw [sec_nat, hs₁, ← sec_comp, biprod.inl_desc, ← genQ, ma]
      rfl
    · change Sec.res b (Sec.map (biprod.desc a' b') s) = Sec.res b gQ
      rw [sec_nat, hs₂, ← sec_comp, biprod.inr_desc, ← genQ, mb]
      rfl
  refine ⟨φ, ?_, ?_⟩
  · apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      exact hdφ₁
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      exact hdφ₂
  · refine (free_hom_sections R Q ((free R).obj Q)).2.1 _ _ fun U x => ?_
    change Sec.map (biprod.desc a' b') (Sec.map φ (freeGen R Q U x)) = freeGen R Q U x
    rw [hφ, ← sec_nat, hsQ, genQ]

end UpperTheory.SectionRestriction

theorem UpperTheory.twistedCohomology_specProd_bijective_prod :
    ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ), Function.Bijective fun x : Ht q (sp (A × B)) n i => (pull _ (spMap (RingHom.fst A B)) (tw q i) n x, pull _ (spMap (RingHom.snd A B)) (tw q i) n x) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.EtC.chains_disc_biprod_isIso (ZMod q) _ _ (UpperTheory.SectionRestriction.free_iso _ _ fun F => UpperTheory.SectionRestriction.sec_bij F A B)
  exact UpperTheory.SectionRestriction.split_bij ((chains (ZMod q)).map (spMap (RingHom.fst A B)))
    ((chains (ZMod q)).map (spMap (RingHom.snd A B))) h2 (tw q i) n
end

