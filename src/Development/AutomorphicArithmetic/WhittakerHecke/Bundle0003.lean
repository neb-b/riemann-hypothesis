module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.AutomorphicArithmetic.WhittakerHecke.SurjectiveEvalBlowupChartOfSpanEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.CechCocycleLineBundle
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma eval₂_scale {A S : Type*} [CommRing A] [CommRing S] {n : ℕ} (g : A →+* S)
    (x : Fin n → S) (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A} (ha : a.IsHomogeneous m) :
    eval₂ g (fun l => w * x l) a = w ^ m * eval₂ g x a :=
  _root_.UpperTheory.Reformulated.B.Qk57.eval₂_scale g x w ha

set_option backward.isDefEq.respectTransparency false in
private lemma homOfLE_appTop_topIso {W : Scheme.{0}} {U U' : W.Opens} (e : U' ≤ U) (x : Γ(W, U)) :
    (W.homOfLE e).appTop (U.topIso.inv x) = U'.topIso.inv (W.presheaf.map (homOfLE e).op x) := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun t => (W.presheaf.map t) x) (Subsingleton.elim _ _)

private noncomputable def rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    R →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop).hom

private lemma toSpecΓ_rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s)) = s := by
  refine ext_to_Spec ?_
  change (Scheme.ΓSpecIso _).inv ≫ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s))).appTop =
    (Scheme.ΓSpecIso _).inv ≫ s.appTop
  rw [ProjHom.specCorr_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private noncomputable def phi (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) :
    MvPolynomial (Fin (M + 1)) R →+* Γ(U, ⊤) :=
  eval₂Hom (U.ι.appTop.hom.comp (rho s)) fun l => U.topIso.inv (x l)

private lemma phi_X (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (l : Fin (M + 1)) :
    phi s U x (X l) = U.topIso.inv (x l) := by
  simp [phi]

private lemma phi_C (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (r : R) :
    phi s U x (C r) = U.ι.appTop (rho s r) := by
  simp [phi]

private lemma phi_irr (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    (HomogeneousIdeal.irrelevant (grading R M)).toIdeal.map (phi s U x) = ⊤ :=
  map_irrelevant_eq_top _ m (by rw [phi_X, hx, map_one]; exact isUnit_one)

private noncomputable def loc (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : U.toScheme ⟶ PSpace R M :=
  Proj.fromOfGlobalSections (grading R M) (phi s U x) (phi_irr s U x m hx)

private lemma loc_agree {U U' : W.Opens} (x : Fin (M + 1) → Γ(W, U)) (x' : Fin (M + 1) → Γ(W, U'))
    (m m' : Fin (M + 1)) (hx : x m = 1) (hx' : x' m' = 1)
    (hrel : ∀ l k, W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x l) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' k) =
      W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x k) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' l)) :
    W.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ loc s U x m hx =
      W.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ loc s U' x' m' hx' := by
  unfold loc
  rw [ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X,
    ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X]
  set ψ := (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop.hom.comp (phi s U x) with hψ
  set ψ' := (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop.hom.comp (phi s U' x') with hψ'
  have hX : ∀ l, ψ (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_left).op (x l)) :=
    fun l => by
      rw [hψ, RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hX' : ∀ l, ψ' (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_right).op (x' l)) :=
    fun l => by
      rw [hψ', RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hC : ∀ r, ψ (C r) = ψ' (C r) := fun r => by
    rw [hψ, hψ', RingHom.comp_apply, RingHom.comp_apply, phi_C, phi_C]
    change ((U.ι.appTop ≫ (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop) _) =
      ((U'.ι.appTop ≫ (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop) _)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have hm : ψ (X m) = 1 := by rw [hX, hx, map_one, map_one]
  have hm' : ψ' (X m') = 1 := by rw [hX', hx', map_one, map_one]
  have hrel' : ∀ l k, ψ (X l) * ψ' (X k) = ψ (X k) * ψ' (X l) := fun l k => by
    rw [hX, hX, hX', hX', ← map_mul, ← map_mul, hrel]
  have hw : IsUnit (ψ (X m')) :=
    IsUnit.of_mul_eq_one (ψ' (X m)) (by rw [← hrel' m m', hm, hm', one_mul])
  have hsc : ∀ l, ψ (X l) = ψ (X m') * ψ' (X l) := fun l => by
    rw [← hrel' l m', hm', mul_one]
  refine ProjHom.fromOfGlobalSections_eq_of_twist _ _ (fun l => X l) (fun _ => 1) (fun _ => one_pos)
    (fun l => X_mem l) iSup_basicOpen_X _ _ (ψ (X m')) hw fun d a ha => ?_
  have e1 : ψ = eval₂Hom (ψ'.comp C) fun l => ψ (X m') * ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp [hC]) (fun l => by simp [hsc l])
  have e2 : ψ' = eval₂Hom (ψ'.comp C) fun l => ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun l => by simp)
  calc ψ a = eval₂ (ψ'.comp C) (fun l => ψ (X m') * ψ' (X l)) a := by
        conv_lhs => rw [e1]
        rfl
    _ = ψ (X m') ^ d * eval₂ (ψ'.comp C) (fun l => ψ' (X l)) a := eval₂_scale _ _ _ ha
    _ = ψ (X m') ^ d * ψ' a := by
        congr 1
        conv_rhs => rw [e2]
        rfl
end

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private lemma rho_comp {Y : Scheme.{0}} (h : Y ⟶ W) (r : R) : rho (h ≫ s) r = h.appTop (rho s r) := by
  rw [rho, Scheme.Hom.comp_appTop]
  rfl

private lemma loc_str (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    loc s U x m hx ≫ PSpace.str R M = U.ι ≫ s := by
  unfold loc
  rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  conv_rhs => rw [← toSpecΓ_rho (U.ι ≫ s)]
  congr 2
  ext r
  refine Eq.trans ?_ (rho_comp s U.ι r).symm
  refine Eq.trans ?_ (phi_C s U x r)
  rfl

private lemma loc_preimage (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : loc s U x m hx ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) = ⊤ := by
  unfold loc
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (grading R M) _ _ one_pos (X_mem m), phi_X, hx,
    map_one]
  exact Scheme.basicOpen_of_isUnit _ isUnit_one

set_option backward.isDefEq.respectTransparency false in
private lemma loc_coord (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m l : Fin (M + 1))
    (hx : x m = 1) (g : U.toScheme ⟶ PSpace R M) (hg : g = loc s U x m hx)
    (e : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen (grading R M) (X m)) :
    g.appLE _ ⊤ e (chartHom m (X l)) = U.topIso.inv (x l) := by
  subst hg
  have hb : U.toScheme.basicOpen (phi s U x (X m)) = ⊤ := by
    rw [phi_X, hx, map_one]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have hmem : (X l : MvPolynomial (Fin (M + 1)) R) ∈ grading R M (1 • 1) := by
    simpa using X_mem l
  have key := ProjHom.corr_fromOfGlobalSections' (grading R M) (phi s U x) (phi_irr s U x m hx)
    one_pos (X_mem m) ⊤ hb e 1 (X l) hmem
  rw [ProjHom.corr_apply, phi_X, phi_X, hx, map_one, map_one, one_pow, mul_one,
    ProjHom.ι_appTop_eq] at key
  have key2 := congrArg (Scheme.Opens.topIso (⊤ : U.toScheme.Opens)).hom key
  simp only [Iso.inv_hom_id_apply] at key2
  rw [chartHom_of_mem m (X_mem l)]
  refine Eq.trans key2 ?_
  have : (homOfLE le_top : (⊤ : U.toScheme.Opens) ⟶ ⊤).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma appLE_ι {Y : Scheme.{0}} (f : W ⟶ Y) (O : Y.Opens) (U : W.Opens)
    (h : U ≤ f ⁻¹ᵁ O) (e : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ O) (y : Γ(Y, O)) :
    (U.ι ≫ f).appLE O ⊤ e y = U.topIso.inv (f.appLE O U h y) := by
  rw [← Scheme.Hom.appLE_comp_appLE U.ι f O U ⊤ h (by simp), CommRingCat.comp_apply,
    Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg (fun t => (W.presheaf.map t) (f.appLE O U h y)) (Subsingleton.elim _ _)
end

theorem UpperTheory.cech_cocycle_line_bundle :
    ∀ {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) (M : ℕ) {ι : Type}
        (V : ι → W.Opens), iSup V = ⊤ → ∀ (μ : ι → Fin (M + 1)) (c : ∀ i, Fin (M + 1) → Γ(W, V i)),
        (∀ i, c i (μ i) = 1) →
        (∀ i j l k, W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i l) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j k) =
          W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i k) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j l)) →
        ∃ f : W ⟶ PSpace R M, f ≫ PSpace.str R M = s ∧ ∀ i,
          ∃ h : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)), ∀ l,
            f.appLE _ (V i) h (chartHom (μ i) (X l)) = c i l := by
  intro R _ W s M ι V hV μ c h1 h2
  let cov := W.openCoverOfIsOpenCover V hV
  let fi : ∀ i, (V i).toScheme ⟶ PSpace R M := fun i => loc s (V i) (c i) (μ i) (h1 i)
  have hag : ∀ i j : ι, pullback.fst (cov.f i) (cov.f j) ≫ fi i =
      pullback.snd (cov.f i) (cov.f j) ≫ fi j := fun i j => by
    have H := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ fi i = pullback.snd (V i).ι (V j).ι ≫ fi j
    rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc, Category.assoc,
      loc_agree s (c i) (c j) (μ i) (μ j) (h1 i) (h1 j) (h2 i j)]
  let f : W ⟶ PSpace R M := cov.glueMorphisms fi hag
  have hι : ∀ i, (V i).ι ≫ f = fi i := fun i => cov.ι_glueMorphisms fi hag i
  refine ⟨f, ?_, fun i => ?_⟩
  · refine cov.hom_ext _ _ fun i => ?_
    have hi : (V i).ι ≫ f ≫ PSpace.str R M = (V i).ι ≫ s := by
      rw [← Category.assoc, hι i]
      exact loc_str s (V i) (c i) (μ i) (h1 i)
    exact hi
  · have hpre : ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) = ⊤ := by
      rw [hι i]
      exact loc_preimage s (V i) (c i) (μ i) (h1 i)
    have hle : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := fun x hx => by
      have hx' : (⟨x, hx⟩ : (V i).toScheme) ∈
          ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := by
        rw [hpre]
        trivial
      exact hx'
    refine ⟨hle, fun l => ?_⟩
    have h3 := appLE_ι f _ (V i) hle hpre.ge (chartHom (μ i) (X l))
    rw [loc_coord s (V i) (c i) (μ i) l (h1 i) _ (hι i) hpre.ge] at h3
    have h4 := congrArg (V i).topIso.hom h3
    simpa only [Iso.inv_hom_id_apply] using h4.symm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsBlowupAffineChartCoverOfSpanEq
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem chart_cover {R : Type} [CommRing R] (I : Ideal R) {M : ℕ} (a : Fin (M + 1) → ↥I)
    (h : Ideal.span (Set.range fun l => (a l : R)) = I) :
    ⨆ m, (affineBlowupChart I (a m) ''ᵁ ⊤) = ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange, opensRange_affineBlowupChart_eq_basicOpen]
  refine Proj.iSup_basicOpen_eq_top (reesGrading I) (fun m => reesGenerator I (a m)) ?_
  refine (reesGrading_irrelevant_le_span I).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  have hb : (b : R) ∈ Ideal.span (Set.range fun l => (a l : R)) := by rw [h]; exact b.2
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
  have hsum : reesGenerator I b = ∑ l, algebraMap R ↥(reesAlgebra I) (c l) * reesGenerator I (a l) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [reesGenerator_coe, ← hc, MulMemClass.coe_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show _ = Polynomial.C (c l) * _
    rw [Polynomial.C_mul_monomial]
  rw [SetLike.mem_coe, hsum]
  exact sum_mem fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)

private theorem chart_inter {R : Type} [CommRing R] (I : Ideal R) (a b : ↥I) :
    (affineBlowupChart I a ''ᵁ ⊤) ⊓ (affineBlowupChart I b ''ᵁ ⊤) =
      affineBlowupChart I a ''ᵁ PrimeSpectrum.basicOpen (chartFraction I a b) := by
  have hel : HomogeneousLocalization.Away.isLocalizationElem
        (reesGenerator_mem_reesGrading I a) (reesGenerator_mem_reesGrading I b)
      = chartFraction I a b := by
    apply HomogeneousLocalization.val_injective
    rw [chartFraction_eq_mk]
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.val_mk, pow_one]
  have hpre : affineBlowupChart I a ⁻¹ᵁ (affineBlowupChart I b).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I a b) := by
    rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι, ← hel]
    exact Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I a) Nat.one_pos
      (reesGenerator_mem_reesGrading I b) Nat.one_pos
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange]

private theorem fromSpec_appLE_top {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(Z, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(Z, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact CategoryTheory.Functor.map_id _ _

private theorem exists_open_emb {Z W : Scheme.{0}} (I : Z.IdealSheafData) (π : W ⟶ Z)
    (hπ : IsBlowupAlongIdealSheaf π I) (U : Z.affineOpens) :
    ∃ (j : affineBlowup (I.ideal U) ⟶ W) (_ : IsOpenImmersion j),
      j ≫ π = AffineBlowup.toSpec (I.ideal U) ≫ U.2.fromSpec ∧ j ''ᵁ ⊤ = π ⁻¹ᵁ U.1 := by
  have hU : IsAffineOpen U.1 := U.2
  haveI : IsOpenImmersion (IsAffineOpen.fromSpec U.2) := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hI : I.comap U.2.fromSpec = specIdealSheaf (I.ideal U) := by
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    have e : (⊤ : (Spec Γ(Z, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
      rw [U.2.fromSpec_preimage_self]
    have h5 : (I.comap U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
        Ideal.map (Scheme.ΓSpecIso Γ(Z, U.1)).inv.hom (I.ideal U) := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.2.fromSpec U ⟨⊤, isAffineOpen_top _⟩ e]
      have h6 := fromSpec_appLE_top U.2 e
      have h7 : ∀ f g : Γ(Z, U.1) ⟶ Γ(Spec Γ(Z, U.1), ⊤), f = g →
          Ideal.map f.hom (I.ideal U) = Ideal.map g.hom (I.ideal U) := by
        rintro f _ rfl
        rfl
      exact h7 _ _ h6
    exact h5.trans (specIdealSheaf_ideal_top (I.ideal U)).symm
  have h1 := hπ.pullback_snd_of_isOpenImmersion U.2.fromSpec
  rw [hI] at h1
  obtain ⟨e, he⟩ := (isBlowupAlongIdealSheaf_affineBlowup_toSpec (I.ideal U)).exists_iso h1
  refine ⟨e.hom ≫ pullback.fst π U.2.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  · rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Hom.opensRange_pullbackFst]
    exact congrArg (π ⁻¹ᵁ ·) hU.opensRange_fromSpec

private theorem sections_transfer {Z W : Scheme.{0}} (π : W ⟶ Z) (U : Z.affineOpens) {C : Type} [CommRing C]
    (φ : Γ(Z, U.1) →+* C) (ψ : Spec (CommRingCat.of C) ⟶ W) [IsOpenImmersion ψ]
    (hψ : ψ ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
    (le : ψ ''ᵁ ⊤ ≤ π ⁻¹ᵁ U.1) :
    ∃ e : Γ(W, ψ ''ᵁ ⊤) ≃+* C, (∀ x, e (π.appLE U.1 (ψ ''ᵁ ⊤) le x) = φ x) ∧
      ∀ z, W.basicOpen (e.symm z) = ψ ''ᵁ PrimeSpectrum.basicOpen z := by
  let E : Γ(W, ψ ''ᵁ ⊤) ≅ CommRingCat.of C := ψ.appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of C)
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · have hcat : π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ E.hom = CommRingCat.ofHom φ := by
      have h0 : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ψ ⁻¹ᵁ (ψ ''ᵁ ⊤) := fun x _ => ⟨x, trivial, rfl⟩
      have h1 : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (ψ ≫ π) ⁻¹ᵁ U.1 := fun x hx => le (h0 hx)
      have h2 : π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ (ψ.appIso ⊤).hom = (ψ ≫ π).appLE U.1 ⊤ h1 := by
        rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      have h3 : ∀ (f : Spec (CommRingCat.of C) ⟶ Z) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
          (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ f ⁻¹ᵁ U.1),
          f.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = CommRingCat.ofHom φ := by
        rintro f rfl h
        have h4 : (⊤ : (Spec Γ(Z, U.1)).Opens) ≤ (IsAffineOpen.fromSpec U.2) ⁻¹ᵁ U.1 := by
          rw [U.2.fromSpec_preimage_self]
        rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (IsAffineOpen.fromSpec U.2) U.1 ⊤ ⊤ h4 le_top, fromSpec_appLE_top U.2 h4]
        have h8 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop := by
          exact Scheme.Hom.appLE_eq_app _
        rw [h8, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      show π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ (ψ.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = _
      rw [← Category.assoc, h2]
      exact h3 _ hψ h1
    intro x
    exact congrArg (fun f => f.hom x) hcat
  · intro z
    have h2 : (Spec (CommRingCat.of C)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom z)
        = PrimeSpectrum.basicOpen z := basicOpen_eq_of_affine (R := CommRingCat.of C) z
    rw [← h2, Scheme.image_basicOpen]
    rfl

private theorem assemble {Z W A : Scheme.{0}} (π : W ⟶ Z) (U : Z.affineOpens) {M : ℕ}
    (g : Fin (M + 1) → Γ(Z, U.1)) (C : Fin (M + 1) → Type) [∀ m, CommRing (C m)]
    (φ : ∀ m, Γ(Z, U.1) →+* C m) (fr : ∀ m, Fin (M + 1) → C m)
    (j : A ⟶ W) [IsOpenImmersion j] (hjr : j ''ᵁ ⊤ = π ⁻¹ᵁ U.1)
    (ch : ∀ m, Spec (CommRingCat.of (C m)) ⟶ A) [∀ m, IsOpenImmersion (ch m)]
    (hch : ∀ m, ch m ≫ j ≫ π = Spec.map (CommRingCat.ofHom (φ m)) ≫ U.2.fromSpec)
    (heq : ∀ m l, φ m (g l) = fr m l * φ m (g m))
    (hnzd : ∀ m, φ m (g m) ∈ nonZeroDivisors (C m))
    (hsurj : ∀ m, Function.Surjective (MvPolynomial.eval₂Hom (φ m) (fr m)))
    (hcov : ⨆ m, (ch m ''ᵁ ⊤) = ⊤)
    (hint : ∀ m l, (ch m ''ᵁ ⊤) ⊓ (ch l ''ᵁ ⊤) = ch m ''ᵁ PrimeSpectrum.basicOpen (fr m l)) :
    ∃ (V : Fin (M + 1) → W.Opens) (le : ∀ m, V m ≤ π ⁻¹ᵁ U.1) (c : ∀ m, Fin (M + 1) → Γ(W, V m)),
          (∀ m, IsAffineOpen (V m)) ∧ iSup V = π ⁻¹ᵁ U.1 ∧
          (∀ m l, π.appLE U.1 (V m) (le m) (g l) = π.appLE U.1 (V m) (le m) (g m) * c m l) ∧
          (∀ m, c m m = 1) ∧
          (∀ m, π.appLE U.1 (V m) (le m) (g m) ∈ nonZeroDivisors Γ(W, V m)) ∧
          (∀ m, Function.Surjective (MvPolynomial.eval₂Hom (π.appLE U.1 (V m) (le m)).hom (c m))) ∧
          (∀ m l, V m ⊓ V l = W.basicOpen (c m l)) := by
  have himg : ∀ (m) (O : (Spec (CommRingCat.of (C m))).Opens),
      (ch m ≫ j) ''ᵁ O = j ''ᵁ (ch m ''ᵁ O) := fun m O => Scheme.Hom.comp_image _ _ _
  have hψ : ∀ m, (ch m ≫ j) ≫ π = Spec.map (CommRingCat.ofHom (φ m)) ≫ U.2.fromSpec := by
    intro m
    rw [Category.assoc, hch]
  have hle : ∀ m, (ch m ≫ j) ''ᵁ ⊤ ≤ π ⁻¹ᵁ U.1 := by
    intro m
    rw [himg, ← hjr]
    exact (j.opensFunctor).monotone le_top
  choose e he1 he2 using fun m => sections_transfer π U (φ m) (ch m ≫ j) (hψ m) (hle m)
  have key : ∀ m x, π.appLE U.1 ((ch m ≫ j) ''ᵁ ⊤) (hle m) x = (e m).symm (φ m x) := by
    intro m x
    rw [← he1 m x, RingEquiv.symm_apply_apply]
  have hone : ∀ m, fr m m = 1 := by
    intro m
    have h1 : (fr m m - 1) * φ m (g m) = 0 := by rw [sub_mul, ← heq, one_mul, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp (hnzd m)) _ h1)
  refine ⟨fun m => (ch m ≫ j) ''ᵁ ⊤, hle, fun m l => (e m).symm (fr m l), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact (isAffineOpen_top _).image_of_isOpenImmersion (ch m ≫ j)
  · apply le_antisymm
    · exact iSup_le fun m => hle m
    · rw [← hjr]
      rintro x ⟨y, -, rfl⟩
      have hy : y ∈ ⨆ m, ch m ''ᵁ ⊤ := hcov ▸ trivial
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨m, ?_⟩
      rw [himg]
      exact ⟨y, hm, rfl⟩
  · intro m l
    rw [key, key, heq, map_mul, mul_comm]
  · intro m
    simp only [hone, map_one]
  · intro m
    rw [key]
    refine mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_
    have h1 := congrArg (e m) hy
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    exact (map_eq_zero_iff _ (e m).injective).mp ((mem_nonZeroDivisors_iff_right.mp (hnzd m)) _ h1)
  · intro m
    have hcomp : (MvPolynomial.eval₂Hom (π.appLE U.1 ((ch m ≫ j) ''ᵁ ⊤) (hle m)).hom (fun l => (e m).symm (fr m l)))
        = (e m).symm.toRingHom.comp (MvPolynomial.eval₂Hom (φ m) (fr m)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [key]
      · intro i
        simp
    rw [hcomp]
    exact (e m).symm.surjective.comp (hsurj m)
  · intro m l
    have hinf : ∀ P Q : A.Opens, j ''ᵁ P ⊓ j ''ᵁ Q = j ''ᵁ (P ⊓ Q) := by
      intro P Q
      apply TopologicalSpace.Opens.ext
      exact (Set.image_inter j.isOpenEmbedding.injective).symm
    refine Eq.trans ?_ (he2 m (fr m l)).symm
    calc (ch m ≫ j) ''ᵁ ⊤ ⊓ (ch l ≫ j) ''ᵁ ⊤ = j ''ᵁ (ch m ''ᵁ ⊤) ⊓ j ''ᵁ (ch l ''ᵁ ⊤) := by
          rw [himg, himg]
      _ = j ''ᵁ (ch m ''ᵁ ⊤ ⊓ ch l ''ᵁ ⊤) := hinf _ _
      _ = j ''ᵁ (ch m ''ᵁ PrimeSpectrum.basicOpen (fr m l)) := by rw [hint]
      _ = _ := (himg m _).symm

theorem UpperTheory.exists_blowup_affine_chart_cover_of_span_eq :
    ∀ {Z W : Scheme.{0}} (I : Z.IdealSheafData) (π : W ⟶ Z), IsBlowupAlongIdealSheaf π I → ∀ (U : Z.affineOpens) {M : ℕ} (g : Fin (M + 1) → Γ(Z, U.1)),
        Ideal.span (Set.range g) = I.ideal U →
        ∃ (V : Fin (M + 1) → W.Opens) (le : ∀ m, V m ≤ π ⁻¹ᵁ U.1) (c : ∀ m, Fin (M + 1) → Γ(W, V m)),
          (∀ m, IsAffineOpen (V m)) ∧ iSup V = π ⁻¹ᵁ U.1 ∧
          (∀ m l, π.appLE U.1 (V m) (le m) (g l) = π.appLE U.1 (V m) (le m) (g m) * c m l) ∧
          (∀ m, c m m = 1) ∧
          (∀ m, π.appLE U.1 (V m) (le m) (g m) ∈ nonZeroDivisors Γ(W, V m)) ∧
          (∀ m, Function.Surjective (MvPolynomial.eval₂Hom (π.appLE U.1 (V m) (le m)).hom (c m))) ∧
          (∀ m l, V m ⊓ V l = W.basicOpen (c m l)) := by
  intro Z W I π hπ U M g hg
  have hgm : ∀ l, g l ∈ I.ideal U := fun l => hg ▸ Ideal.subset_span ⟨l, rfl⟩
  let a : Fin (M + 1) → ↥(I.ideal U) := fun l => ⟨g l, hgm l⟩
  obtain ⟨j, hj, hjπ, hjr⟩ := exists_open_emb I π hπ U
  refine assemble π U g (fun m => HomogeneousLocalization.Away (reesGrading (I.ideal U)) (reesGenerator (I.ideal U) (a m)))
    (fun m => chartRingHom (I.ideal U) (a m)) (fun m l => chartFraction (I.ideal U) (a m) (a l)) j hjr
    (fun m => affineBlowupChart (I.ideal U) (a m)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro m
    rw [hjπ, ← Category.assoc, affineBlowupChart_comp_toSpec]
  · exact fun m l => chartRingHom_coe_eq_chartFraction_mul (I.ideal U) (a m) (a l)
  · exact fun m => chartRingHom_mem_nonZeroDivisors (I.ideal U) (a m)
  · exact fun m => UpperTheory.surjective_eval_blowupChart_of_span_eq _ a hg m
  · exact chart_cover _ a hg
  · exact fun m l => chart_inter _ _ _
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IsUnitChartCoordAndHomogeneousChartTransition
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_chart_overlap {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N)
    (O : W.Opens) (a b : Fin (N + 1))
    (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))
    (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b))
    (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F ∈ grading R N (n • 1)) :
    h.appLE _ O ha (chartHom a F) *
        h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
      h.appLE _ O hb (chartHom b F) := by
  have hO : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [Proj.basicOpen_mul]
    exact fun x hx => ⟨hb hx, ha hx⟩
  have e1 : h.appLE _ O ha =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_right a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have e2 : h.appLE _ O hb =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_left a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have hF' : F ∈ grading R N n := by simpa using hF
  rw [e1, e2]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [chartHom_of_mem a hF']
  exact map_mul_pow_eq _ _ (chart_identity a b hF)

theorem UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition :
    ∀ {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N) (O : W.Opens) (a b : Fin (N + 1))
        (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b)),
        IsUnit (h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R))) ∧
        ∀ (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R), F.IsHomogeneous n →
          h.appLE _ O ha (chartHom a F) * h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
            h.appLE _ O hb (chartHom b F) := by
  intro R _ N W h O a b ha hb
  refine ⟨?_, fun n F hF => projective_chart_overlap h O a b ha hb n F ?_⟩
  · have key := projective_chart_overlap h O a b ha hb 1 (X b) (by simpa using X_mem b)
    rw [pow_one, chartHom_X_self, map_one] at key
    exact IsUnit.of_mul_eq_one_right _ key
  · have : F ∈ grading R N n := hF
    simpa using this
end

