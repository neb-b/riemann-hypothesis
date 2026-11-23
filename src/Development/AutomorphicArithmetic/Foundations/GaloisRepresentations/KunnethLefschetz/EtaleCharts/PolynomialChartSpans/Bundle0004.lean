module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordBC
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_pushout {K K' B B' : Type} [CommRing K] [CommRing K'] [CommRing B] [CommRing B']
    (φ : K →+* K') (s : K →+* B) (s' : K' →+* B') (t : B →+* B')
    (po : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom s) (CommRingCat.ofHom s') (CommRingCat.ofHom t))
    (σ : Type) (x : σ → B) (hE : (MvPolynomial.eval₂Hom s x).Etale) :
    (MvPolynomial.eval₂Hom s' fun i => t (x i)).Etale := by
  have hl : IsPushout (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (MvPolynomial.map φ : MvPolynomial σ K →+* MvPolynomial σ K'))
      (CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K')) := by
    letI := φ.toAlgebra
    letI : Algebra (MvPolynomial σ K) (MvPolynomial σ K') := MvPolynomial.algebraMvPolynomial
    exact ((CommRingCat.isPushout_iff_isPushout (R := K) (S := MvPolynomial σ K) (R' := K')
      (S' := MvPolynomial σ K')).mpr inferInstance).flip
  have e1 : CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s x) = CommRingCat.ofHom s := by
    ext a
    simp
  have e2 : CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K') ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i)) = CommRingCat.ofHom s' := by
    ext a
    simp
  have big : IsPushout (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s x)) (CommRingCat.ofHom φ) (CommRingCat.ofHom t)
      (CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K') ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i))) := by
    rw [e1, e2]
    exact po.flip
  have hw : ∀ a, t (s a) = s' (φ a) := fun a => by
    have := congrArg (fun f => f.hom a) po.w
    simpa using this.symm
  have p : CommRingCat.ofHom (MvPolynomial.eval₂Hom s x) ≫ CommRingCat.ofHom t =
      CommRingCat.ofHom (MvPolynomial.map φ : MvPolynomial σ K →+* MvPolynomial σ K') ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i)) := by
    ext1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hw]
    · intro i
      simp
  have r := big.of_left p hl
  have hP : (RingHom.toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) =>
      f.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := RingHom.toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) => f.Etale)
    r.flip hE

theorem coordBC : UpperTheory.Gal.KunnethLefschetz.G.CoordBC := by
  intro K K' _ _ φ Z Z' q q' a hpb V hV σ x hE
  haveI : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hU : IsAffineOpen (a ⁻¹ᵁ V) := hV.preimage a
  refine ⟨hU, ?_⟩
  have hUY : a ⁻¹ᵁ V = a ⁻¹ᵁ V ⊓ q' ⁻¹ᵁ ⊤ := by simp
  have h1 : (⊤ : (Spec (CommRingCat.of K')).Opens) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤ := le_top
  have h2 : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hI := isIso_pushoutSection_of_isAffineOpen hpb h1 h2 hUY (isAffineOpen_top _) (isAffineOpen_top _) hV
  have sq := ((isIso_pushoutSection_iff hpb h1 h2 hUY).mp hI).flip
  have sq' : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Pb.strV q V))
      (CommRingCat.ofHom (Pb.strV q' (a ⁻¹ᵁ V))) (CommRingCat.ofHom (Scheme.Hom.app a V).hom) := by
    refine sq.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Scheme.ΓSpecIso_naturality]
      simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Pb.strV]
    · simp [Pb.strV]
    · simp [Scheme.Hom.app_eq_appLE]
  exact etale_pushout φ (Pb.strV q V) (Pb.strV q' (a ⁻¹ᵁ V)) (Scheme.Hom.app a V).hom sq' σ x hE

end UpperTheory.Gal.KunnethLefschetz.G
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.OKDvr
section
theorem UpperTheory.Gal.KunnethLefschetz.G.oKDvr :
    UpperTheory.Gal.KunnethLefschetz.G.OKDvr := by
  intro l _ K _
  have hK : (CrystallineSemistableComparison.OK l K) = (integralClosure ℤ_[l] K).toSubring := by
    ext x
    constructor
    · intro hx
      have h1 : ‖(x : PadicAlgCl l)‖ ≤ 1 := hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := UpperTheory.V.Lib.Small.isIntegral_of_norm_le h1
      exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 h2
    · intro hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := IsIntegral.map (K.val.restrictScalars ℤ_[l]) hx
      exact UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l _ h2
  rw [hK]
  exact (IsIntegralClosure.isNoetherianRing ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PresBC
section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem presAlg {A B A' B' : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ A') (g' : B ⟶ B') (f' : A' ⟶ B')
    (po : IsPushout f g g' f') {σ : Type} (u : σ → B) (S : Set (MvPolynomial σ A))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom f.hom u))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom f.hom u) = Ideal.span S) :
    Function.Surjective (MvPolynomial.eval₂Hom f'.hom fun s => g'.hom (u s)) ∧
      RingHom.ker (MvPolynomial.eval₂Hom f'.hom fun s => g'.hom (u s)) =
        Ideal.span (MvPolynomial.map g.hom '' S) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = MvPolynomial.eval₂Hom f.hom u := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = MvPolynomial.eval₂Hom f'.hom (fun s => g'.hom (u s)) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Ideal (MvPolynomial σ A'), I = Ideal.span (MvPolynomial.map g.hom '' S) := ⟨_, rfl⟩
  rw [← hφ] at hs hk
  rw [← hΦ, ← hI]
  have hw : ∀ a, f'.hom (g.hom a) = g'.hom (f.hom a) := fun a => by
    have h := congrArg (fun k => k.hom a) po.w
    simpa using h.symm
  have key : Φ.comp (MvPolynomial.map g.hom) = g'.hom.comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hΦ, hφ, hw]
    · intro s
      simp [hΦ, hφ]
  have key' : ∀ p, Φ (MvPolynomial.map g.hom p) = g'.hom (φ p) := fun p => by
    simpa using congrArg (fun k => k p) key
  have hle : Ideal.span S ≤ I.comap (MvPolynomial.map g.hom) :=
    Ideal.span_le.2 fun s hs' => by
      rw [hI]
      exact Ideal.subset_span ⟨s, hs', rfl⟩
  have hIΦ : ∀ x ∈ I, Φ x = 0 := by
    intro x hx
    have hle2 : I ≤ RingHom.ker Φ := by
      rw [hI]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨s, hs', rfl⟩
      have hs0 : φ s = 0 := by
        have : s ∈ RingHom.ker φ := hk ▸ Ideal.subset_span hs'
        exact this
      show Φ _ = 0
      rw [key', hs0, map_zero]
    exact hle2 hx
  let ψ : MvPolynomial σ A →+* (MvPolynomial σ A' ⧸ I) := (Ideal.Quotient.mk I).comp (MvPolynomial.map g.hom)
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro x hx
    rw [hk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hle hx)
  let r : B →+* (MvPolynomial σ A' ⧸ I) := RingHom.liftOfSurjective φ hs ⟨ψ, hker⟩
  have hr : ∀ p, r (φ p) = ψ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply φ _ _ ⟨ψ, hker⟩ p
  let q : A' →+* (MvPolynomial σ A' ⧸ I) := (Ideal.Quotient.mk I).comp MvPolynomial.C
  have hrq : ∀ a, r (f.hom a) = q (g.hom a) := fun a => by
    have h1 : φ (MvPolynomial.C a) = f.hom a := by simp [hφ]
    rw [← h1, hr]
    simp [ψ, q]
  let d : B' ⟶ CommRingCat.of (MvPolynomial σ A' ⧸ I) :=
    po.desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a)
  have hd1 : ∀ b, d.hom (g'.hom b) = r b := fun b => by
    exact congrArg (fun k => k.hom b) (po.inl_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a))
  have hd2 : ∀ a, d.hom (f'.hom a) = q a := fun a => by
    exact congrArg (fun k => k.hom a) (po.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a))
  let e : (MvPolynomial σ A' ⧸ I) →+* B' := Ideal.Quotient.lift I Φ hIΦ
  have he : ∀ x, e (Ideal.Quotient.mk I x) = Φ x := fun x => Ideal.Quotient.lift_mk I Φ hIΦ
  have hde : ∀ x, d.hom (e x) = x := by
    have h : d.hom.comp e = RingHom.id _ := by
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        have h1 : Φ (MvPolynomial.C a) = f'.hom a := by simp [hΦ]
        simp only [RingHom.comp_apply, he, h1, hd2]
        simp [q]
      · intro s
        have h1 : Φ (MvPolynomial.X s) = g'.hom (u s) := by simp [hΦ]
        have h2 : φ (MvPolynomial.X s) = u s := by simp [hφ]
        simp only [RingHom.comp_apply, he, h1, hd1]
        rw [← h2, hr]
        simp [ψ]
    exact fun x => congrArg (fun k => k x) h
  have hed : d ≫ CommRingCat.ofHom e = 𝟙 B' := by
    apply po.hom_ext
    · ext b
      obtain ⟨p, rfl⟩ := hs b
      have h0 : e (ψ p) = g'.hom (φ p) := by
        show e (Ideal.Quotient.mk I _) = _
        rw [he, key']
      simp [hd1, hr, h0]
    · ext a
      have h0 : e (q a) = f'.hom a := by
        show e (Ideal.Quotient.mk I _) = _
        rw [he]
        simp [hΦ]
      simp [hd2, h0]
  have hed' : ∀ b, e (d.hom b) = b := fun b => by
    have h := congrArg (fun k => k.hom b) hed
    simpa using h
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (d.hom b)
    exact ⟨p, by rw [← he, hp, hed']⟩
  · ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      have h0 : Ideal.Quotient.mk I x = 0 := by
        rw [← hde (Ideal.Quotient.mk I x), he, hx, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.1 h0
    · exact hIΦ x

theorem presBC : PresBC := by
  intro Y Z Y' Z' π π' a c H V C h hV hC hV' h' σ u S hs hk
  have hUY : c ⁻¹ᵁ C = c ⁻¹ᵁ C ⊓ π' ⁻¹ᵁ (a ⁻¹ᵁ V) := le_antisymm (le_inf le_rfl h') inf_le_left
  have po := (isIso_pushoutSection_iff H (US := V) (UT := a ⁻¹ᵁ V) (UX := C) le_rfl h hUY).1
    (isIso_pushoutSection_of_isAffineOpen H le_rfl h hUY hV hV' hC)
  have res := presAlg _ _ _ _ po u S hs hk
  have hcapp : (c.app C).hom = (c.appLE C (c ⁻¹ᵁ C) le_rfl).hom := by
    rw [Scheme.Hom.app_eq_appLE]
  have haapp : (a.app V).hom = (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom := by
    rw [Scheme.Hom.app_eq_appLE]
  refine ⟨?_, ?_, ?_⟩
  · have hs1 : IsPullback ((c ⁻¹ᵁ C).ι ≫ π') (c ∣_ C) a (C.ι ≫ π) :=
      ((isPullback_morphismRestrict c C).paste_vert H).flip
    have hs2 : IsPullback (π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ⁻¹ᵁ V).ι) (c ∣_ C) a
        (π.resLE V C h ≫ V.ι) := by
      rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
      exact hs1
    have hcomm : π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ∣_ V) = (c ∣_ C) ≫ π.resLE V C h := by
      rw [← cancel_mono V.ι]
      have e1 := (isPullback_morphismRestrict a V).w
      simp only [Category.assoc, e1, Scheme.Hom.resLE_comp_ι]
      exact hs2.w.trans (by simp)
    have hsq := IsPullback.of_right hs2 hcomm (isPullback_morphismRestrict a V).flip
    haveI : IsAffine (V : Scheme) := hV
    haveI : IsAffine (a ⁻¹ᵁ V : Scheme) := hV'
    haveI : IsAffine (C : Scheme) := hC
    exact IsAffine.of_isIso hsq.isoPullback.hom
  · rw [hcapp] at *
    exact res.1
  · rw [hcapp, haapp]
    exact res.2

end UpperTheory.Gal.KunnethLefschetz.G
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SubstXZero
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Etale)
    (σ : Type) : (MvPolynomial.map (σ := σ) φ).Etale := by
  algebraize [φ]
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := B)
  have h : Algebra.IsPushout A (MvPolynomial σ A) B (MvPolynomial σ B) := inferInstance
  haveI := h.symm
  exact RingHom.Etale.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hφ

private theorem etale_open {R : Type} [CommRing R] (U : (Spec (CommRingCat.of R)).Opens)
    (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale := by
  have h0 : (Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale :=
    HasRingHomProperty.appLE @Etale (𝟙 _) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  exact RingHom.Etale.respectsIso.right _
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h0

private def subst (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    MvPolynomial (Fin (D + 1)) O →+* MvPolynomial (Fin D) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X :
    Fin (D + 1) → MvPolynomial (Fin D) O)).toRingHom

private theorem subst_C (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (r : O) :
    subst O ϖ D (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [subst]

private theorem subst_X_zero (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    subst O ϖ D (MvPolynomial.X 0) = MvPolynomial.C ϖ := by
  simp [subst]

private theorem subst_X_succ (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (i : Fin D) :
    subst O ϖ D (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [subst]

private theorem prod_first (O : Type) [CommRing O] (D : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1), MvPolynomial.X i) =
      (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) O) := by
  have h : Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp only [Fin.val_zero]; omega⟩
  rw [h, Finset.prod_singleton]

private def modelEquiv (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    (MvPolynomial (Fin (D + 1)) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1),
        MvPolynomial.X i) - MvPolynomial.C ϖ))) ≃+* MvPolynomial (Fin D) O :=
  RingEquiv.ofRingHom
    (Ideal.Quotient.lift _ (subst O ϖ D) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [prod_first, map_mul, map_sub, subst_X_zero, subst_C, sub_self, mul_zero]))
    ((Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ).toRingHom)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [subst_C]
      · simp [subst_X_succ])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [subst_C]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, subst_X_zero, RingHom.id_apply]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_C]
          refine (Ideal.Quotient.eq.mpr ?_).symm
          rw [prod_first]
          exact Ideal.mem_span_singleton_self _
        · simp [subst_X_succ])

theorem smSst : SmSst := by
  intro O _ ϖ X p _ x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth p x
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  have hf := etale_open (R := O) U hU
  refine ⟨V, hV, hx, n + 1, 1, le_rfl, by omega,
    (g.comp (MvPolynomial.map ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom)).comp
        (modelEquiv O ϖ n).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (modelEquiv O ϖ n).bijective)
      (RingHom.Etale.stableUnderComposition _ _ (etale_map _ hf _) hg)
  · refine RingHom.ext fun r => ?_
    have e1 : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top ≫
        Scheme.Hom.appLE p U V e = Scheme.Hom.appLE p ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE p (𝟙 _) ⊤ U V le_top e).trans ?_
      simp
    have e2 := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom r)) e1
    have e3 := RingHom.congr_fun hgC (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom r)
    have e4 : (modelEquiv O ϖ n) (algebraMap O _ r) = MvPolynomial.C r := subst_C O ϖ n r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e4, MvPolynomial.map_C]
    exact e3.trans e2

end UpperTheory.Gal.KunnethLefschetz.G
end
end

