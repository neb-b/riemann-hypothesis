module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0004
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafNbPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.NbPf

variable {A B : Type} [CommRing A] [CommRing B]

def psi (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    B →+* A ⧸ I :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))

theorem psi_comp (φ : A →+* B) (I : Ideal A) (hb) : (psi φ I hb).comp φ = Ideal.Quotient.mk I := by
  ext a
  simp only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.symm_apply_eq]
  simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]

theorem isPushout_psi (φ : A →+* B) (I : Ideal A) (hb) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (psi φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  refine ⟨⟨by ext a; simpa using congrArg (fun f => f a) (psi_comp φ I hb)⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => s.inr) ?_ ?_ ?_⟩⟩
  · intro s
    have hk : I.map φ ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      have := congrArg (fun f => f.hom i) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr hi]
    ext b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (psi φ I hb b)
    have e1 : Ideal.Quotient.mk (I.map φ) (φ a) = Ideal.Quotient.mk (I.map φ) b := by
      have : (RingEquiv.ofBijective _ hb) (psi φ I hb b) = Ideal.Quotient.mk (I.map φ) b := by
        simp [psi]
      rw [← this, ← ha]; simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq] at e1
    have e2 : s.inl.hom (φ a) = s.inl.hom b := by
      have := hk e1; rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e3 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ← ha]
    rw [← e2, e3]
  · intro s; simp
  · intro s m _ h2; simpa using h2

theorem nb (hE : LeafExc) : Cl.LeafNb := by
  intro hA1 q A B _ _ φ I J hN hJ h
  subst hJ
  obtain ⟨he, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr he
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_psi φ I hb)
  rw [Spec.map_id] at hP
  refine hE hA1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (psi φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hP (off B (I.map φ)) (off A I) ?_ (Cl.off_map φ I)
  change (PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _
  congr 1
  have hr := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hr
  rw [← hr]; rfl

end LateralTheory.CohomologicalPurity.NbPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafNbhdExcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def nbhdRet {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) : B →+* A ⧸ I :=
  ((RingEquiv.ofBijective _ hb).symm : (B ⧸ I.map φ) →+* A ⧸ I).comp (Ideal.Quotient.mk (I.map φ))

theorem nbhdRet_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) (a : A) :
    nbhdRet φ I hb (φ a) = Ideal.Quotient.mk I a := by
  unfold nbhdRet
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  simp [Ideal.quotientMap_mk]

theorem nbhd_isPushout {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (nbhdRet φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  have w : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (nbhdRet φ I hb) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ 𝟙 (CommRingCat.of (A ⧸ I)) := by
    ext a; simp [nbhdRet_comp]
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk _ (fun s => s.inr) ?_ ?_ ?_)
  · intro s
    ext b
    obtain ⟨x, hx⟩ := hb.2 (Ideal.Quotient.mk (I.map φ) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have hker : ∀ y ∈ I.map φ, s.inl y = 0 := by
      intro y hy
      have hle : I.map φ ≤ RingHom.ker s.inl.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro i hi
        have := congrArg (fun g => g.hom i) s.condition
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [Ideal.mem_comap, RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]
      exact hle hy
    have h1 : s.inl b = s.inl (φ a) := by
      have := hker _ hx
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    have h2 := congrArg (fun g => g.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    have h3 : nbhdRet φ I hb b = Ideal.Quotient.mk I a := by
      unfold nbhdRet
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
      exact (Ideal.Quotient.eq.2 hx).symm
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [h3, h1, h2]
  · intro s; simp
  · intro s m h1 h2
    simpa using h2

theorem nbhd_isPullback {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPullback (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb))) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  have := isPullback_SpecMap_of_isPushout _ _ _ _ (nbhd_isPushout φ I hb)
  simpa using this

theorem range_spec_quot {A : Type} [CommRing A] (I : Ideal A) :
    (off A I : Set (Spec (CommRingCat.of A))) = (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))ᶜ := by
  ext x
  change x ∈ (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ↔ x ∈ (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)))ᶜ
  rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I)), Ideal.mk_ker]

theorem leafNbhdExc_of (hE : LeafExc) : LeafNbhdExc := by
  intro a1 q A B _ _ φ I hN hq h
  obtain ⟨het, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.2 het
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact hE a1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (nbhd_isPullback φ I hb) _ _ (range_spec_quot I)
    (off_map φ I)

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem chart_of_data (hS : LeafSec) {d : ℕ} {A T : Type} [CommRing A] [CommRing T] (I : Ideal A) (x : Fin d → A)
    (ι : A →+* T) (κ : MvPolynomial (Fin d) (A ⧸ I) →+* T) (μ : T →+* A ⧸ I)
    (hι : ι.Etale) (hκ : κ.Etale) (hμι : μ.comp ι = Ideal.Quotient.mk I)
    (hμκ : μ.comp κ = MvPolynomial.constantCoeff) (hx : ∀ j, ι (x j) = κ (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  obtain ⟨t, ht1, ht⟩ := hS A T ι I μ hι hμι
  have hu : IsUnit (algebraMap T (Localization.Away t) t) := IsLocalization.Away.algebraMap_isUnit t
  have hloc : (algebraMap T (Localization.Away t)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)
  have hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a := fun a => RingHom.congr_fun hμι a
  have hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q := fun q => RingHom.congr_fun hμκ q
  have key : ∀ s : T, μ s = 0 →
      algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι) := by
    intro s hs
    have h1 := Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)
    rw [Ideal.map_map, map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have hut : IsUnit (μ t) := by rw [ht1]; exact isUnit_one
  let μB : Localization.Away t →+* A ⧸ I := IsLocalization.Away.lift t hut
  have hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a := by
    intro a
    simp only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']
  refine ⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι,
    (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩,
    RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩
  · apply Ideal.quotientMap_injective'
    intro a ha
    have hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have := hker (Ideal.mem_comap.mp ha)
    rw [RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers t) b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (μ s)
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    have e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) t) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _)]
      refine Ideal.Quotient.eq.mpr ?_
      have := key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])
      simpa [map_sub] using this
    have e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) s) =
        Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a) := by
      refine Ideal.Quotient.eq.mpr ?_
      have := key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])
      simpa [map_sub] using this
    simp only at hbn
    rw [← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]
  · rw [show I.map ((algebraMap T (Localization.Away t)).comp ι) =
        (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI],
      Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [hx]
  · intro a
    have := key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a)))
      (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])
    simpa [map_sub] using this

theorem chart_of_tensor (hS : LeafSec) {d : ℕ} {P A Q : Type} [CommRing P] [CommRing A] [CommRing Q] [Algebra P A]
    [Algebra P Q] (I : Ideal A) (x : Fin d → A) (c : MvPolynomial (Fin d) (A ⧸ I) ≃+* Q) [Algebra.Etale P A]
    [Algebra.Etale P Q]
    (hcomm : ∀ p, MvPolynomial.constantCoeff (c.symm (algebraMap P Q p)) = Ideal.Quotient.mk I (algebraMap P A p))
    (px : Fin d → P) (hpx1 : ∀ j, algebraMap P A (px j) = x j)
    (hpx2 : ∀ j, algebraMap P Q (px j) = c (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  let f : A →ₐ[P] A ⧸ I := Ideal.Quotient.mkₐ P I
  have hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) =
      algebraMap P (A ⧸ I) p := fun p => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]; exact hcomm p
  let g : Q →ₐ[P] A ⧸ I := { MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }
  let μ := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let ι := algebraMap A (A ⊗[P] Q)
  let κ := ((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom
  have hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q := fun q => by
    simp [κ, Algebra.TensorProduct.comm_tmul]
  refine chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective)
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance)
        (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))
  · ext a; simp [μ, ι, f, g]
  · apply RingHom.ext; intro q; simp [μ, hκa, f, g]
  · intro j
    rw [hκa]
    show x j ⊗ₜ 1 = _
    rw [← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q),
      TensorProduct.smul_tmul]

theorem LeafNbhd_of (hS : LeafSec) (hP : LeafPoly) : LeafNbhd := by
  intro e d R A _ _ φ I x y hc
  have hπ := hP e d R A φ I x y hc
  set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα
  set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
    ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i))))
    with hπdef
  have hxI : ∀ j, x j ∈ I := fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [π, α]
    · intro i
      rcases i with j | i
      · simp [π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]
      · simp [π, α]
  exact @chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra
    (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp)
    (fun j => by show π _ = _; rw [hπdef]; simp) hc.2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPickPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem pick_span_top (A M K : Type) [CommRing A] [AddCommGroup M] [Module A M] [Field K] [Algebra A K] :
    Submodule.span K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add a c ha hc => exact add_mem (ha trivial) (hc trivial)

theorem LeafPick_of : LeafPick := by
  intro d A M _ _ _ _ p _ hd
  set K := p.ResidueField
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)
  rw [pick_span_top] at hbspan
  let B : Module.Basis b K (K ⊗[A] M) := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by rw [← hd, Module.finrank_eq_card_basis B]
  let B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  have hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i := by
    intro i
    have : B' i ∈ b := by simp [B', B]
    obtain ⟨m, hm⟩ := hbs this
    exact ⟨m, hm⟩
  choose x hx using hmem
  set N := Submodule.span A (Set.range x)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := (N.mkQ).baseChange K
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)
  have hg0 : ∀ v, g v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range B') := by rw [B'.span_eq]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      rw [← hx i]
      simp [g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro r a _ ha; simp [ha]
  have hsub : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor; intro u w
    obtain ⟨u', rfl⟩ := hgsurj u
    obtain ⟨w', rfl⟩ := hgsurj w
    rw [hg0, hg0]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro h
    exact (not_nontrivial_iff_subsingleton.2 hsub) h
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.1 hnot
  refine ⟨x, f, hfp, fun m => ?_⟩
  rw [SetLike.mem_coe, Module.mem_annihilator] at hf
  have := hf (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf
section
noncomputable section
open MvPolynomial TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafPolyPf

theorem one_tmul_algebraMap {P S A : Type} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A]
    (p : P) : (1 : S) ⊗ₜ[P] algebraMap P A p = algebraMap P S p ⊗ₜ[P] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def kap (d e : ℕ) (R : Type) [CommRing R] :
    MvPolynomial (Fin d ⊕ Fin e) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin e) R) :=
  eval₂Hom (C.comp C) (Sum.elim 0 fun i => C (X i))

theorem leafPoly : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  intro e d R A _ _ φ I x y h
  obtain ⟨hψ, hI⟩ := h
  set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef
  let P := MvPolynomial (Fin d ⊕ Fin e) R
  let S := MvPolynomial (Fin d) (MvPolynomial (Fin e) R)
  let Cc := MvPolynomial (Fin d) (A ⧸ I)
  letI : Algebra P A := ψ.toAlgebra
  letI : Algebra P S := (kap d e R).toAlgebra
  letI : Algebra S (S ⊗[P] A) := Algebra.TensorProduct.leftAlgebra (R := P) (A := S) (B := A)
  have hb : (algebraMap S (S ⊗[P] A)).Etale :=
    RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ
  have hx : ∀ j, x j ∈ I := fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hψX : ∀ i, ψ (X i) = Sum.elim x y i := fun i => by simp [ψ]
  let gy : MvPolynomial (Fin e) R →+* A ⧸ I := eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)
  let FS : S →+* Cc := eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X
  let ρ : P →+* Cc := (C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)
  letI : Algebra P Cc := ρ.toAlgebra
  have hFSC : ∀ p, FS (C p) = C (gy p) := fun p => MvPolynomial.eval₂Hom_C _ _ _
  have hFSX : ∀ j, FS (X j) = X j := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have kC : ∀ r, kap d e R (C r) = C (C r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have kl : ∀ j, kap d e R (X (Sum.inl j)) = 0 := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have ψC : ∀ r, ψ (C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hFS : FS.comp (kap d e R) = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))
      rw [kC, hFSC, hgC, ψC]
    · rintro (j | i)
      · show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))
        rw [kl, hψX, map_zero]; simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]
      · show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))
        rw [kr, hFSC, hgX, hψX]; rfl
  let fS : S →ₐ[P] Cc := { FS with commutes' := fun p => RingHom.congr_fun hFS p }
  let fA : A →ₐ[P] Cc := { (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }
  let F : S ⊗[P] A →+* Cc := (Algebra.TensorProduct.productMap fS fA).toRingHom
  have hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : x j = algebraMap P A (X (Sum.inl j)) := by
      rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
    have h2 : algebraMap P S (X (Sum.inl j)) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact kl j
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]
  let G : Cc →+* S ⊗[P] A :=
    eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom
      fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)
  have hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s := fun s => by simp [F, fS, fA]
  have hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a := fun a => by
    erw [MvPolynomial.eval₂Hom_C]; rfl
  have hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A) := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id Cc := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [F, G, fS, fA]
    · intro j
      show F (G (X j)) = X j
      rw [hGX, hF1, hFSX]
  have hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := S) (B := A)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)
        have e1 : φ r = algebraMap P A (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        have e2 : algebraMap P S (C r) = C (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_C _ _ _
        rw [hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]
      · intro i
        show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)
        have e1 : y i = algebraMap P A (X (Sum.inr i)) := by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
        have e2 : algebraMap P S (X (Sum.inr i)) = C (X i) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_X' _ _ _
        rw [hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]
    · intro j
      show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)
      rw [hF1, hFSX, hGX]
  have hGF : G.comp F = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have hs := RingHom.congr_fun hS s
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs
      have ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a := by
        simp [F, G, fS, fA]; erw [MvPolynomial.eval₂Hom_C]; rfl
      have hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a) := by simp
      rw [RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]
    | add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hu hv ⊢; rw [hu, hv]
  let E : S ⊗[P] A ≃+* Cc := RingEquiv.ofRingHom F G hFG hGF
  let σ : P ≃+* S := (MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv
  have s1 : ∀ r, σ (C r) = C (C r) := fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r
  have s2 : ∀ j, σ (X (Sum.inl j)) = X j := fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j
  have s3 : ∀ i, σ (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i
  have key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
      ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) =
      (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r)); rw [s1]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
    · rintro (j | i)
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j))); rw [s2]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_X']
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i))); rw [s3]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)

theorem LeafPoly_of : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := leafPoly

end LateralTheory.CohomologicalPurity.LeafPolyPf
end
end

