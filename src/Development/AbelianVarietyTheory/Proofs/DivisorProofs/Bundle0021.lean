module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfield
section
open IsLocalRing

open scoped TensorProduct

namespace GlobalTheory

theorem etale_hom_to_field_lands_in_algClosed_subfield
    (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L]
    (α : A →+* K) (ι : K →+* L) (β : B →+* L) :
    (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α →
      ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  intro _ hβ
  letI : Algebra A K := α.toAlgebra
  letI : Algebra K L := ι.toAlgebra
  letI : Algebra A L := (ι.comp α).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[A] L :=
    { β with
      commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }
  let f : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _
  haveI : Algebra.IsIntegral K f.range :=
    Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)
  have hsurj : Function.Surjective (algebraMap K f.range) := by
    intro y
    have hy : IsIntegral K (y : L) := (Algebra.IsIntegral.isIntegral y).map f.range.val
    obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K (y : L)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))
    exact ⟨k, Subtype.ext hk⟩
  let e : K ≃+* f.range :=
    RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩
  let ψ : B →+* K :=
    e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)
  have hι : ∀ x, ι (ψ x) = β x := by
    intro x
    have h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x) := rfl
    have h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x) := by
      simp only [ψ, e, RingHom.comp_apply]
      exact (RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _
    rw [← h1, h2]
    simp [f, g]
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    apply ι.injective
    rw [RingHom.comp_apply, hι]
    exact congrArg (fun f : A →+* L => f a) hβ
  · ext x
    exact hι x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegral
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalRingOfLocalization
section
open IsLocalRing

namespace GlobalTheory

theorem exists_finitePresentation_isLocalization_of_localization (A B E : Type) [CommRing A]
    [CommRing B] [CommRing E] [Algebra A B] (M : Submonoid A) [IsLocalization M B] [Algebra B E]
    [Algebra.FinitePresentation B E] :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.FinitePresentation A D)
      (φ : D →+* E), φ.comp (algebraMap A D) = (algebraMap B E).comp (algebraMap A B) ∧
      @IsLocalization D _ (Algebra.algebraMapSubmonoid D M) E _ φ.toAlgebra := by
  classical
  obtain ⟨n, f, hf, hK⟩ := ‹Algebra.FinitePresentation B E›
  letI : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B) :=
    MvPolynomial.algebraMvPolynomial
  haveI hL : IsLocalization (M.map (MvPolynomial.C (σ := Fin n))) (MvPolynomial (Fin n) B) :=
    MvPolynomial.isLocalization M B
  obtain ⟨s, hs⟩ := hK
  choose p hp using fun g : (s : Set (MvPolynomial (Fin n) B)) =>
    IsLocalization.surj (M.map (MvPolynomial.C (σ := Fin n))) (g : MvPolynomial (Fin n) B)
  let J₀ : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range fun g => (p g).1)
  have hJ : J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)) =
      RingHom.ker f := by
    have hs' : Ideal.span (s : Set (MvPolynomial (Fin n) B)) = RingHom.ker f := hs
    rw [Ideal.map_span, ← hs']
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [← hp g]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span g.2)
    · rw [Ideal.span_le]
      intro g hg
      rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ (p ⟨g, hg⟩).2),
        hp ⟨g, hg⟩]
      exact Ideal.subset_span ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
  have hJfg : J₀.FG := Submodule.fg_span (Set.finite_range _)
  let D := MvPolynomial (Fin n) A ⧸ J₀
  haveI : Algebra.FinitePresentation A D := Algebra.FinitePresentation.quotient hJfg
  let Dl := MvPolynomial (Fin n) B ⧸ J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B))
  haveI hDl : IsLocalization (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) Dl :=
    inferInstance
  let e : Dl ≃+* E := (Ideal.quotEquivOfEq hJ).trans (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  let φ : D →+* E := e.toRingHom.comp (algebraMap D Dl)
  refine ⟨D, inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · ext a
    change e (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)
      (MvPolynomial.C a))) = algebraMap B E (algebraMap A B a)
    have he : ∀ x, e (Ideal.Quotient.mk _ x) = f x := fun x => rfl
    rw [he, MvPolynomial.algebraMap_def, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, f.commutes]
  · letI : Algebra D E := φ.toAlgebra
    let e' : Dl ≃ₐ[D] E := AlgEquiv.ofRingEquiv (f := e) (fun x => rfl)
    have hsub : Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n))) =
        Algebra.algebraMapSubmonoid D M := by
      ext x
      simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    haveI := IsLocalization.isLocalization_of_algEquiv
      (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) e'
    rwa [hsub] at this

theorem exists_etale_atPrime_algEquiv_of_isEtaleAt (R D : Type) [CommRing R] [CommRing D]
    [Algebra R D] [Algebra.FinitePresentation R D] (P' : Ideal D) [P'.IsPrime]
    [Algebra.IsEtaleAt R P'] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P') := by
  obtain ⟨f, hfP, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) P'
  let A' := Localization.Away f
  have hdisj : Disjoint (Submonoid.powers f : Set D) P' :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfP
  let q' : Ideal A' := P'.map (algebraMap D A')
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A' P' ‹_› hdisj
  have hcomap : q'.comap (algebraMap D A') = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A' ‹_› hdisj
  haveI h1 : IsLocalization.AtPrime (Localization.AtPrime q') (q'.comap (algebraMap D A')) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f)
      (Localization.AtPrime q') q'
  haveI h2 : IsLocalization P'.primeCompl (Localization.AtPrime q') := by
    have h1' : IsLocalization (q'.comap (algebraMap D A')).primeCompl (Localization.AtPrime q') := h1
    have hsub : (q'.comap (algebraMap D A')).primeCompl = P'.primeCompl := by
      ext x
      simp only [Ideal.mem_primeCompl_iff, hcomap]
    rwa [hsub] at h1'
  let e : Localization.AtPrime q' ≃ₐ[D] Localization.AtPrime P' :=
    IsLocalization.algEquiv P'.primeCompl _ _
  exact ⟨A', inferInstance, inferInstance, hfet, q', hq', ⟨e.restrictScalars R⟩⟩

theorem essEtale_atPrime_of_etale_over_atPrime : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R A E _ _ _ _ _ q _ _ _ _ _ P _
  obtain ⟨D, _, _, _, φ, hφ, hloc⟩ :=
    exists_finitePresentation_isLocalization_of_localization A (Localization.AtPrime q) E q.primeCompl
  letI : Algebra R D := ((algebraMap A D).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FinitePresentation R D := Algebra.FinitePresentation.trans R A D
  letI : Algebra D E := φ.toAlgebra
  haveI : IsScalarTower R D E := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime q) E,
      IsScalarTower.algebraMap_eq R A (Localization.AtPrime q), ← RingHom.comp_assoc, ← hφ]
    rfl
  let EP := Localization.AtPrime P
  haveI : IsScalarTower D E EP := inferInstance
  haveI : IsScalarTower R D EP := inferInstance
  haveI hEP : IsLocalization.AtPrime EP (P.comap (algebraMap D E)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid D q.primeCompl) EP P
  let P' := P.comap (algebraMap D E)
  let eP : Localization.AtPrime P' ≃ₐ[D] EP := IsLocalization.algEquiv P'.primeCompl _ _
  haveI : Algebra.FormallyEtale R A := inferInstance
  haveI : Algebra.FormallyEtale A (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  haveI : Algebra.FormallyEtale R (Localization.AtPrime q) :=
    Algebra.FormallyEtale.comp R A (Localization.AtPrime q)
  haveI : Algebra.FormallyEtale R E := Algebra.FormallyEtale.comp R (Localization.AtPrime q) E
  haveI : Algebra.FormallyEtale E EP := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallyEtale R EP := Algebra.FormallyEtale.comp R E EP
  haveI : Algebra.IsEtaleAt R P' := Algebra.FormallyEtale.of_equiv (eP.restrictScalars R).symm
  obtain ⟨A', i1, i2, i3, q', i4, ⟨e⟩⟩ := exists_etale_atPrime_algEquiv_of_isEtaleAt R D P'
  exact ⟨A', i1, i2, i3, q', i4, ⟨e.trans (eP.restrictScalars R)⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeOfHeightOne
section
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_under p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal
section
namespace GlobalTheory

theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices
section
open Filter Topology

namespace GlobalTheory

theorem tendsto_comp_div_pow_of_ratio (d : ℕ) (h : ℕ → ℝ) (L r : ℝ) (u : ℕ → ℕ) (hr : 0 < r)
    (hh : Tendsto (fun j : ℕ => h j / (j : ℝ) ^ d) atTop (𝓝 L))
    (hu : Tendsto (fun M : ℕ => (u M : ℝ) / M) atTop (𝓝 r)) :
    Tendsto (fun M : ℕ => h (u M) / (M : ℝ) ^ d) atTop (𝓝 (L * r ^ d)) ∧
      Tendsto u atTop atTop := by
  have hu' : Tendsto (fun M : ℕ => (u M : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun M : ℕ => (u M : ℝ) / M * M) atTop atTop :=
      Tendsto.pos_mul_atTop hr hu tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have huN : Tendsto u atTop atTop := tendsto_natCast_atTop_iff.1 hu'
  refine ⟨?_, huN⟩
  have h2 := (hh.comp huN).mul (hu.pow d)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, huN.eventually (eventually_gt_atTop 0)] with M hM huM
  have a : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have b : (u M : ℝ) ≠ 0 := by exact_mod_cast huM.ne'
  simp only [Function.comp]
  rw [div_pow]
  field_simp

theorem tendsto_natDiv_div_self (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((M:ℝ) / n)
      rw [Nat.floor_div_eq_div] at this
      linarith
    rw [le_div_iff₀ hMR]
    have : (1 / (n:ℝ) - 1 / M) * M = M / n - 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMR]
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := n)
    have e : 1 / (n:ℝ) * M = M / n := by ring
    linarith

theorem eventually_le_at_nearby_indices :
    ∀ (d b c : ℕ) (f : ℝ → ℕ → ℝ) (g : ℤ → ℝ) (f₀ : ℤ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ j : ℕ, f₀ j = f 0 j) → (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
        g (b * M + (M / n : ℕ) - c) ≤ f₀ (b * M - c) + ε * (M : ℝ) ^ d := by
  intro d b c f g f₀ α β _hd hb hf hf₀ hg ε hε
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop
      (𝓝 (α * (b:ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α
    rwa [add_zero] at this
  have hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ) := by positivity
  obtain ⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧
      (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by
    have hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0)
        (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) := by
      have : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0)
          (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul
          continuous_const).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d <
      α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)
    obtain ⟨η, h1, h2⟩ := hev.exists
    exact ⟨η, h2, h1⟩
  have hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop
      (𝓝 ((b:ℝ) + 1 / (n:ℝ))) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop
        (𝓝 ((b:ℝ) + 1 / n - 0)) :=
      ((tendsto_natDiv_div_self n hn0).const_add _).sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M + M / n :=
      le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  have hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ)) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0)) :=
      tendsto_const_nhds.sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  obtain ⟨hA, hu₁⟩ := tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos
    (hf η hη.le) hr₁
  obtain ⟨hB, -⟩ := tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR
    (hf 0 le_rfl) hr₀
  have hev : ∀ᶠ M : ℕ in atTop,
      f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε :=
    (tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)
  filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0]
    with M hM hgM hMc hM0
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hle1 : c ≤ b * M + M / n :=
    le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
  have hle0 : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
  have e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  have e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle0]; push_cast; ring
  rw [e1, e0, hf₀]
  have hpos : 0 < (M:ℝ) ^ d := pow_pos hMR d
  rw [← sub_div, div_lt_iff₀ hpos] at hM
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeqOfStep
section
namespace GlobalTheory.SequenceFromIteration

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hstep : ∀ (n : ℕ) (a : A), P n a → ∃ b : A, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n : ℕ, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  choose g hgP hgQ using hstep
  let G : (n : ℕ) → {a : A // P n a} := fun n =>
    Nat.rec (motive := fun n => {a : A // P n a}) ⟨a₀, h₀⟩
      (fun k x => ⟨g k x.1 x.2, hgP k x.1 x.2⟩) n
  exact ⟨fun n => (G n).1, rfl, fun n => ⟨(G n).2, hgQ n (G n).1 (G n).2⟩⟩

end GlobalTheory.SequenceFromIteration
end

