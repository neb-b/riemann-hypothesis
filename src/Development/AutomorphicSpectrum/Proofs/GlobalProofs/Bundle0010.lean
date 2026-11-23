module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipal
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_locPrincipal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupport
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_notMem_support {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


open TensorProduct in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  intro k A _ _ φ I h1 h2
  letI := φ.toAlgebra
  haveI hA : Algebra.Smooth k A := h1
  have halg : (Ideal.Quotient.algebra k : Algebra k (A ⧸ I)) =
      ((Ideal.Quotient.mk I).comp φ).toAlgebra := Algebra.algebra_ext _ _ fun _ => rfl
  have hQ : Algebra.FormallySmooth k (A ⧸ I) := by
    have hs : @Algebra.Smooth k _ (A ⧸ I) _ ((Ideal.Quotient.mk I).comp φ).toAlgebra := h2
    rw [← halg] at hs
    exact hs.formallySmooth
  haveI : Algebra.FormallySmooth k A := hA.formallySmooth
  haveI : Module.Projective A (KaehlerDifferential k A) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.FinitePresentation k A := hA.finitePresentation
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  haveI : Module.Finite A (KaehlerDifferential k A) := KaehlerDifferential.finite k A
  haveI : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] KaehlerDifferential k A) :=
    Module.Finite.base_change A (A ⧸ I) _
  haveI : IsScalarTower A (A ⧸ I) I.Cotangent := by
    first
    | infer_instance
    | exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := A ⧸ I)
    Ideal.Quotient.mk_surjective).mp hQ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := Ideal.Cotangent.equivOfEq _ _ (Ideal.mk_ker (I := I))
  let i : I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] KaehlerDifferential k A :=
    LinearMap.extendScalarsOfSurjective hsurj
      (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) ∘ₗ e.symm.toLinearMap)
  let s : (A ⧸ I) ⊗[A] KaehlerDifferential k A →ₗ[A ⧸ I] I.Cotangent :=
    LinearMap.extendScalarsOfSurjective hsurj (e.toLinearMap ∘ₗ l)
  have hsi : s ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun hl (e.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    first
    | (simp only [s, i, LinearMap.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, h, LinearEquiv.apply_symm_apply]; done)
    | (show e (l (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) (e.symm x))) = x
       rw [h, LinearEquiv.apply_symm_apply])
  refine ⟨Module.Finite.of_surjective s fun x => ⟨i x, ?_⟩, Module.Projective.of_split i s hsi⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hsi x
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipal
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem LocPrincipal.exists_pow_mul_sq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {x : A} (hx : x ∈ I ^ 2) :
    ∃ N : ℕ, ∃ c : A, t ^ N * x = c * (f * f) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro g hg k hk
    obtain ⟨n, hn⟩ := h g hg
    obtain ⟨m, hm⟩ := h k hk
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨n + m, a * b, ?_⟩
    calc t ^ (n + m) * (g * k) = (t ^ n * g) * (t ^ m * k) := by ring
      _ = a * b * (f * f) := by rw [← ha, ← hb]; ring
  · rintro x y ⟨N, c, hc⟩ ⟨M, d, hd⟩
    refine ⟨N + M, t ^ M * c + t ^ N * d, ?_⟩
    calc t ^ (N + M) * (x + y) = t ^ M * (t ^ N * x) + t ^ N * (t ^ M * y) := by ring
      _ = _ := by rw [hc, hd]; ring

theorem LocPrincipal.smul_toCotangent_ne_zero {A : Type} [CommRing A] [IsDomain A] {I p : Ideal A}
    [p.IsPrime] (hIp : I ≤ p) {t f : A} (ht : t ∉ p) (hf : f ∈ I) (hf0 : f ≠ 0)
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {s : A} (hs : s ∉ p) :
    s • I.toCotangent ⟨f, hf⟩ ≠ 0 := by
  intro h0
  rw [← map_smul I.toCotangent s ⟨f, hf⟩, Ideal.toCotangent_eq_zero] at h0
  have h0' : s * f ∈ I ^ 2 := by simpa [smul_eq_mul] using h0
  obtain ⟨N, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_mul_sq h h0'
  have hcancel : t ^ N * s = c * f := by
    apply mul_right_cancel₀ hf0
    calc t ^ N * s * f = t ^ N * (s * f) := by ring
      _ = c * (f * f) := hc
      _ = c * f * f := by ring
  have hmem : t ^ N * s ∈ p := by
    rw [hcancel]
    exact hIp (I.mul_mem_left c hf)
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hmem with h1 | h1
  · exact ht (Ideal.IsPrime.mem_of_pow_mem ‹p.IsPrime› N h1)
  · exact hs h1

theorem LocPrincipal.exists_pow_smul_eq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (hf : f ∈ I) (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) (m : I.Cotangent) :
    ∃ (n : ℕ) (c : A), t ^ n • m = c • I.toCotangent ⟨f, hf⟩ := by
  obtain ⟨g, rfl⟩ := I.toCotangent_surjective m
  obtain ⟨n, hn⟩ := h g g.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, c, ?_⟩
  rw [← map_smul I.toCotangent (t ^ n) g, ← map_smul I.toCotangent c ⟨f, hf⟩]
  congr 1
  ext
  simp [smul_eq_mul, hc]

theorem rankAtStalk_cotangent_eq_one {A : Type} [CommRing A] [IsDomain A] (I : Ideal A)
    [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent]
    (P : PrimeSpectrum (A ⧸ I))
    (hP : LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I))) :
    Module.rankAtStalk I.Cotangent P = 1 := by
  obtain ⟨t, f, ht, hf, hf0, h⟩ := hP
  have htP : Ideal.Quotient.mk I t ∉ P.asIdeal := fun H => ht (Ideal.mem_comap.mpr H)
  have hIq : I ≤ P.asIdeal.comap (Ideal.Quotient.mk I) := fun g hg => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact zero_mem _
  have hsmul : ∀ (a : A) (m : I.Cotangent), Ideal.Quotient.mk I a • m = a • m := fun a m => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hspan : Submodule.span (Localization.AtPrime P.asIdeal)
      {LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_smul_eq hf h m
      have htn : (Ideal.Quotient.mk I t) ^ n ∈ P.asIdeal.primeCompl :=
        Ideal.mem_primeCompl_iff.mpr fun H => htP (Ideal.IsPrime.mem_of_pow_mem P.isPrime n H)
      have key : Ideal.Quotient.mk I c • I.toCotangent ⟨f, hf⟩ =
          (⟨_, htn⟩ : P.asIdeal.primeCompl) • m := by
        rw [Submonoid.mk_smul, hsmul, ← map_pow, hsmul]
        exact hc.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨Localization.mk (Ideal.Quotient.mk I c) (⟨_, htn⟩ * s), ?_⟩
      rw [LocalizedModule.mk_smul_mk, key, mul_one, LocalizedModule.mk_cancel_common_left]
  have hx : LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl) ≠ 0 := by
    intro H
    rw [← LocalizedModule.zero_mk (1 : P.asIdeal.primeCompl), LocalizedModule.mk_eq] at H
    obtain ⟨⟨u, hu⟩, hu0⟩ := H
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective u
    simp only [one_smul, smul_zero, Submonoid.mk_smul] at hu0
    rw [hsmul] at hu0
    exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.smul_toCotangent_ne_zero hIq ht hf hf0 h
      (fun hs => Ideal.mem_primeCompl_iff.mp hu (Ideal.mem_comap.mp hs)) hu0
  have hfree : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) := by
    haveI : Module.Flat (A ⧸ I) I.Cotangent := Module.Flat.of_projective
    have hmem : P ∈ Module.freeLocus (A ⧸ I) I.Cotangent := by
      rw [Module.freeLocus_eq_univ]
      trivial
    exact Module.mem_freeLocus.mp hmem
  haveI : Module.Finite (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    Module.Finite.of_fg_top ⟨{LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) 1}, by
      rw [Finset.coe_singleton]
      exact hspan⟩
  haveI := nontrivial_of_ne _ _ hx
  have hle : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) ≤ 1 := by
    have := finrank_le_of_span_eq_top (R := Localization.AtPrime P.asIdeal)
      (v := fun _ : Unit => LocalizedModule.mk (I.toCotangent ⟨f, hf⟩)
        (1 : P.asIdeal.primeCompl)) (by rw [Set.range_const]; exact hspan)
    simpa using this
  have hpos : 0 < Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    (Module.finrank_pos_iff_of_free _ _).mpr inferInstance
  show Module.finrank (Localization.AtPrime P.asIdeal)
    (LocalizedModule P.asIdeal.primeCompl I.Cotangent) = 1
  omega

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPair
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Charts

theorem smooth_affine_chart {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  let φ₀ : CommRingCat.of k ⟶ Γ(X, U.1) := Spec.preimage (U.2.fromSpec ≫ g)
  have h1 : Spec.map φ₀ = U.2.fromSpec ≫ g := Spec.map_preimage _
  refine ⟨φ₀.hom, ?_, ?_⟩
  · have : Smooth (Spec.map φ₀) := by
      rw [h1]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (IsAffineOpen.isOpenImmersion_fromSpec (hU := U.2)) hg
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · have hc : Z.subschemeCover.f U ≫ (Z.subschemeι ≫ g) =
        Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U))) := by
      rw [Spec.map_comp, h1, ← Category.assoc, Z.subschemeCover_map_subschemeι,
        Z.glueDataObjι_ι]
      exact Category.assoc _ _ _
    have : Smooth (Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U)))) := by
      rw [← hc]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (Z.subschemeCover.map_prop U) hZ
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this

end GlobalTheory.CompanionTheory.Hypotheses₂.Charts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem exists_gen_of_map_eq_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (t : A)
    [IsLocalization.Away t B] (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f} := by
  have hbI : b ∈ I.map (algebraMap A B) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨⟨f, s⟩, hf⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) B).mp hbI
  refine ⟨f, f.2, ?_, ?_⟩
  · intro h0
    apply hb
    rw [h0, map_zero] at hf
    exact ((IsLocalization.map_units B s).mul_left_eq_zero).mp hf
  · intro g hg
    have hg' : algebraMap A B g ∈ Ideal.span {b} := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg'
    obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers t) c
    have key : algebraMap A B ((u : A) * (s : A) * g) = algebraMap A B (a * (f : A)) := by
      rw [map_mul, map_mul, map_mul, ← hc, ← hu, ← hf]
      ring
    obtain ⟨e, he⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) B).mp key
    obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp e.2
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    rw [← hl, ← hj, ← hk] at he
    refine ⟨l + j + k, Ideal.mem_span_singleton'.mpr ⟨t ^ l * a, ?_⟩⟩
    rw [pow_add, pow_add]
    linear_combination -he

theorem locPrincipal_of_cartAt : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) →
    LocPrincipal (Z.ideal U) q.asIdeal := by
  intro X _ Z U q hC
  obtain ⟨V, h, hxV, hh, hZV⟩ := hC
  have hxU : U.2.fromSpec q ∈ (U.1 : X.Opens) := by
    have hr : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rw [U.2.range_fromSpec] at hr
    exact hr
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 (U.2.fromSpec q) ⟨hxU, hxV⟩
  have hWU : X.basicOpen f ≤ U.1 := X.basicOpen_le f
  have hWV : X.basicOpen f ≤ V.1 := by
    rw [hfg]
    exact X.basicOpen_le g
  haveI : Nonempty (X.basicOpen f) := ⟨⟨_, hxf⟩⟩
  haveI : Nonempty (V.1 : X.Opens) := ⟨⟨_, hxV⟩⟩
  haveI : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  have hZW : Z.ideal (X.affineBasicOpen f) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    have hmap := Z.map_ideal (U := X.affineBasicOpen f) (V := V) hWV
    rw [hZV, Ideal.map_span, Set.image_singleton] at hmap
    first
      | exact hmap.symm
      | (rw [← hmap]; rfl)
      | (convert hmap.symm using 3)
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hb : (X.presheaf.map (homOfLE hWV).op).hom h ≠ 0 := by
    intro h0
    apply nonZeroDivisors.ne_zero hh
    apply map_injective_of_isIntegral X (homOfLE hWV)
    rw [map_zero]
    exact h0
  have hI : (Z.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    rw [← hZW]
    first
      | exact Z.map_ideal (U := X.affineBasicOpen f) (V := U) hWU
      | exact Z.map_ideal_basicOpen U f
  obtain ⟨f0, hf0, hf0ne, hgen⟩ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_gen_of_map_eq_span f (Z.ideal U) _ hb hI
  refine ⟨f, f0, ?_, hf0, hf0ne, hgen⟩
  have hq : q ∈ PrimeSpectrum.basicOpen f :=
    Eq.mp (congrArg (q ∈ ·) (U.2.fromSpec_preimage_basicOpen f)) hxf
  exact (PrimeSpectrum.mem_basicOpen f q).mp hq

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

