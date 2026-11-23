module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallAlgHom
section
open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifi
section
open TensorProduct

noncomputable section
namespace GlobalTheory.DenseSec

theorem locQuot_finiteType_formallyUnramified (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
    (g : ℕ) (t : Fin g → A) (h : A) (hE : GlobalTheory.DenseSec.EtChart R A t h) (Ω : Type) [Field Ω] [Algebra R Ω]
    (I : Ideal (TensorProduct R Ω A)) :
    (letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
      (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
    Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
      Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) := by
  letI algPD : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  letI algRA : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI algRP : Algebra (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω) := MvPolynomial.algebraMvPolynomial
  letI algRD : Algebra (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    ((algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      (algebraMap (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω))).toAlgebra
  haveI hST := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algRP algPD algRD (fun _ => rfl)
  let f : A →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    (algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      ((Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)).toRingHom)
  have hf : ∀ a, f a = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
      (Ideal.Quotient.mk I (1 ⊗ₜ[R] a)) := fun a => rfl
  have hu : IsUnit (f h) := by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit _
  let ψ0 : Localization.Away h →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    IsLocalization.Away.lift h hu
  have hψ0 : ∀ a, ψ0 (algebraMap A (Localization.Away h) a) = f a :=
    IsLocalization.Away.lift_eq h hu
  have hΩ : ∀ w : Ω, algebraMap Ω (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) w =
      algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
        (Ideal.Quotient.mk I (w ⊗ₜ[R] 1)) := by
    intro w
    rw [IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ I)]
    rfl
  have hcomp : ψ0.comp (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h)) =
      algebraMap (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.C r))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.C r))
      rw [hψ0, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, hf, hΩ]
      congr 2
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    · intro i
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.X i))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.X i))
      rw [hψ0, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hf]
  let ψ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    { ψ0 with commutes' := fun p => RingHom.congr_fun hcomp p }
  let Φ : MvPolynomial (Fin g) Ω ⊗[MvPolynomial (Fin g) R] Localization.Away h →ₐ[MvPolynomial (Fin g) Ω]
      Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (p : MvPolynomial (Fin g) Ω) (y : Localization.Away h), Φ (p ⊗ₜ y) = algebraMap _ _ p * ψ0 y :=
    fun p y => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hQ : ∀ x : TensorProduct R Ω A ⧸ I,
      algebraMap _ (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x ∈ Φ.range := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction b using TensorProduct.inductionOn with
    | tmul w a =>
      refine ⟨MvPolynomial.C w ⊗ₜ algebraMap A _ a, ?_⟩
      show Φ (MvPolynomial.C w ⊗ₜ algebraMap A _ a) = _
      rw [hΦ, hψ0, hf]
      show MvPolynomial.aeval _ (MvPolynomial.C w) * _ = _
      rw [MvPolynomial.aeval_C, hΩ, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [RingHom.map_add (Ideal.Quotient.mk I), RingHom.map_add (algebraMap (Ω ⊗[R] A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ]; exact add_mem hx hy
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) z
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hs : s = ⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ ^ n := Subtype.ext hn.symm
    have hinv : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
        (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
          Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) =
        Φ (1 ⊗ₜ IsLocalization.mk' (Localization.Away h) (1 : A) (⟨h, Submonoid.mem_powers _⟩ : Submonoid.powers h)) := by
      rw [hΦ, map_one, one_mul, IsLocalization.mk'_eq_iff_eq_mul]
      show _ = _ * f h
      rw [← hψ0, ← map_mul, IsLocalization.mk'_spec]
      simp
    have : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x s ∈ Φ.range := by
      have hpow : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) s =
          (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
            (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
              Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ^ n := by
        rw [hs, ← IsLocalization.mk'_pow, one_pow]
      rw [IsLocalization.mk'_eq_mul_mk'_one, hpow, hinv]
      exact mul_mem (hQ x) (pow_mem (AlgHom.mem_range_self Φ _) n)
    exact this
  exact ⟨Algebra.FiniteType.of_surjective Φ hsurj, Algebra.FormallyUnramified.of_surjective Φ hsurj⟩

end GlobalTheory.DenseSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
section
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_isDomain_isIntegrallyClosed :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A]
      [Algebra.Etale R A] (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro R A _ _ _ _ _ _ p _
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale R p (Localization.AtPrime p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraic
section
namespace GlobalTheory

namespace FracAlgEtale

theorem exists_isAlgebraic_ratFunc_of_ringHom (k B : Type) [Field k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) (f : B)
    (hf : f ≠ 0) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (R : Type)
    [CommRing R] [Algebra A' R] [IsLocalization.Away (algebraMap B A' f) R] (Q : Type)
    [CommRing Q] [Algebra R Q] [IsFractionRing R Q] (K : Type) [Field K] (π : Q →+* K)
    (hπ : Function.Surjective π) :
    ∃ _ : Algebra (RatFunc k) K, Algebra.IsAlgebraic (RatFunc k) K := by
  let ι : R →+* Q := algebraMap R Q
  letI : Algebra B R := ((algebraMap A' R).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra A' K := (π.comp (ι.comp (algebraMap A' R))).toAlgebra
  letI : Algebra B K := ((algebraMap A' K).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let F := FractionRing B

  haveI : Module.Flat A' R := IsLocalization.flat R (Submonoid.powers (algebraMap B A' f))
  haveI : Module.Flat B R := Module.Flat.trans B A' R
  have hreg : ∀ b ∈ nonZeroDivisors B, algebraMap B R b ∈ nonZeroDivisors R := by
    intro b hb
    have hs := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hb
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => hs ?_, fun x hx => hs ?_⟩
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
  have hunitR : ∀ s ∈ nonZeroDivisors R, IsUnit (π (ι s)) := fun s hs =>
    (IsLocalization.map_units Q (⟨s, hs⟩ : nonZeroDivisors R)).map π
  have hBK : ∀ b : B, algebraMap B K b = π (ι (algebraMap B R b)) := fun b => rfl
  have hunit : ∀ y : nonZeroDivisors B, IsUnit (algebraMap B K y) := fun y => by
    rw [hBK]; exact hunitR _ (hreg _ y.2)
  letI : Algebra F K := (IsLocalization.lift (M := nonZeroDivisors B) (S := F) hunit).toAlgebra
  haveI : IsScalarTower B F K := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq (M := nonZeroDivisors B) (S := F) hunit b).symm

  haveI : Module.Finite F (TensorProduct B F A') := Algebra.FormallyUnramified.finite_of_free F _
  let ψ : TensorProduct B F A' →ₐ[F] K :=
    Algebra.TensorProduct.lift (Algebra.ofId F K) (IsScalarTower.toAlgHom B A' K)
      (fun _ _ => Commute.all _ _)
  have hA : ∀ a : A', IsIntegral F (algebraMap A' K a) := fun a => by
    have h1 := (Algebra.IsIntegral.isIntegral (R := F) ((1 : F) ⊗ₜ[B] a)).map ψ
    simpa [ψ] using h1
  have hAR : ∀ a : A', π (ι (algebraMap A' R a)) = algebraMap A' K a := fun a => rfl
  have hf' : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  have hR : ∀ x : R, IsIntegral F (π (ι x)) := by
    intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B A' f)) x
    have hx' := congrArg (fun y => π (ι y)) hx
    simp only [map_mul, map_pow] at hx'
    have hfK : π (ι (algebraMap A' R (algebraMap B A' f))) = algebraMap F K (algebraMap B F f) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; rfl
    rw [hfK, hAR] at hx'
    have hu : IsUnit (algebraMap F K (algebraMap B F f)) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; exact hunit ⟨f, hf'⟩
    have hne : (algebraMap F K (algebraMap B F f)) ^ n ≠ 0 := pow_ne_zero _ hu.ne_zero
    have : π (ι x) = algebraMap A' K a * ((algebraMap F K (algebraMap B F f)) ^ n)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hne).2 hx'
    rw [this]
    exact (hA a).mul ((isIntegral_algebraMap (R := F) (A := K) (x := algebraMap B F f)).pow n).inv
  have hall : ∀ z : K, IsIntegral F z := by
    intro z
    obtain ⟨q, rfl⟩ := hπ z
    obtain ⟨⟨x, s⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors R) q
    have hq' : π q * π (ι s) = π (ι x) := by
      rw [← map_mul]; exact congrArg π hq
    have : π q = π (ι x) * (π (ι s))⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hunitR _ s.2).ne_zero).2 hq'
    rw [this]
    exact (hR x).mul (hR s).inv
  haveI : Algebra.IsIntegral F K := ⟨hall⟩
  haveI : Algebra.IsAlgebraic F K := inferInstance

  obtain ⟨algRF, hRF⟩ := GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc k B hB
  letI algK : Algebra (RatFunc k) K := ((algebraMap F K).comp (algebraMap (RatFunc k) F)).toAlgebra
  haveI : IsScalarTower (RatFunc k) F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨algK, Algebra.IsAlgebraic.trans (RatFunc k) F K⟩

theorem exists_isAlgebraic_ratFunc_residue : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  intro k B _ _ _ _ _ _ hB f hf A' _ _ _ M
  haveI : M.asIdeal.IsMaximal := M.isMaximal
  letI : Field (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) :=
    Ideal.Quotient.field M.asIdeal
  exact exists_isAlgebraic_ratFunc_of_ringHom k B hB f hf A' (Localization.Away (algebraMap B A' f))
    (FractionRing (Localization.Away (algebraMap B A' f)))
    (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) (Ideal.Quotient.mk M.asIdeal)
    (Ideal.Quotient.mk_surjective (I := M.asIdeal))

end FracAlgEtale

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMap
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.base_le_all {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    EtNbhd.base ≤ i := by
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) ?_, ?_⟩
  · intro a ha
    have hcomp : (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) =
        (Algebra.ofId R i.A).comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom :=
      MvPolynomial.algHom_ext fun x => x.elim0
    have ha' : (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom a = 0 := ha
    exact (DFunLike.congr_fun hcomp a).trans ((congrArg (Algebra.ofId R i.A) ha').trans (map_zero _))
  · exact Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun x => x.elim0)

theorem Hens.of_algebraMap (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R) :
    Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  have h := EtNbhd.base_le_all i
  change Hens.of i (algebraMap R i.B r) = Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r)
  have e : Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r) =
      Hens.of i (EtNbhd.trans h (algebraMap R EtNbhd.base.B r)) :=
    (Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h _).symm
  rw [e]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (EtNbhd.base (R := R)).A (EtNbhd.base (R := R)).B r, EtNbhd.trans,
    Localization.localRingHom_to_map, RingHom.coe_coe, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply R i.A i.B r]

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.trans_isLocalHom_injective (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R)
    (h : i ≤ j) : IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  have hloc : IsLocalHom (EtNbhd.trans h) := by
    unfold EtNbhd.trans
    exact Localization.isLocalHom_localRingHom _ _ _ _
  refine ⟨hloc, ?_⟩
  set f : i.A →ₐ[R] j.A := h.choose with hfdef
  letI : Algebra i.A j.A := (f : i.A →+* j.A).toAlgebra
  haveI : IsScalarTower R i.A j.A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.Etale i.A j.A := Algebra.Etale.of_restrictScalars R i.A j.A
  have hflat : (f : i.A →+* j.A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hB : (EtNbhd.trans h).Flat := RingHom.Flat.localRingHom hflat j.q i.q _
  letI : Algebra i.B j.B := (EtNbhd.trans h).toAlgebra
  haveI : Module.Flat i.B j.B := RingHom.flat_algebraMap_iff.mp hB
  haveI : IsLocalHom (algebraMap i.B j.B) := hloc
  haveI hff : Module.FaithfullyFlat i.B j.B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.FaithfullyFlat.injective hff

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacter
section
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_action_factors (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O]
    [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X]
    [Module k X] (σX : O →+* Module.End k X)
    (hσ : ∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) :
    ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  letI : Algebra C (Module.End k X) :=
    ((algebraMap k (Module.End k X)).comp (algebraMap C k)).toAlgebra'
      (fun c f => Algebra.commutes (algebraMap C k c) f)
  haveI : IsScalarTower C k (Module.End k X) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : O →ₐ[C] Module.End k X :=
    { σX with
      commutes' := fun c => by
        change σX (algebraMap C O c) = algebraMap k (Module.End k X) (algebraMap C k c)
        rw [hσ]; exact (Algebra.algebraMap_eq_smul_one _).symm }
  let F : (k ⊗[C] O) →ₐ[k] Module.End k X :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k X)) g
      (fun x y => Algebra.commutes x (g y))
  refine ⟨F.comp e.symm.toAlgHom, fun o => ?_⟩
  show F (e.symm (e (1 ⊗ₜ[C] o))) = σX o
  rw [e.symm_apply_apply]
  rw [show F (1 ⊗ₜ[C] o) = Algebra.ofId k (Module.End k X) 1 * g o from
    Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomInjectiveApplyOfTranscendental
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algebraicIndependent_update_pow {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] {x : ι → A} (hx : AlgebraicIndependent R x) (i₀ : ι) {n : ℕ} (hn : 0 < n) :
    AlgebraicIndependent R (Function.update x i₀ (x i₀ ^ n)) := by
  let e := Equiv.optionSubtypeNe i₀
  have key : ∀ y : ι → A, y ∘ e = fun o => o.elim (y i₀) (fun b => y b.1) := by
    intro y; funext o; cases o <;> rfl
  rw [← algebraicIndependent_equiv e, key] at hx
  rw [← algebraicIndependent_equiv e, key]
  obtain ⟨h1, h2⟩ := AlgebraicIndependent.option_iff.1 hx
  have hrest : (fun b : {b // b ≠ i₀} => Function.update x i₀ (x i₀ ^ n) b.1) =
      fun b => x b.1 := by
    funext b; exact Function.update_of_ne b.2 _ _
  rw [hrest, Function.update_self]
  exact AlgebraicIndependent.option_iff.2 ⟨h1, h2.pow hn⟩

end GlobalTheory
end

