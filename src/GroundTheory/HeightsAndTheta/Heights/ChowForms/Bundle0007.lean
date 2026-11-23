module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealDim.proof (h₁ : IncidenceGeneric.Statement) (h₂ : GenericLinearTrdeg.Statement)
    (h₃ : AffineChartTrdeg.Statement) : IncIdealDim.Statement := by
  intro F _ n k d P hP hdim
  have := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set K := FractionRing (MvPolynomial (Fin (n' + 1)) F ⧸ P)
  set ξ := genPt P
  have hξj : ξ j ≠ 0 := by
    simp only [ξ, genPt]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin (n' + 1) → K := fun m => if m = j then (ξ j)⁻¹ else 0 with hc_def
  have hc : ∑ m, c m * ξ m = 1 := by
    simp [c, inv_mul_cancel₀ hξj]

  let τ : Fin k × Fin n' → Fin k × Fin (n' + 1) := fun im => (im.1, j.succAbove im.2)
  have hτ : Function.Injective τ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [τ, Prod.mk.injEq] at h
    exact Prod.ext h.1 (j.succAbove_right_injective h.2)
  let ψ : MvPolynomial (Fin k × Fin n') K →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    (rename τ).restrictScalars F
  have hψ : Function.Injective ψ := rename_injective τ hτ
  let η : Fin n' → K := fun m => -(ξ (j.succAbove m) * (ξ j)⁻¹)
  let G : Set (MvPolynomial (Fin k × Fin n') K) :=
    Set.range (fun ij => X ij) ∪ Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))

  have hA : ∀ i m, genSubst ξ c (i, j.succAbove m) = ψ (X (i, m)) := by
    intro i m
    simp [ψ, τ, genSubst, c, Fin.succAbove_ne]
  have hB : ∀ i, genSubst ξ c (i, j) = ψ (∑ m, X (i, m) * C (η m)) := by
    intro i
    have h1 : (C (ξ j) * C (ξ j)⁻¹ : MvPolynomial (Fin k × Fin (n' + 1)) K) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hξj, map_one]
    have h2 : ψ (∑ m, X (i, m) * C (η m)) =
        -((∑ m, X (i, j.succAbove m) * C (ξ (j.succAbove m))) * C (ξ j)⁻¹) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ψ, AlgHom.restrictScalars_apply, map_sum, map_mul, rename_X, rename_C, τ]
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [C_neg, C_mul]
      ring
    rw [h2]
    simp only [genSubst, c, if_pos rfl]
    rw [Fin.sum_univ_succAbove _ j]
    linear_combination (-(X (i, j) : MvPolynomial (Fin k × Fin (n' + 1)) K)) * h1
  have hrange : Set.range (genSubst ξ c) = ψ '' G := by
    ext p
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      by_cases hm : m = j
      · rw [hm]
        exact ⟨_, Or.inr ⟨i, rfl⟩, (hB i).symm⟩
      · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
        exact ⟨_, Or.inl ⟨(i, m'), rfl⟩, (hA i m').symm⟩
    · rintro ⟨q, (⟨⟨i, m⟩, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact ⟨(i, j.succAbove m), hA i m⟩
      · exact ⟨(i, j), hB i⟩

  have hη : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = ((d : ℕ) : Cardinal) := by
    have heq : Algebra.adjoin F (Set.range η) =
        Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹) := by
      apply le_antisymm
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        exact neg_mem (Algebra.subset_adjoin ⟨j.succAbove m, rfl⟩)
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        by_cases hm : m = j
        · beta_reduce
          rw [hm, mul_inv_cancel₀ hξj]
          exact one_mem _
        · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
          have : ξ (j.succAbove m') * (ξ j)⁻¹ = -η m' := (neg_neg _).symm
          beta_reduce
          rw [this]
          exact neg_mem (Algebra.subset_adjoin ⟨m', rfl⟩)
    rw [heq]
    exact h₃ F (n' + 1) d P j hP hdim hj

  let φ : MvPolynomial (Fin k × Fin (n' + 1)) F →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    aeval (genSubst ξ c)
  have hker : incIdeal P k = RingHom.ker φ := by
    ext g
    rw [h₁ F (n' + 1) k P c hc g, RingHom.mem_ker]
  have hφrange : φ.range = (Algebra.adjoin F G).map ψ := by
    show (aeval (genSubst ξ c)).range = _
    rw [aeval_range, hrange, Algebra.adjoin_image]
  haveI : Algebra.FiniteType F φ.range :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have htr : Algebra.trdeg F φ.range = ((k * n' + min k d : ℕ) : Cardinal) := by
    rw [hφrange, ← AlgEquiv.trdeg_eq (A := ↥(Algebra.adjoin F G))
      (Subalgebra.equivMapOfInjective (Algebra.adjoin F G) ψ hψ)]
    exact h₂ F K n' k d η hη
  rw [hker, ringKrullDim_eq_of_ringEquiv (AlgEquiv.toRingEquiv (Ideal.quotientKerEquivRange φ)),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := ↥φ.range), htr]
  have hnum : k * (n' + 1) - k + min k d = k * n' + min k d := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hnum]
  simp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthFiniteAlgebra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

noncomputable section

namespace LengthFiniteAlgebra

variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem comap_eq_maximalIdeal [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)

theorem finite_maximalSpectrum [Module.Finite O B] : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal O).primesOver B)
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_
  intro P Q h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)

theorem length_eq_finsum_localization [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]
  let φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal) :=
    LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    apply MaximalSpectrum.toPiLocalization_injective B
    funext P
    exact congrFun h P
  by_cases h : Module.length O B = ⊤
  · rw [h]
    exact (top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm
  · have hfl : IsFiniteLength O B := Module.length_ne_top_iff.mp h
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
    have : IsArtinianRing B := isArtinian_of_tower O hfl.2
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, hx⟩ := PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z
      exact ⟨x, hx⟩
    exact (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq

theorem isLocalHom_localization [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ P.comap (algebraMap O B) := by
    rw [comap_eq_maximalIdeal P]; exact hna
  have h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈
      maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2 ha


omit [IsLocalRing O] in
theorem length_residueField (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by
  let e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  exact (e'.toLinearEquiv.restrictScalars O).length_eq.symm

theorem ord_mul_length [Module.Finite O B] (P : Ideal B) [P.IsMaximal] (θ : B) :
    Ring.ord (Localization.AtPrime P) (algebraMap B _ θ) * Module.length O (B ⧸ P) =
      Module.length O (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) θ}) := by
  have := isLocalHom_localization (O := O) P
  have h1 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) θ})
  have h2 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (ResidueField (Localization.AtPrime P))
  have h3 : Module.length (Localization.AtPrime P) (ResidueField (Localization.AtPrime P)) = 1 := by
    rw [Module.length_eq_of_surjective (S := Localization.AtPrime P)
      (R := ResidueField (Localization.AtPrime P)) residue_surjective]
    exact Module.length_eq_one _ _
  rw [length_residueField, h3, one_mul] at h2
  rw [h2, h1]
  rfl


omit [IsLocalRing O] in
theorem length_localization_quotient (I : Ideal B) (Q : Ideal (B ⧸ I)) [Q.IsMaximal] :
    Module.length O (Localization.AtPrime Q) =
      Module.length O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl =
      Q.primeCompl := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))
  have : IsScalarTower O (B ⧸ I)
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ I),
        IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))),
        IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]
      rfl
  exact (e.toLinearEquiv.restrictScalars O).length_eq

theorem finsum_reindex [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  have := finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B := fun Q =>
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by
      have := Q.isMaximal; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine Fintype.sum_of_injective ι ?_ _ _ ?_ ?_
  · intro Q₁ Q₂ h
    exact MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  · intro P hP
    have hθ : θ ∉ P.asIdeal := by
      intro hθ
      apply hP
      have hle : Ideal.span {θ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hθ
      have := P.isMaximal
      have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal)
        (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
      exact ⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
    have hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ) :=
      IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Module.length_eq_zero
  · intro Q
    have := Q.isMaximal
    rw [length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]

end LengthFiniteAlgebra


open LengthFiniteAlgebra in
theorem LengthFiniteAlgebra.proof : LengthFiniteAlgebra.Statement := by
  intro O B _ _ _ _ _ _ θ
  have hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  rw [(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq,
    length_eq_finsum_localization, finsum_reindex]
  congr 1
  funext P
  exact (ord_mul_length P.asIdeal θ).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PSectionOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrder.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoice.Statement) (h₄ : SpecFirstNe.Statement) (h₅ : LocalizationPrimeDVR.Statement)
    (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartLocDomain.Statement)
    (h₉ : ChartNorm.Statement) (h₁₀ : ChartLength.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrder.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstNe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Choice

variable {F : Type} [Field F] {k n : ℕ}

def specFirstSplit (ij : Fin (k + 1) × Fin n) : (Fin k × Fin n) ⊕ Fin n :=
  Fin.cases (motive := fun _ => (Fin k × Fin n) ⊕ Fin n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

theorem specFirstSplit_injective : Function.Injective (specFirstSplit (k := k) (n := n)) := by
  rintro ⟨i, m⟩ ⟨j, m'⟩ h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]

theorem specFirst_eq_map_eval (g : MvPolynomial (Fin (k + 1) × Fin n) F) (t : Fin n → F) :
    specFirst g t = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit g)) := by
  have h : (bind₁ (specFirstVar t) : MvPolynomial (Fin (k + 1) × Fin n) F →ₐ[F] _).toRingHom =
      (map (eval t)).comp ((sumAlgEquiv F (Fin k × Fin n) (Fin n)).toRingHom.comp
        (rename specFirstSplit).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change bind₁ (specFirstVar t) (C a) =
        map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit (C a)))
      rw [bind₁_C_right, rename_C, sumAlgEquiv_C_inl, map_C, eval_C]
    · rintro ⟨i, m⟩
      cases i using Fin.cases <;>
        simp [specFirstVar, specFirstSplit, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]
  exact RingHom.congr_fun h g

theorem exists_specFirst_ne_zero [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by
  set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr
      ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)
  obtain ⟨β, hβ⟩ := ne_zero_iff.mp hg
  have ht : ∃ t : Fin n → F, eval t (AddMonoidAlgebra.coeff g β) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hβ (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, fun h0 => ht ?_⟩
  have := congr_arg (AddMonoidAlgebra.coeff · β) h0
  simpa only [specFirst_eq_map_eval, ← hg_def, coeff_map, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] using this

end Choice

theorem det_mulLeft_ne_zero {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by
  classical
  intro h
  by_cases H : ∃ s : Finset B, Nonempty (Module.Basis s O B)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : Module.Free O B := Module.Free.of_basis b
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
    rw [bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot] at hker
    exact hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)
  · simp [LinearMap.coe_det, H] at h

theorem SpecFirstNe.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₄ : ChartLocDomain.Statement) (h₅ : ChartNorm.Statement) : SpecFirstNe.Statement := by
  intro F _ _ n e I f u hI hf hu
  obtain ⟨t, ht⟩ := exists_specFirst_ne_zero hf.1
  have hlt : linForm t ∉ I := fun hmem => ht (by
    have hmem' := h₂ F n e I I f t hf le_rfl hmem
    rwa [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')
  have htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)) := by
    rwa [Ideal.mem_bot]
  obtain ⟨hdom, -, hθ⟩ := h₄ F n e I f t ⊥ hI hf hlt
  have hnorm := h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u
  have ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (specFirst f t) ≠ 0 := fun h => ht
    (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))
  have hdet := det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
    (hθ u hu)
  intro h0
  rw [h0, map_zero] at hnorm
  exact mul_ne_zero ha hdet hnorm.symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def firstGroup {F : Type*} [Field F] {n e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval (fun ij : Fin (e + 1) × Fin n =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) f

def ChartFirstGroupPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f →
      Prime (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

