module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramSchur
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

theorem ChartGram.det_eq_corner_mul_schur {K : Type*} [Field K] {e : ℕ}
    (M : Matrix (Fin (e + 1)) (Fin (e + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      (Matrix.of fun i j : Fin e => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0).det := by
  set c : Fin (e + 1) → K := fun i => if i = 0 then 0 else -(M i 0 / M 0 0) with hc
  set B : Matrix (Fin (e + 1)) (Fin (e + 1)) K := Matrix.of fun i j => M i j + c i * M 0 j with hB
  have hdet : B.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [hc]) (fun i j => by simp [hB])
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin e, B i.succ 0 = 0 := by
    intro i
    simp only [hB, hc, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    field_simp
    ring
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  congr 1
  · simp [hB, hc]
  · congr 1
    ext i j
    simp only [hB, hc, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    ring

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ReducedTensorPerfect
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_tensorProduct_of_forall_field {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C]
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [Algebra.EssFiniteType k E], IsReduced (C ⊗[k] E))
    (A : Type u) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (C ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Fintype (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).fintype
  classical
  have hP : ∀ P : minimalPrimes B, P.1.IsPrime := fun P => P.2.1.1
  let φ : B →ₐ[k] ∀ P : minimalPrimes B, FractionRing (B ⧸ P.1) :=
    AlgHom.pi fun P =>
      (IsScalarTower.toAlgHom k (B ⧸ P.1) (FractionRing (B ⧸ P.1))).comp (Ideal.Quotient.mkₐ k P.1)
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      intro P hPm
      have h1 := congr_fun hb ⟨P, hPm⟩
      have h2 : algebraMap (B ⧸ P) (FractionRing (B ⧸ P)) (Ideal.Quotient.mk P b) = 0 := h1
      rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    have : b ∈ nilradical B := hmem
    rw [nilradical_eq_zero] at this
    exact this
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (φ.toLinearMap) hφ
  have : ∀ P : minimalPrimes B, IsReduced (C ⊗[k] FractionRing (B ⧸ P.1)) := fun P => h _
  let ψ := Algebra.TensorProduct.piRight k k C (fun P : minimalPrimes B => FractionRing (B ⧸ P.1))
  exact isReduced_of_injective (ψ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id C C) φ).toRingHom)
    ((AlgEquiv.injective ψ).comp hinj)

theorem isReduced_tensorProduct_of_isSeparable {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [Algebra.EssFiniteType F E]
    (D : Type u) [CommRing D] [Algebra F D] [IsReduced D] : IsReduced (E ⊗[F] D) := by
  refine isReduced_tensorProduct_of_forall_field E (fun M _ _ _ => ?_) D
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  have : IsReduced (M ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F E M).toAlgHom (AlgEquiv.injective _)

theorem isReduced_fractionRing_mvPolynomial_tensorProduct (K : Type u) [Field K] (σ : Type u)
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (FractionRing (MvPolynomial σ K) ⊗[K] L) := by
  let R := MvPolynomial σ K
  have : IsReduced (R ⊗[K] L) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm K R L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv)
      (RingEquiv.injective _)
  have : IsReduced (FractionRing R ⊗[R] (R ⊗[K] L)) := by
    let : Algebra (R ⊗[K] L) (FractionRing R ⊗[R] (R ⊗[K] L)) := Algebra.TensorProduct.rightAlgebra
    exact isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      (FractionRing R ⊗[R] (R ⊗[K] L)) inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange K R R (FractionRing R) L).symm.toAlgHom
    (AlgEquiv.injective _)


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_tensorProduct_field_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (E : Type u) [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] : IsReduced (L ⊗[K] E) := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  let F := IntermediateField.adjoin K (s : Set E)
  have : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp K F E
  let e : FractionRing (MvPolynomial s K) ≃ₐ[K] F :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by simp [F]))
  have : IsReduced (FractionRing (MvPolynomial s K) ⊗[K] L) :=
    isReduced_fractionRing_mvPolynomial_tensorProduct K s L
  have : IsReduced (F ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom
      (AlgEquiv.injective _)
  have hD := isReduced_tensorProduct_of_isSeparable (F := F) (E := E) (F ⊗[K] L)
  exact @isReduced_of_injective _ _ _ _ _ _ _
    ((Algebra.TensorProduct.comm K L E).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K F F E L).symm.toRingEquiv)
    (RingEquiv.injective _) hD

theorem isReduced_tensorProduct_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (A : Type u) [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (L ⊗[K] A) :=
  isReduced_tensorProduct_of_forall_field L
    (fun E _ _ _ => isReduced_tensorProduct_field_of_perfectField K L E) A

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaMultiplicityWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def AreaMultiplicityWeight.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E)
    (f' : E → E →L[ℝ] E), MeasurableSet A → (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      AEMeasurable (fun y => (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)) μ ∧
        ∀ g : E → ℝ≥0∞, Measurable g →
          ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ =
            ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsKernelProjMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def KernelProjMeasurable.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n k : ℕ)
    (L : X → Matrix (Fin k) (Fin n) ℂ), Continuous L →
      Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLocalSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalSectionLengthSum.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B) (f : B),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Module.length B (B ⧸ (J ⊔ Ideal.span {f})) =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing B).toFinset,
          Module.length B (B ⧸ (P ⊔ Ideal.span {f}))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPiQuotCokerFiniteLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def quotToPiMinimalPrimes {B : Type*} [CommRing B] (J : Ideal B) :
    (B ⧸ J) →ₗ[B] ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) :=
  LinearMap.pi fun P => Submodule.factor P.2.1.2

def PiQuotCokerFiniteLength.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B),
    J.IsRadical →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Function.Injective (quotToPiMinimalPrimes J) ∧
        IsFiniteLength B
          (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegAdjoinLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegAdjoinLe.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (s : Set Ω) (ι : Type) [Fintype ι] (t : ι → Ω)
    (ι' : Type) (w : ι' → Ω), (∀ i, IsAlgebraic (Algebra.adjoin K (s ∪ Set.range t)) (w i)) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤
        Algebra.trdeg K (Algebra.adjoin K s) + Fintype.card ι

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegBaseAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegBaseAlgebraic.Statement : Prop :=
  ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower F K Ω], Algebra.IsAlgebraic F K → ∀ (ι : Type) (z : ι → Ω),
      Algebra.trdeg K (Algebra.adjoin K (Set.range z)) ≤ Algebra.trdeg F (Algebra.adjoin F (Set.range z))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ZeroLocusDimH.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} ≤ 2 * (d : ENNReal)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem ringKrullDim_le_of_isIntegral_inj {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem aeval_derivative_minpoly_ne_zero {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hx : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  intro h0
  have hdvd := minpoly.isIntegrallyClosed_dvd hx h0
  have hmon := minpoly.monic hx
  have hne : Polynomial.derivative (minpoly R x) ≠ 0 := by
    intro hd
    exact (minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)
  have h1 := Polynomial.degree_le_of_dvd hdvd hne
  have h2 := Polynomial.degree_derivative_lt hmon.ne_zero
  exact absurd h1 (not_le.2 h2)

theorem exists_simple_root_data {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)
  let _ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := ⟨hint⟩
  have hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩
  choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))
  have hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom =
      algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      change _ = g (C a)
      rw [← MvPolynomial.algebraMap_eq, g.commutes]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hπ j
  have hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n),
      Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
        Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q := by
    intro Q i
    rw [Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]
  have hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  refine ⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_,
    fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey]
    exact aeval_derivative_minpoly_ne_zero hinj _

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end

