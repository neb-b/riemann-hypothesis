module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem ConeTrdeg.mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : Geo.MRing ι} {d : K → ℕ}
    (hg : Geo.IsMultiHomog g d) :
    Geo.mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  simp only [Geo.mConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [mul_assoc]
  congr 2
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

theorem ConeTrdeg.proof : ConeTrdeg.Statement := by
  intro K _ ι _ Ω _ y hbir hnz hhor
  classical

  have hinjΩ : Function.Injective (algebraMap ℤ Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro n hn
    have hmem : (MvPolynomial.C n : Geo.MRing ι) ∈ Geo.mCoordIdeal y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply, hn, map_zero]
    have h2 : n ∈ (Geo.mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* Geo.MRing ι) := hmem
    simp only [Geo.IsHorizontal] at hhor
    rw [hhor] at h2
    exact (Ideal.mem_bot).1 h2
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr hinjΩ
  have : FaithfulSMul Ω (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω (MvPolynomial K Ω)).mpr (MvPolynomial.C_injective K Ω)
  have hB : Algebra.trdeg ℤ (MvPolynomial K Ω) = Algebra.trdeg ℤ Ω + Fintype.card K := by
    rw [← trdeg_add_eq ℤ Ω (A := MvPolynomial K Ω), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  have hZB : Function.Injective (algebraMap ℤ (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq ℤ Ω (MvPolynomial K Ω), RingHom.coe_comp]
    exact (MvPolynomial.C_injective K Ω).comp hinjΩ
  let S := (Geo.mConeMap y).range
  have hA : Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ S :=
    (Ideal.quotientKerEquivRange (Geo.mConeMap y)).trdeg_eq
  have : FaithfulSMul ℤ S := (faithfulSMul_iff_algebraMap_injective ℤ S).mpr
    (Function.Injective.of_comp (f := algebraMap S (MvPolynomial K Ω))
      (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]))
  have : FaithfulSMul S (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective S (MvPolynomial K Ω)).mpr Subtype.val_injective

  have halgC : ∀ a : Ω, IsAlgebraic S (MvPolynomial.C a : MvPolynomial K Ω) := by
    intro a
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir a
    have hgS : Geo.mConeMap y g ∈ S := AlgHom.mem_range_self _ _
    have hhS : Geo.mConeMap y h ∈ S := AlgHom.mem_range_self _ _
    have hne : Geo.mConeMap y h ≠ 0 := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh]
      exact mul_ne_zero (MvPolynomial.C_ne_zero.2 hh0)
        (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
    refine IsAlgebraic.of_mul (y := Geo.mConeMap y h) (mem_nonZeroDivisors_of_ne_zero hne)
      (isAlgebraic_algebraMap (⟨_, hhS⟩ : S)) ?_
    have hmul : Geo.mConeMap y h * MvPolynomial.C a = Geo.mConeMap y g := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh, ConeTrdeg.mConeMap_of_isMultiHomog y hg, hgh, map_mul]
      ring
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hgS⟩ : S)

  choose c hc using hnz
  have halgX : ∀ k, IsAlgebraic S (X k : MvPolynomial K Ω) := by
    intro k
    have hS : Geo.mConeMap y (X ⟨k, c k⟩) ∈ S := AlgHom.mem_range_self _ _
    refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨k, c k⟩))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.C_ne_zero.2 (hc k))) (halgC _) ?_
    have hmul : (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) = Geo.mConeMap y (X ⟨k, c k⟩) := by
      simp [Geo.mConeMap]
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hS⟩ : S)
  have : Algebra.IsAlgebraic S (MvPolynomial K Ω) := ⟨fun p ↦ by
    induction p using MvPolynomial.induction_on with
    | C a => exact halgC a
    | add p q hp hq => exact hp.add hq
    | mul_X p k hp => exact hp.mul (halgX k)⟩
  have hSB := trdeg_add_eq ℤ S (A := MvPolynomial K Ω)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial K Ω), add_zero] at hSB
  rw [hA, hSB, hB]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PFibreCompDimZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsDedekindDomain

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

section Fibres

variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}

theorem fibreComponent_dim_eq (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial σ ℤ ⧸ W) = m ∧ ∀ q : ℕ, q.Prime →
      ∀ W' ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
        ringKrullDim (MvPolynomial σ ℤ ⧸ W') = m := by
  have := hP
  obtain ⟨n, f, hfC⟩ : ∃ (n : ℕ) (f : MvPolynomial σ ℤ ≃+* MvPolynomial (Fin n) ℤ),
      ∀ a : ℤ, f (C a) = C a :=
    ⟨_, (renameEquiv ℤ (Fintype.equivFin σ)).toRingEquiv, fun a => rename_C _ _⟩
  have hPn : (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).IsPrime :=
    Ideal.map_isPrime_of_equiv f
  have hPnC : (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).comap (C : ℤ →+* MvPolynomial _ ℤ) = ⊥ := by
    ext a
    rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap,
      show f.symm (C a) = C a from f.symm_apply_eq.mpr (hfC a).symm, ← Ideal.mem_comap, hPC]
  have key : ∀ q : ℕ, q.Prime →
      ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
        ringKrullDim (MvPolynomial σ ℤ ⧸ W) = ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
          (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).map (MvPolynomial.map (algebraMap ℤ ℚ))) ∧
        ∃ m : ℕ, ringKrullDim (MvPolynomial σ ℤ ⧸ W) = m := by
    intro q hq W hW
    clear hp
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(q : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq),
      by simpa using hq.ne_zero⟩
    have hmap : (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) =
        P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ⊔ Ideal.map (C : ℤ →+* MvPolynomial _ ℤ) v.asIdeal := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        RingEquiv.coe_toRingHom, hfC]
    have hWn : W.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ∈
        (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ⊔ Ideal.map C v.asIdeal).minimalPrimes := by
      rw [← hmap, Ideal.minimalPrimes_map_of_surjective (f := (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)) f.surjective,
        RingHom.ker_coe_equiv, sup_bot_eq]
      exact ⟨W, hW, rfl⟩
    have hle := le_sup_right.trans hWn.1.2
    have hiso : ringKrullDim (MvPolynomial σ ℤ ⧸ W) =
        ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ W.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ f rfl)
    refine ⟨?_, ?_⟩
    · rw [hiso, ringKrullDim_eq_of_ringEquiv (Vertical.quotientResidueEquiv v _ hle)]
      exact Vertical.FibreCompDim.full ℤ ℚ _ _ _ v hPn hPnC hWn
    · rw [hiso]
      exact Vertical.exists_ringKrullDim_quotient_eq_nat v _ hWn.1.1 hle
  obtain ⟨h1, m, hm⟩ := key p hp W hW
  exact ⟨m, hm, fun q hq W' hW' => (key q hq W' hW').1.trans (h1.symm.trans hm)⟩


omit [Fintype σ] in
theorem fibreComponent_dim_succ_le (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hCp : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ P := fun h => by
    have : (p : ℤ) ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h
    rw [hPC, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left.trans hW.1.2))
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk P (C (p : ℤ)))
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))

theorem ringKrullDim_le_of_fibreComponents (k : WithBot ℕ∞)
    (h : ∀ q : ℕ, q.Prime → ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
      ringKrullDim (MvPolynomial σ ℤ ⧸ W) ≤ k) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ k + 1 := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro M hM
  have := Model.isJacobsonRing_int
  let := Ideal.Quotient.field M
  let g : MvPolynomial σ ℤ →+* (MvPolynomial σ ℤ ⧸ P) ⧸ M :=
    (Ideal.Quotient.mk M).comp (Ideal.Quotient.mk P)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (g.comp C)
    (MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing g hg) ⊥
  obtain ⟨q, hq, hqI⟩ := (Ideal.isPrime_int_iff.mp hI.isPrime).resolve_left
    (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  have hqM : Ideal.Quotient.mk P (C (q : ℤ)) ∈ M := by
    have : (q : ℤ) ∈ (⊥ : Ideal ((MvPolynomial σ ℤ ⧸ P) ⧸ M)).comap (g.comp C) := by
      rw [hqI]
      exact Ideal.subset_span rfl
    rwa [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem] at this
  refine (Ideal.height_le_ringKrullDim_quotient_add_one hqM).trans (add_le_add_left ?_ 1)
  have hspan : Ideal.span {Ideal.Quotient.mk P (C (q : ℤ))} =
      (Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup P _)]
  exact ringKrullDim_quotient_le_of_minimalPrimes _ _ (h q hq)

end Fibres

theorem FibreCompDimZ.proof : FibreCompDimZ.Statement := by
  intro σ _ P hP hPC d p hp hdim W hW
  obtain ⟨m, hm, hall⟩ := fibreComponent_dim_eq hP hPC hp hW
  have h1 := fibreComponent_dim_succ_le hP hPC hp hW
  have h2 := ringKrullDim_le_of_fibreComponents (P := P) (m : WithBot ℕ∞)
    fun q hq W' hW' => (hall q hq W' hW').le
  rw [hm, hdim] at h1
  rw [hdim] at h2
  rw [hm]
  have h1' : m + 1 ≤ d + 1 := by exact_mod_cast h1
  have h2' : d + 1 ≤ m + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : m = d)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace IdealIndexPlaces

theorem genIndex_comap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    {A B : AddSubgroup G} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    genIndex (A.comap f) (B.comap f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self hA,
    AddSubgroup.map_comap_eq_self hB]

theorem absNorm_eq_index {L : Type*} [Field L] [NumberField L] (A : Ideal (𝓞 L)) :
    A.absNorm = A.toAddSubgroup.index := Ideal.absNorm_eq_index A

theorem genIndex_ideal {L : Type*} [Field L] [NumberField L] {A B : Ideal (𝓞 L)} (hA : A ≠ ⊥)
    (hB : B ≠ ⊥) : genIndex A.toAddSubgroup B.toAddSubgroup = (B.absNorm : ℝ) / A.absNorm := by
  have hAB : A ⊓ B ≠ ⊥ := fun h ↦ (mul_ne_zero hA hB) (le_bot_iff.mp (h ▸ Ideal.mul_le_inf))
  have hn : (A ⊓ B).absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hAB
  have hAn : A.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hA
  have hBn : B.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
  have h1 : B.toAddSubgroup.relIndex A.toAddSubgroup * A.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_left, absNorm_eq_index]
    rfl
  have h2 : A.toAddSubgroup.relIndex B.toAddSubgroup * B.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_right, absNorm_eq_index]
    rfl
  have h1' : (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / A.absNorm := by
    rw [← h1]; push_cast; field_simp
  have h2' : (A.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / B.absNorm := by
    rw [← h2]; push_cast; field_simp
  unfold genIndex
  rw [h1', h2']
  field_simp

end IdealIndexPlaces


open IdealIndexPlaces in
theorem IdealIndexPlaces.proof : IdealIndexPlaces.Statement := by
  intro L _ _ ι _ y hy
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  replace hi0 : y i0 ≠ 0 := hi0
  set c : 𝓞 L := z i0 with hc
  have hcy : (c : L) = b * y i0 := hzy i0
  have hcL : (c : L) ≠ 0 := by rw [hcy]; exact mul_ne_zero hbL hi0
  have hc0 : c ≠ 0 := fun h ↦ hcL (by rw [h]; rfl)
  set M := multiplierIdeal y with hMdef
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((c : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (c : L)⁻¹ * t := fun t ↦ rfl
  set I : Ideal (𝓞 L) := M.comap g with hIdef
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hI : ∀ t : 𝓞 L, t ∈ I ↔ ∀ i, t * z i ∈ Ideal.span {c * b} := by
    intro t
    change (∀ i, (c : L)⁻¹ * t * y i ∈ Set.range (algebraMap (𝓞 L) L)) ↔ _
    refine forall_congr' fun i ↦ ?_
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * ((c : L) * b) = t * z i
      change (e : L) = _ at he
      rw [he, hzy i]
      field_simp
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      have he' : (e : L) * ((c : L) * b) = t * z i := congrArg (fun s : 𝓞 L ↦ (s : L)) he
      rw [hzy i] at he'
      have h3 : (e : L) * c = t * y i := mul_right_cancel₀ hbL (by linear_combination he')
      change (e : L) = _
      field_simp
      linear_combination h3

  have hIJ : I * J ≤ Ideal.span {c * b} := by
    refine Ideal.mul_le.mpr fun t ht s hs ↦ ?_
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (𝓞 L) t) (Ideal.span {c * b}) :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (hI t).mp ht i)
    exact hle hs
  have hcbJ : Ideal.span {c * b} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right b J (Ideal.subset_span ⟨i0, rfl⟩))
  have hcb0 : Ideal.span {c * b} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc0 hb0
  have hJ0 : J ≠ ⊥ := fun h ↦ hcb0 (le_bot_iff.mp (h ▸ hcbJ))
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr hcbJ
  have hKI : K ≤ I := fun t ht ↦ (hI t).mpr fun i ↦ by
    rw [hK, mul_comm t]; exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) ht
  have hIK : I ≤ K := by
    have h : J * K ∣ J * I := Ideal.dvd_iff_le.mpr (by rw [mul_comm J I, ← hK]; exact hIJ)
    exact Ideal.le_of_dvd ((mul_dvd_mul_iff_left hJ0).mp h)
  have hIeq : I = K := le_antisymm hIK hKI
  have hI0 : I ≠ ⊥ := by
    intro h; rw [hIeq] at h; rw [h, Ideal.mul_bot] at hK; exact hcb0 hK
  have hnorm : (I.absNorm : ℝ) * J.absNorm =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| * |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    have h := congrArg (fun A ↦ (Ideal.absNorm A : ℝ)) hK
    simp only [map_mul, Ideal.absNorm_span_singleton, Int.natAbs_mul, Nat.cast_mul,
      Nat.cast_natAbs] at h
    rw [hIeq]
    push_cast at h
    linear_combination -1 * h

  set C : Ideal (𝓞 L) := (1 : Submodule (𝓞 L) L).comap g with hCdef
  have hC : C = Ideal.span {c} := by
    ext t
    rw [Ideal.mem_span_singleton']
    show g t ∈ (1 : Submodule (𝓞 L) L) ↔ _
    rw [Submodule.mem_one, hg]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * c = t
      change (e : L) = _ at he
      rw [he]
      field_simp
    · rintro ⟨e, rfl⟩
      refine ⟨e, ?_⟩
      change (e : L) = (c : L)⁻¹ * ((e : L) * c)
      field_simp
  have hrange1 : M.toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    have ha' : a ∈ M := ha
    obtain ⟨e, he⟩ := ha' i0
    refine ⟨b * e, ?_⟩
    change (c : L)⁻¹ * ((b : L) * e) = a
    change (e : L) = _ at he
    rw [he, hcy]
    field_simp
  have hrange2 : (1 : Submodule (𝓞 L) L).toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    obtain ⟨e, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨c * e, ?_⟩
    change (c : L)⁻¹ * ((c : L) * e) = e
    field_simp
  have hC0 : C ≠ ⊥ := by rw [hC, Ne, Ideal.span_singleton_eq_bot]; exact hc0
  have hgen : genIndex M.toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| / I.absNorm := by
    rw [← genIndex_comap g.toAddMonoidHom hrange1 hrange2]
    have e1 : M.toAddSubgroup.comap g.toAddMonoidHom = I.toAddSubgroup := rfl
    have e2 : (1 : Submodule (𝓞 L) L).toAddSubgroup.comap g.toAddMonoidHom = C.toAddSubgroup := rfl
    rw [e1, e2, genIndex_ideal hI0 hC0, hC, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl

  have hz0 : z ≠ 0 := fun h ↦ hc0 (congrFun h i0)
  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [hgen]
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) with hPdef
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hIn : (I.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  have hP : (J.absNorm : ℝ) * P = |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    linear_combination |((Algebra.norm ℤ b : ℤ) : ℝ)| * hprodz - (J.absNorm : ℝ) * P * hinv
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hIn]
  apply mul_left_cancel₀ hJn
  linear_combination |((Algebra.norm ℤ c : ℤ) : ℝ)| * hP - hnorm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PPointHeightDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module Matrix
open scoped ComplexOrder

noncomputable section

section Embedding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


end Embedding

end

end GroundTheory.Heights₂.Heights
end

