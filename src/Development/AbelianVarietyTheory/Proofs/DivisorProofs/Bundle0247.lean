module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import GroundTheory.LocalFields.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroup
section
open Matrix
open scoped Classical

namespace GlobalTheory

noncomputable def strictMonoEquivPowersetCard (a : ℕ) (n : Type*) [LinearOrder n] :
    {s : Fin a → n // StrictMono s} ≃ Set.powersetCard n a :=
  ({ toFun := fun s => OrderEmbedding.ofStrictMono s.1 s.2
     invFun := fun f => ⟨f, f.strictMono⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => by ext; rfl } : {s : Fin a → n // StrictMono s} ≃ (Fin a ↪o n)).trans
    Set.powersetCard.ofFinEmbEquiv

theorem subsetEnum_strictMonoEquivPowersetCard (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by
  have h : Set.powersetCard.ofFinEmbEquiv.symm (strictMonoEquivPowersetCard a n s) =
      OrderEmbedding.ofStrictMono s.1 s.2 := Equiv.symm_apply_apply _ _
  exact congrArg (fun f : Fin a ↪o n => (f : Fin a → n)) h

theorem minorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  intro N a M hM
  set e := strictMonoEquivPowersetCard a (Fin N)
  have hC : (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) =
      (compoundMatrix a Mᵀ).submatrix e e := by
    ext s s'
    have he : ∀ s, subsetEnum (e s) = s.1 := subsetEnum_strictMonoEquivPowersetCard a
    simp only [submatrix_apply, compoundMatrix, of_apply, he]
    rfl
  have hT : Mᵀ * (Mᵀ)ᴴ = 1 := by
    rw [mem_unitaryGroup_iff'] at hM
    have h1 : Mᵀ * (Mᵀ)ᴴ = (star M * M)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, mul_comm]
    rw [h1, hM, transpose_one]
  rw [hC, mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hT,
    compoundMatrix_one, submatrix_one_equiv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanZeroCompSmulPeriodicFundamentalDomain
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_zero_comp_smul_of_periodic :
    ∀ (n : Type) [Fintype n] (L : AddSubgroup (n → ℝ)) [Countable L] (D : Set (n → ℝ)) (k : (n → ℝ) → ℂ) (q : ℝ), 0 < q → MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → 0 < MeasureTheory.volume D → MeasureTheory.volume D < ⊤ → Continuous k → (∃ C : ℝ, ∀ s, ‖k s‖ ≤ C) → (∀ p ∈ L, ∀ s, k (s + p) = k s) → ∫ s in D, k s = 0 → ∀ (L₁ : AddSubgroup (n → ℝ)) [Countable L₁] (D₁ : Set (n → ℝ)), MeasureTheory.IsAddFundamentalDomain L₁ D₁ MeasureTheory.volume → MeasureTheory.volume D₁ < ⊤ → (∀ p ∈ L₁, ∀ s, k (q • (s + p)) = k (q • s)) → ∫ s in D₁, k (q • s) = 0 := by
  intro n _ L _ D k q hq hD hDpos hDfin hk hb hper h0 L₁ _ D₁ hD₁ hD₁fin hper₁
  have hq0 : q ≠ 0 := hq.ne'
  have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq0
  let φ : (n → ℝ) →+ (n → ℝ) := DistribSMul.toAddMonoidHom (n → ℝ) q⁻¹
  have hφ : Function.Injective φ := fun x y h => by
    simpa [φ, smul_right_inj hqi] using h
  let L' : AddSubgroup (n → ℝ) := L.map φ
  let eL : L ≃+ L' := AddSubgroup.equivMapOfInjective L φ hφ
  haveI : Countable L' := Countable.of_equiv L eL.toEquiv
  let f : (n → ℝ) ≃ (n → ℝ) := (Homeomorph.smulOfNeZero q⁻¹ hqi).toEquiv
  have hf : ∀ x, f x = q⁻¹ • x := fun x => rfl
  have hfs : ∀ x, f.symm x = q • x := fun x => by
    apply f.injective
    rw [Equiv.apply_symm_apply, hf, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hD' : IsAddFundamentalDomain L' (f '' D) volume := by
    refine hD.image_of_equiv f ?_ eL.symm.toEquiv ?_
    · have : (f.symm : (n → ℝ) → (n → ℝ)) = fun x => q • x := funext hfs
      rw [this]
      exact Measure.quasiMeasurePreserving_smul volume hq0
    · intro g x
      show f ((eL.symm g : L) +ᵥ x) = g +ᵥ f x
      have hg : ((g : L') : n → ℝ) = q⁻¹ • ((eL.symm g : L) : n → ℝ) := by
        conv_lhs => rw [← eL.apply_symm_apply g]
        rfl
      rw [AddSubgroup.vadd_def, AddSubgroup.vadd_def, vadd_eq_add, vadd_eq_add, hf, hf, smul_add, hg]
  have himg : f '' D = q⁻¹ • D := by
    ext x; simp [hf, Set.mem_smul_set]
  rw [himg] at hD'
  have hvol : volume (q⁻¹ • D) = ENNReal.ofReal |q⁻¹ ^ Module.finrank ℝ (n → ℝ)| * volume D :=
    Measure.addHaar_smul volume q⁻¹ D
  have hvne0 : volume (q⁻¹ • D) ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero ?_ hDpos.ne'
    simpa using abs_pos.2 (pow_ne_zero (Module.finrank ℝ (n → ℝ)) hqi)
  have hvfin : volume (q⁻¹ • D) < ⊤ := by
    rw [hvol]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin
  have hint0 : ∫ s in q⁻¹ • D, k (q • s) = 0 := by
    rw [Measure.setIntegral_comp_smul_of_pos volume k (q⁻¹ • D) hq, smul_smul,
      mul_inv_cancel₀ hq0, one_smul, h0, smul_zero]
  have hperL' : ∀ p ∈ L', ∀ s, k (q • (s + p)) = k (q • s) := by
    intro p hp s
    obtain ⟨p0, hp0, rfl⟩ := AddSubgroup.mem_map.1 hp
    have : q • (s + φ p0) = q • s + p0 := by
      simp [φ, smul_add, smul_smul, mul_inv_cancel₀ hq0]
    rw [this, hper p0 hp0]
  obtain ⟨C, hC⟩ := hb
  have key := mean_fundamentalDomain_eq_of_periodic n L' L₁ (q⁻¹ • D) D₁ (fun s => k (q • s))
    hD' hD₁ hvfin hD₁fin (hk.comp (continuous_const_smul q)) ⟨C, fun s => hC _⟩ hperL' hper₁
  rw [hint0, mul_zero] at key
  have hre : ((volume (q⁻¹ • D)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hvne0 hvfin.ne).ne'
  exact (mul_eq_zero.1 key).resolve_left hre

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusInversionAffineFinrankSubspaces
section
namespace GlobalTheory.CuspGL

theorem finsum_le_oneValue_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A : Submodule K U) :
    ∑ᶠ B : {B : Submodule K U // B ≤ A}, oneValue (Nat.card K) (Module.finrank K B.1) =
      (Module.finrank K A : ℂ) := by
  classical
  haveI : Finite A := Module.finite_of_finite K
  haveI : Fintype (Submodule K A) := Fintype.ofFinite _
  rw [← sum_oneValue_finrank K A, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (Submodule.MapSubtype.orderIso A).toEquiv]
  refine finsum_congr fun W => ?_
  congr 1
  exact Submodule.finrank_map_subtype_eq A W

theorem eq_of_finsum_le_eq {α : Type} [PartialOrder α] [Finite α] (G H : α → ℂ)
    (h : ∀ A : α, ∑ᶠ B : {B : α // B ≤ A}, G B.1 = ∑ᶠ B : {B : α // B ≤ A}, H B.1) (A : α) :
    G A = H A := by
  classical
  induction A using WellFoundedLT.induction with
  | ind A ih =>
    haveI : Fintype {B : α // B ≤ A} := Fintype.ofFinite _
    have h1 := h A
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A})),
      ← Finset.add_sum_erase _ (fun B : {B : α // B ≤ A} => H B.1)
        (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A}))] at h1
    have h2 : ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), G B.1 =
        ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), H B.1 := by
      refine Finset.sum_congr rfl fun B hB => ih B.1 (lt_of_le_of_ne B.2 fun e => ?_)
      exact (Finset.mem_erase.1 hB).1 (Subtype.ext e)
    rw [h2] at h1
    exact add_right_cancel h1

theorem moebius_affine_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ) (hU : 0 < Module.finrank K U)
    (hG : ∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 =
      c₀ + c * (Module.finrank K A : ℂ)) :
    G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  have key := eq_of_finsum_le_eq G
    (fun B => (if B = ⊥ then c₀ else 0) + c * oneValue (Nat.card K) (Module.finrank K B)) (fun A => by
      haveI : Fintype {B : Submodule K U // B ≤ A} := Fintype.ofFinite _
      rw [hG A, ← finsum_le_oneValue_finrank K U A, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_eq_single (⟨⊥, bot_le⟩ : {B : Submodule K U // B ≤ A})]
      · simp
      · intro B _ hB
        exact if_neg fun e => hB (Subtype.ext e)
      · intro h
        exact absurd (Finset.mem_univ _) h) ⊤
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  rw [key, if_neg top_ne_bot, zero_add, finrank_top, oneValue, if_neg hU.ne']

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
section
open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_quotient_map_span_singleton :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})],
      IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) →
      ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  intro R A _ _ _ _ _ _ f hf _ hreg n hd
  have h1 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop f A) n := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hf hreg hd
  have heq : (f • (⊤ : Submodule R A)) =
      ((Ideal.span {f}).map (algebraMap R A)).restrictScalars R := by
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop f A ≃ₗ[R] (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R A)))
  obtain ⟨rs, hl, hm, hr⟩ := (ReciprocityTheory.CA.modDepthGE_congr e n).mp h1
  refine ⟨rs.map (algebraMap R (R ⧸ Ideal.span {f})), by simp [hl], ?_, ?_⟩
  · intro r hr'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr'
    exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hm a ha)
  · exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' rs).mpr hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca
section
open IsLocalRing

namespace GlobalTheory

theorem exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim (R : Type) [CommRing R]
    [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    ∃ q : Ideal R, q.IsPrime ∧ q ≠ ⊥ ∧ q < maximalIdeal R := by
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum R), l.length = 2 :=
    Order.le_krullDim_iff.mp (by exact_mod_cast h)
  let i0 : Fin l.length := ⟨0, by omega⟩
  let i1 : Fin l.length := ⟨1, by omega⟩
  have h01 : l i0.succ = l i1.castSucc := congrArg l (Fin.ext rfl)
  have s0 := l.step i0
  have s1 := l.step i1
  rw [h01] at s0
  refine ⟨(l i1.castSucc).asIdeal, (l i1.castSucc).isPrime, ?_, ?_⟩
  · intro h0
    have : (l i0.castSucc).asIdeal < (l i1.castSucc).asIdeal := s0
    rw [h0] at this
    exact not_lt_bot this
  · exact lt_of_lt_of_le (show (l i1.castSucc).asIdeal < (l i1.succ).asIdeal from s1)
      (le_maximalIdeal (l i1.succ).isPrime.ne_top)

end GlobalTheory

namespace GlobalTheory

open Pointwise

theorem modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A]
      [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A],
      2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  intro R A _ _ _ _ _ _ _ _ hdim
  obtain ⟨hRd, hRic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  have hinj := FaithfulSMul.algebraMap_injective R A
  obtain ⟨q, hq, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim R hdim
  have hm0 : maximalIdeal R ≠ ⊥ := (bot_le.trans_lt hqm).ne'
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
  have hx' : algebraMap R A x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hreg : IsSMulRegular A x := by
    intro a b hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hx' hab

  have hmemx : ∀ a : A, a ∈ x • (⊤ : Submodule R A) ↔ a ∈ Ideal.span {algebraMap R A x} := by
    intro a
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩

  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x A) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite R (QuotSMulTop x A)
    have hsub : (maximalIdeal R : Set R) ⊆
        ⋃ p ∈ associatedPrimes R (QuotSMulTop x A), (p : Set R) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal R :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hmz : ∀ a ∈ maximalIdeal R, algebraMap R A a * z ∈ Ideal.span {algebraMap R A x} := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, hmemx] at ha
      simpa [Algebra.smul_def] using ha
    have hz : z ∉ Ideal.span {algebraMap R A x} := by
      intro hz
      apply (maximalIdeal.isMaximal R).ne_top
      rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
        Submodule.Quotient.mk_eq_zero, hmemx]
      exact hz
    set I := Ideal.span {algebraMap R A x}
    have hzq : (Ideal.Quotient.mk I z : A ⧸ I) ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hzq
    haveI hPp : P.IsPrime := hP.isPrime
    have hmP : maximalIdeal R ≤ P.comap (algebraMap R A) := by
      intro a ha
      apply hle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hmz a ha
    have hPm : P.comap (algebraMap R A) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ P).ne_top hmP).symm
    haveI : P.LiesOver (maximalIdeal R) := ⟨hPm.symm⟩
    obtain ⟨Q, hQP, hQp, hQq⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := A) P hqm
    have h1 : P.height = 1 := height_eq_one_of_mem_associatedPrimes hx' hP
    have hlt : Q.height < P.height := Ideal.height_strict_mono_of_isPrime hQP
    rw [h1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at hlt
    apply hq0
    rw [hQq.over, hlt]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
      (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 ∧
        _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ ε hζ
  have hε : ε ≠ 1 := by
    rintro rfl
    have h1 : _root_.GlobalTheory.Sandwich.root (1 : PreTilt O p) = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      exact map_one _
    have h2 : PreTilt.untilt (1 : PreTilt O p) = 1 := by simp
    rw [h1, h2] at hζ
    have hp : p ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (pow_one 1)
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp)
  have hc : (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hε
  have hmu : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    intro h
    apply hc
    rw [h]
    exact WittVector.zero_coeff _ _ _
  refine ⟨hc, hmu, fun h => hmu ?_⟩
  rw [← _root_.GlobalTheory.Sandwich.xi_mul_nu, h, mul_zero]

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHomStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (exact GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (intros; apply GlobalTheory.HomCount.nonempty_equiv_of_card_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFiltration
section
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

theorem exists_norm_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  intro L _ _ σ ϖ q h P m hm x hx hxm
  obtain ⟨x₀, hx₀, hv⟩ := h.2.2.2.2.1
  have hve : Valued.v (x₀ - σ x₀) = 1 := by rw [← Valuation.map_neg, neg_sub]; exact hv
  have he : x₀ - σ x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hve; exact zero_ne_one hve
  have hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L := by
    change Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hve, inv_one, mul_one]; exact hx₀
  let cO : intL L := ⟨_, hcO⟩
  have hcs : cO + sigO σ h.2.1 cO = 1 := by
    apply Subtype.ext
    change x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1
    have e2 : σ x₀ - x₀ = -(x₀ - σ x₀) := by ring
    rw [map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]
    field_simp
    ring
  set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι
  set πA := ι (piO h) with hπA
  have hconjπ : GlobalTheory.UTr.conj P πA = πA := by
    rw [hπA, GlobalTheory.UTr.conj_algebraMap]; congr 1; exact Subtype.ext h.2.2.1
  have hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1 := by
    have := congrArg ι hcs
    rw [map_add (f := _), map_one] at this
    rw [hι, GlobalTheory.UTr.conj_algebraMap]; rw [← this]; ring
  have h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m} := hxm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x := (GlobalTheory.UTr.mem_plus (P := P)).1 hx
  have hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a := by
    have := congrArg (GlobalTheory.UTr.conj P) ha
    rw [map_mul, map_pow, hconjπ, map_sub, map_one, hxc] at this
    rw [mul_comm, this, ← ha, mul_comm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1) := by
    rw [add_sub_cancel_left]; exact Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩
  refine ⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩
  change (x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) *
    GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}
  have e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) =
      1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a) := by
    rw [map_add (f := _), map_one, map_mul, map_pow, hconjπ, map_mul]
  rw [e1, Ideal.mem_span_singleton']
  refine ⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩
  linear_combination ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc

end GlobalTheory.NormEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralRayIteratedFDerivStatement
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) → ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  first | exact @GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | exact GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | (intros; apply GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv <;> assumption)
end

