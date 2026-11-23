module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarProperSubmoduleEqZeroModuleTopology
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Set Pointwise Metric

namespace GlobalTheory.HaarNullSub

theorem addHaar_submodule_eq_zero (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V]
    [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (s : Submodule F V) (hs : s ≠ ⊤) : μ (s : Set V) = 0 := by
  haveI := hμ
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousSMul F V := inferInstance

  let e₀ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e₀ := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
  have hc' : Continuous e₀.symm := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) :=
    { e₀.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }

  have hcl : IsClosed (s : Set V) := by
    have h1 : IsClosed ((s.map e₀.toLinearMap : Submodule F _) : Set (Fin (Module.finrank F V) → F)) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : (s : Set V) = h ⁻¹' ((s.map e₀.toLinearMap : Submodule F _) : Set _) := by
      ext v
      simp [h, Submodule.mem_map]
    rw [h2]; exact h1.preimage h.continuous

  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, c0, c1⟩ := NormedField.exists_norm_lt_one F
  let u : ℕ → V := fun n => c ^ n • x
  have hu : Tendsto u atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one c1
    simpa [u] using this.smul_const x
  have hC : IsCompact (insert 0 (range u)) := hu.isCompact_insert_range

  have hdisj : ∀ A ⊆ (s : Set V), Pairwise (Function.onFun Disjoint fun n => {u n} + A) := by
    intro A hA m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨_, rfl, a, ha, rfl⟩ ⟨_, rfl, b, hb, hab⟩
    apply hx
    have hne : c ^ m - c ^ n ≠ 0 := by
      intro h0
      apply hmn
      have : ‖c‖ ^ m = ‖c‖ ^ n := by rw [← norm_pow, ← norm_pow, sub_eq_zero.mp h0]
      exact pow_right_injective₀ c0 (ne_of_lt c1) this.symm |>.symm
    have hmem : (c ^ m - c ^ n) • x ∈ s := by
      have : (c ^ m - c ^ n) • x = b - a := by
        simp only [u] at hab
        rw [sub_smul, show c ^ m • x = c ^ n • x + b - a by rw [hab]; abel]; abel
      rw [this]; exact s.sub_mem (hA hb) (hA ha)
    exact (Submodule.smul_mem_iff s hne).mp hmem

  have key : ∀ R : ℝ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 R) = 0 := by
    intro R
    set A := (s : Set V) ∩ h ⁻¹' closedBall 0 R with hAdef
    have hAc : IsCompact A := by
      have hK : IsCompact (h ⁻¹' closedBall 0 R) := by
        rw [← h.image_symm]
        exact (isCompact_closedBall (0 : Fin (Module.finrank F V) → F) R).image h.symm.continuous
      exact hK.inter_left hcl
    have hAm : MeasurableSet A := hcl.measurableSet.inter (isClosed_closedBall.preimage h.continuous).measurableSet
    by_contra hne
    apply lt_irrefl (⊤ : ENNReal)
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, μ A := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
      _ = ∑' n : ℕ, μ ({u n} + A) := by
        congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
      _ = μ (⋃ n, {u n} + A) := Eq.symm <| measure_iUnion (hdisj A inter_subset_left) fun n => by
        simpa only [image_add_left, singleton_add] using (measurable_const_add (-u n)) hAm
      _ ≤ μ (insert 0 (range u) + A) := by
        apply measure_mono
        refine iUnion_subset fun n => add_subset_add ?_ Subset.rfl
        exact singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_range_self n))
      _ < ⊤ := (hC.add hAc).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc
    μ (s : Set V) ≤ ∑' n : ℕ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 n) := by
      conv_lhs => rw [← inter_univ (s : Set V), ← preimage_univ (f := h), ← iUnion_closedBall_nat 0,
        preimage_iUnion, inter_iUnion]
      exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]

end GlobalTheory.HaarNullSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemSurjectivityAndCountOrderZero
section
namespace GlobalTheory.PMonE

theorem glOnto_zero_and_glCount_zero : GLOnto 0 ∧ GLCount 0 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM b hb
    obtain ⟨x, hx, -⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) b hb
    exact ⟨x, hx⟩
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM _
    obtain ⟨y, hy, huniq⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) 0 (fun i => by simp)
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    exact ⟨⟨y, hy⟩, fun z => Subtype.ext (huniq z.1 z.2)⟩

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
section
noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open Polynomial

theorem mem_adjoin_of_pow_eq_one_of_isUnit {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hzR : IsIntegral R z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    simp [eval₂_sub, hz]
  have hzF : IsIntegral F z := hzR.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzF hadj
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzF hadj
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)
  rw [hgen] at hmem
  haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by
    rw [Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L,
      map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff] at hx
    exact hx
  have hIntAe : ∀ p : R[X], IsIntegral R (aeval z p) := fun p =>
    adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)
  set m := minpoly R z with hm
  obtain ⟨h, hmh⟩ : m ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])
  have hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h := by
    have := congrArg (fun p => aeval z (derivative p)) hmh
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add (f := _), map_mul] at this
    have h0 : aeval z m = 0 := minpoly.aeval R z
    simpa [h0] using this
  have hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)
  obtain ⟨ra, hra⟩ := hint _ (hIntAe (derivative m))
  obtain ⟨rb, hrb⟩ := hint _ (hIntAe h)
  obtain ⟨rz, hrz⟩ := hint _ hzR
  have hinj := IsFractionRing.injective R F
  have hrzN : rz ^ N = 1 := hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])
  have hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1) := by
    apply hinj
    have hNL : ((N : L)) = algebraMap F L (N : F) := (map_natCast _ _).symm
    rw [map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL,
      Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]
  have hra_unit : IsUnit ra := by
    have : IsUnit (ra * rb) := by
      rw [hprod]
      have hrzu : IsUnit rz := isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩
      exact (hN.pow _).mul (hrzu.pow _)
    exact isUnit_of_mul_isUnit_left this
  have hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]
  obtain ⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) :=
    ((isUnit_one.neg).pow _).mul hra_unit
  rw [hdisc, ← hv, algebraMap_smul] at hmem
  have : y = (↑v⁻¹ : R) • ((v : R) • y) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _

end GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  intro K K' d φ hφ hd z hz hadj y hy
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  have hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    haveI := Fintype.ofFinite (ResidueField K.O)
    have hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0 := by
      rw [← K.card_res, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hq : 1 ≤ K'.q ^ 2 := by
      rw [hφ.1, ← pow_mul, mul_comm, pow_mul]
      apply Nat.one_le_pow
      rw [← K.card_res]; exact Nat.card_pos
    rw [Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.2 one_ne_zero
  exact mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDvd
section
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.LagIdem

variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]

noncomputable def lagPoly (a : ι → R) (i : ι) : R[X] :=
  C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) *
    ∏ j ∈ Finset.univ.erase i, (X - C (a j))

end GlobalTheory.LagIdem

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_eq_zero_of_dvd_of_aeval_eq_zero {M : E} {p q : R[X]} (hp : aeval M p = 0) (h : p ∣ q) :
    aeval M q = 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [hp]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
private lemma prod_X_sub_C_dvd_sum_lagPoly_sub_one :
    ∏ j, (X - C (a j)) ∣ ∑ i, _root_.GlobalTheory.LagIdem.lagPoly a i - 1 := by
  refine Fintype.prod_dvd_of_coprime
    (fun i j hij => isCoprime_X_sub_C_of_isUnit_sub (hu i j hij)) fun k => ?_
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_one, eval_finsetSum, sub_eq_zero,
    Finset.sum_eq_single k]
  · simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact Ring.inverse_mul_cancel _
      (IsUnit.prod_iff.mpr fun j hj => hu k j (Finset.ne_of_mem_erase hj).symm)
  · intro i _ hik
    simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩) (sub_self _))
  · intro h
    exact absurd (Finset.mem_univ k) h

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_lagPoly_eq_lagIdem (M : E) (a : ι → R) (i : ι) :
    aeval M (_root_.GlobalTheory.LagIdem.lagPoly a i) = _root_.GlobalTheory.Pat.lagIdem M a i := by
  simp [_root_.GlobalTheory.LagIdem.lagPoly, _root_.GlobalTheory.Pat.lagIdem, Algebra.smul_def]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma prod_X_sub_C_eq_mul_prod_erase (a : ι → R) (i : ι) :
    ∏ j, (X - C (a j)) = (X - C (a i)) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
omit hu in
private lemma prod_X_sub_C_dvd_lagPoly_mul_of_ne {i j : ι} (hij : i ≠ j) :
    ∏ l, (X - C (a l)) ∣ _root_.GlobalTheory.LagIdem.lagPoly a i * _root_.GlobalTheory.LagIdem.lagPoly a j := by
  rw [prod_X_sub_C_eq_mul_prod_erase a i]
  have h : X - C (a i) ∣ ∏ l ∈ Finset.univ.erase j, (X - C (a l)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  obtain ⟨q, hq⟩ := h
  refine ⟨C (Ring.inverse (∏ l ∈ Finset.univ.erase i, (a i - a l))) *
    C (Ring.inverse (∏ l ∈ Finset.univ.erase j, (a j - a l))) * q, ?_⟩
  simp only [_root_.GlobalTheory.LagIdem.lagPoly, hq]
  ring

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma commute_aeval_of_commute' {T M : E} (h : Commute T M) (p : R[X]) :
    Commute T (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact Commute.mul_right (show Commute T (algebraMap R E c) from (Algebra.commutes c T).symm)
      (h.pow_right n)

open TensorProduct Polynomial IsLocalRing in
theorem _root_.GlobalTheory.lagIdem_spec : ∀ (R E ι : Type) [CommRing R]
    [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : E) (a : ι → R),
    (∀ i j, i ≠ j → IsUnit (a i - a j)) → Polynomial.aeval M (∏ j, (X - C (a j))) = 0 →
    CompleteOrthogonalIdempotents (_root_.GlobalTheory.Pat.lagIdem M a) ∧
      (∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i = a i • _root_.GlobalTheory.Pat.lagIdem M a i) ∧
      M = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i ∧
      ∀ (T : E) i, Commute T M → Commute T (_root_.GlobalTheory.Pat.lagIdem M a i) := by
  intro R E ι _ _ _ _ _ _ M a hu hM
  have hsum : ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i = 1 := by
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_sum_lagPoly_sub_one a hu)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, aeval_lagPoly_eq_lagIdem, sub_eq_zero] using h
  have hortho : ∀ i j, i ≠ j →
      _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a j = 0 := by
    intro i j hij
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_lagPoly_mul_of_ne a hij)
    simpa [aeval_lagPoly_eq_lagIdem] using h
  have hidem : ∀ i, IsIdempotentElem (_root_.GlobalTheory.Pat.lagIdem M a i) := by
    intro i
    have h : _root_.GlobalTheory.Pat.lagIdem M a i * ∑ j, _root_.GlobalTheory.Pat.lagIdem M a j =
        _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a i := by
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hji => hortho i j (Ne.symm hji))
        (fun h => absurd (Finset.mem_univ i) h)]
    rw [hsum, mul_one] at h
    exact h.symm
  have heigen : ∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i =
      a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
    intro i
    have hdvd : ∏ j, (X - C (a j)) ∣ (X - C (a i)) * _root_.GlobalTheory.LagIdem.lagPoly a i := by
      refine ⟨C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))), ?_⟩
      rw [prod_X_sub_C_eq_mul_prod_erase a i, _root_.GlobalTheory.LagIdem.lagPoly]
      ring
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM hdvd
    rw [map_mul, aeval_lagPoly_eq_lagIdem, map_sub, aeval_X, aeval_C, sub_mul,
      sub_eq_zero, ← Algebra.smul_def] at h
    exact h
  refine ⟨⟨⟨hidem, fun i j hij => hortho i j hij⟩, hsum⟩, heigen, ?_, ?_⟩
  · calc M = M * ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i := by rw [hsum, mul_one]
      _ = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => heigen i
  · intro T i hT
    rw [← aeval_lagPoly_eq_lagIdem]
    exact commute_aeval_of_commute' hT _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosedContinuumRingEquivComplexExtending
section
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem algClosed_continuum_ringEquiv_complex_extending :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C], Cardinal.mk C = Cardinal.continuum →
      ∀ (K : Type) [Field K] [NumberField K] (i : K →+* C) (s : K →+* ℂ),
        ∃ e : C ≃+* ℂ, ∀ x, e (i x) = s x := by
  intro C _ _ _ hC K _ _ i s
  obtain ⟨e₀⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
    (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [hC, Cardinal.mk_complex]))
  haveI : Countable K :=
    Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K (e₀.toRingHom.comp i) s
  exact ⟨e₀.trans τ, fun x => hτ x⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapMemNonZeroDivisorsAdicCompletion
section
namespace GlobalTheory.BK

open PowerSeries Filter Topology

theorem algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩

theorem Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
  have hE : E (K := K) l e ≠ 0 := by
    intro h
    have hcoeff := congrArg (coeff e) h
    rw [E, map_add, coeff_X_pow_self, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_of_ne_zero (NeZero.ne e), add_zero, map_zero] at hcoeff
    exact one_ne_zero hcoeff
  let s : invL l (A O K) :=
    ⟨E (K := K) l e, by
      unfold E
      exact add_mem (pow_mem HasU.X_mem e) (natCast_mem _ l)⟩
  exact algebraMap_mem_nonZeroDivisors_adicCompletion (s := s)
    (mem_nonZeroDivisors_of_ne_zero fun h => hE (congrArg Subtype.val h))

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHom
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.InvMap

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  have hp : (Y.1.map φ) ^ i = (Y.1 ^ i).map φ := by
    have := map_pow φ.mapMatrix Y.1 i
    simpa only [RingHom.mapMatrix_apply] using this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mom, glMap, hp, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

theorem inv_glMap (Y : Gl r k) : GlobalTheory.JR.inv (glMap φ Y) = (GlobalTheory.JR.inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, glMap, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_glMap φ Y i

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    simp only [sec, companion, glMap, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · funext i
    simp only [sec, glMap]
    split_ifs <;> simp

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  rw [Delta, Delta, RingHom.map_det]
  congr 1
  ext i j
  simp only [hankel, sec_map, mom_glMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem mom_glMap_eq_map_mom (ψ : k →+* k') (Y : _root_.GlobalTheory.JR.Gl r k) (n : ℕ) :
    _root_.GlobalTheory.JR.mom (_root_.GlobalTheory.JR.Step.glMap ψ Y) n = ψ (_root_.GlobalTheory.JR.mom Y n) := by
  unfold _root_.GlobalTheory.JR.mom _root_.GlobalTheory.JR.Step.glMap
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_pow]
  rfl

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem sec_map_eq_glMap_sec (ψ : k →+* k') (a : _root_.GlobalTheory.JR.Inv r k) :
    _root_.GlobalTheory.JR.sec (a.map ψ) = _root_.GlobalTheory.JR.Step.glMap ψ (_root_.GlobalTheory.JR.sec a) := by
  unfold _root_.GlobalTheory.JR.sec _root_.GlobalTheory.JR.Inv.map _root_.GlobalTheory.JR.Step.glMap
  simp only [_root_.GlobalTheory.JR.ImgSec.companion_map, Prod.mk.injEq, true_and, and_true]
  funext i
  split_ifs <;> simp


open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
theorem _root_.GlobalTheory.JR.Step.InvMap.inv_and_Delta_map : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ),
    (∀ Y : _root_.GlobalTheory.JR.Gl r k, _root_.GlobalTheory.JR.inv (_root_.GlobalTheory.JR.Step.glMap φ Y) = (_root_.GlobalTheory.JR.inv Y).map φ) ∧
      (∀ a : _root_.GlobalTheory.JR.Inv r k, _root_.GlobalTheory.JR.Delta (a.map φ) = φ (_root_.GlobalTheory.JR.Delta a)) := by
  intro k k' _ _ φ r
  refine ⟨fun Y => ?_, fun a => ?_⟩
  · unfold _root_.GlobalTheory.JR.inv _root_.GlobalTheory.JR.Inv.map
    simp only [mom_glMap_eq_map_mom]
    refine Prod.ext ?_ rfl
    funext i
    simp [_root_.GlobalTheory.JR.Step.glMap, Matrix.charpoly_map]
  · unfold _root_.GlobalTheory.JR.Delta
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.JR.hankel, sec_map_eq_glMap_sec, mom_glMap_eq_map_mom]

end GlobalTheory.JR.Step.InvMap
end

