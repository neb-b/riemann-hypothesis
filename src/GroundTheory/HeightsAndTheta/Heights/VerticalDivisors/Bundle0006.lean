module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Objects

variable {K : Type*} [Field K] [NumberField K]

theorem comap_maximalIdeal_parDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (IsLocalRing.maximalIdeal (ParDVR e n v)).comap (algebraMap (𝓞 K) (ParDVR e n v)) = v.asIdeal := by
  have h1 : algebraMap (𝓞 K) (ParDVR e n v) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)).comp C :=
    IsScalarTower.algebraMap_eq _ _ _
  have h2 : (IsLocalRing.maximalIdeal (ParDVR e n v)).comap
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) = parPrime e n v :=
    Localization.AtPrime.under_maximalIdeal
  rw [h1, ← Ideal.comap_comap, h2]
  ext x
  simp only [Ideal.mem_comap, parPrime]
  constructor
  · intro hx
    rw [MvPolynomial.mem_map_C_iff] at hx
    simpa using hx 0
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

def resToKappa (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.ResidueField →+* (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  Ideal.ResidueField.map v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
    (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm

def parYκ (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Par e n → (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  fun p => algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField (parY e n v p)

end Objects

def SpecCompDim.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      IsProjPrime (reduceMod v W) ∧
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ reduceMod v W) = ((e + 1 : ℕ) : WithBot ℕ∞)

def ChartDomain.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n),
    Q.IsPrime → (∀ c : D, C c ∈ Q → c = 0) → X j ∉ Q →
      IsDomain (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)) ∧
        Function.Injective (algebraMap D
          (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)))

def SecAlgField.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsField (SecAlg (Q.map (MvPolynomial.map (algebraMap k (FractionRing (MvPolynomial (Par e n) k)))))
        (fun p => algebraMap (MvPolynomial (Par e n) k) (FractionRing (MvPolynomial (Par e n) k)) (X p)))

def ParFracIsFractionRing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (parToFrac e n v).toAlgebra
    IsFractionRing (ParDVR e n v) (ParFrac K e n)

def ResidueAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (resToKappa e n v).toAlgebra
    AlgebraicIndependent v.asIdeal.ResidueField (parYκ e n v)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem isChowForm_C_mul {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := hc.isUnit.map C
  rw [hf.2 g, IsUnit.mul_left_dvd hu]

theorem specFirst_C_mul {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by
  simp [specFirst]

theorem Main.proof (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem isHomogeneous_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by
  classical
  rw [specRest, g.as_sum, eval₂_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [eval₂_monomial, Finsupp.prod]
  have hdeg : ∀ ij : Fin (e + 1) × Fin n,
      (Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
        (fun i => C (y (.inl (i, ij.2)))) ij.1 : MvPolynomial (Fin n) S).IsHomogeneous
        (groupWeight (e + 1) n ij 0) := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [groupWeight] using isHomogeneous_X (R := S) j
    · have h0 : groupWeight (e + 1) n (i.succ, j) 0 = 0 := by simp [groupWeight]
      rw [h0]
      exact isHomogeneous_C _ _
  have hsum : ∑ ij ∈ m.support, groupWeight (e + 1) n ij 0 * m ij = d := by
    have hw := hg (mem_support_iff.mp hm)
    have h0 := congrFun hw 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h := (isHomogeneous_C (σ := Fin n) (φ (AddMonoidAlgebra.coeff g m))).mul
    (IsHomogeneous.prod m.support _ _ fun ij _ => (hdeg ij).pow (m ij))
  rw [zero_add, hsum] at h
  exact h

theorem isHomogeneous_det_linear {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => N (τ i) i) (fun _ => 1) fun i _ => hN (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  simpa using (isHomogeneous_C σ ((τ.sign : ℤ) : R)).mul hp

theorem ChowSecDegree.proof (h1 : ChowNormForm.Statement) (h2 : ChowFormHomog.Statement)
    (h3 : NormFormEval.Statement) : ChowSecDegree.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  classical
  obtain ⟨hfin, c, hc, heq⟩ := h1 k E n e Q g y hy hQ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  have : Module.Finite E (SecAlg QE y) := hfin
  have : Module.Free E (SecAlg QE y) := Module.Free.of_divisionRing E (SecAlg QE y)
  let b : Module.Basis (Module.Free.ChooseBasisIndex E (SecAlg QE y)) E (SecAlg QE y) :=
    Module.Free.chooseBasis E (SecAlg QE y)
  have hN : (normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    rw [normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hone : (∑ j, algebraMap E (SecAlg QE y) (y (.inr j)) * secCoord QE y j) = 1 := by
    have hmem : chartForm y - 1 ∈ secIdeal QE y := Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h := Ideal.Quotient.eq.mpr hmem
    rw [map_one] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [chartForm, linForm, secCoord, map_sum, map_mul]
    rfl
  have hN0 : normForm (R := E) (SecAlg QE y) (secCoord QE y) ≠ 0 := by
    intro h0
    have hv := h3 E (SecAlg QE y) n (secCoord QE y) (fun j => y (.inr j))
    rw [h0, map_zero, hone, map_one] at hv
    exact zero_ne_one hv
  have hG : (specRest (algebraMap k E) g y).IsHomogeneous (chowDegree Q (e + 1)) :=
    isHomogeneous_specRest _ (h2 k n (e + 1) Q g hg) y
  rw [heq] at hG
  have hCN : (C c * normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    simpa using hN.C_mul c
  exact hCN.inj_right hG (mul_ne_zero (C_ne_zero.mpr hc) hN0)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFiniteOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FiniteOrd.proof : FiniteOrd.Statement := by
  intro R B _ _ _ _ _ _ b hb 𝔫
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B

  have hB : ringKrullDim B ≤ ringKrullDim R :=
    Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum B ↦
        (⟨Ideal.comap (algebraMap R B) p.asIdeal, inferInstance⟩ : PrimeSpectrum R))
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap (R := R) (A := B) hpq)
  have hS : ringKrullDim (Localization.AtPrime 𝔫.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫.asIdeal (Localization.AtPrime 𝔫.asIdeal)]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans (hB.trans ?_)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R]
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫.asIdeal) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hS)
  have hbB : b ∈ nonZeroDivisors B := by
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ ?_, fun x hx ↦ hb (by simpa [mul_comm, mul_zero] using hx)⟩
    exact hb (by simpa [mul_comm, mul_zero] using hx)
  have hbS : algebraMap B (Localization.AtPrime 𝔫.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime 𝔫.asIdeal) :=
    IsLocalization.map_nonZeroDivisors_le 𝔫.asIdeal.primeCompl _ ⟨b, hbB, rfl⟩
  exact Ring.ord_ne_top hbS

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain WithZero

noncomputable section

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem exists_C_mul_eq_C_pow_mul {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩

end Dedekind

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_map_of_coeff_notMem (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem adicAbv_of_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  rw [WithZero.log_exp, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

theorem irreducible_algebraMap_C (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  have hnu : ¬ IsUnit (φ (C a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    exact fun h => h (Ideal.mem_map_of_mem _ hav)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)
  obtain ⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl),
      IsLocalization.mk' (ParDVR e n v) x s = ϖ := by
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ
    exact ⟨x, s, hxs⟩
  have hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1) := by
    rw [pow_one]
    by_contra hx
    exact hϖ.not_isUnit
      ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha 1 hx
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h) := by
    have h2 := congrArg φ hth
    rw [map_mul, map_mul, pow_one] at h2
    calc φ x = ↑htu.unit⁻¹ * (φ (C t) * φ x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring
  have hϖ' : IsLocalization.mk' (ParDVR e n v) x s =
      φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hx2]
    ring
  rw [hϖ'] at hϖ
  rcases hϖ.isUnit_or_isUnit rfl with hu | hu
  · exact (hnu hu).elim
  · exact (irreducible_mul_isUnit hu).mp hϖ

end NumberField

theorem GaussDVR.proof (h1 : ParDVRIsDVR.Statement) : GaussDVR.Statement := by
  intro K _ _ e n v g hg
  have := h1 K e n v
  classical
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  let μ : 𝓞 K → ℕ := fun b => multiplicity v.asIdeal (Ideal.span {b})
  have hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b := by
    intro b hb k
    rw [← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]
    simp only [μ]
    omega
  have hne : g.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)
  obtain ⟨d0, hd0, hmin⟩ := g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))
  set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm
  have hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : g.coeff d = 0
    · rw [hd]
      exact Ideal.zero_mem _
    · exact (hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha m hgm
  have hb0 : g.coeff d0 ≠ 0 := mem_support_iff.mp hd0
  have hh : h.coeff d0 ∉ v.asIdeal := by
    intro hmem
    have hc := congrArg (AddMonoidAlgebra.coeff · d0) hth
    rw [coeff_C_mul, ← C_pow, coeff_C_mul] at hc
    have h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1) := by
      rw [hc, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem
    have h4 := (v.intValuation_le_pow_iff_mem _ _).mpr h3
    rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem,
      hval _ hb0] at h4
    omega
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hhu : IsUnit (φ h) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro hP
    exact hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)
  have hord : Ring.ord (ParDVR e n v) (φ g) = m := by
    rw [Ring.ord_eq_addVal]
    have h0 := congrArg φ hth
    rw [map_mul φ, map_mul φ, map_pow φ] at h0
    have h2 := congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha),
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hhu] at h2
    simpa using h2
  have hK0 := congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth
  rw [map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)),
    map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C] at hK0
  have hK := congrArg (gaussNorm v) hK0
  rw [← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow,
    adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding,
    (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one] at hK
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecIdealOfPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def toSecB {K : Type*} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) : MvPolynomial (Fin n) (𝓞 K) →+* SecB e I v :=
  (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))).comp
    (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

def SecIdealOfPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      (secIdealOf e I v W).IsPrime ∧ (secIdealOf e I v W).comap (toSecB e I v) = W

end

end GroundTheory.Heights₂.Heights.Vertical
end

