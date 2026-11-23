module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtRho1OfMemIdealPower
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem exists_map_eq_of_mem_sq_sup_pow {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (l N : ℕ) (π : A) (z u : B) (hπ : φ π = z) (hu : (l : B) = z * u) (a : A)
    (ha : a ∈ Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) :
    ∃ x y : B, φ a = (l : B) ^ 2 * x + z ^ N * y := by
  have hsub : Ideal.span {(l : B), z} ≤ Ideal.span {z} := by
    rw [Ideal.span_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · rw [SetLike.mem_coe, hu]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mem_span_singleton_self z
  have hmap : Ideal.map φ (Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) ≤
      Ideal.span {(l : B) ^ 2, z ^ N} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_pair]
    simp only [map_pow, map_natCast, hπ]
    refine sup_le (Ideal.span_mono (by simp)) ?_
    calc Ideal.span {(l : B), z} ^ N ≤ Ideal.span {z} ^ N := Ideal.pow_right_mono hsub N
      _ = Ideal.span {z ^ N} := Ideal.span_singleton_pow z N
      _ ≤ _ := Ideal.span_mono (by simp)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hmap (Ideal.mem_map_of_mem φ ha))
  exact ⟨x, y, by rw [← hxy]; ring⟩

theorem norm_kap_lt_rho1_of_mem_sq_sup_pow :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  intro l _ LL j n f o φ ζ hj hζ hφ a ha k
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hζn : ‖(ζ : PadicComplex l) - 1‖ =
      (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) :=
    norm_primitiveRoot_sub_one l j hj _ hζ
  have hlnorm : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := norm_natCast_prime_padicComplex l
  have hz0 : (ζ : PadicComplex l) - 1 ≠ 0 := by
    rw [← norm_pos_iff, hζn]
    positivity
  have hle : ‖(l : PadicComplex l)‖ ≤ ‖(ζ : PadicComplex l) - 1‖ := by
    rw [hlnorm, hζn, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hl.le
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) := one_le_pow₀ hl.le
    have h2 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by nlinarith
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
    exact h2
  let u : OC l := ⟨(l : PadicComplex l) / ((ζ : PadicComplex l) - 1), by
    rw [mem_OC, norm_div]
    exact div_le_one_of_le₀ hle (norm_nonneg _)⟩
  have hu : ((l : ℕ) : OC l) = (ζ - 1) * u := by
    apply Subtype.ext
    push_cast
    change (l : PadicComplex l) =
      ((ζ : PadicComplex l) - 1) * ((l : PadicComplex l) / ((ζ : PadicComplex l) - 1))
    field_simp
  have huO : ((l : ℕ) : OCO LL) =
      ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * (u ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hu,
      ← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]
  obtain ⟨x, y, hxy⟩ := exists_map_eq_of_mem_sq_sup_pow φ l (l ^ j) letπ _ _ hφ huO a ha
  have e1 : ((l : ℕ) : OCO LL) ^ 2 = (((l : ℕ) : OC l) ^ 2) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_pow, map_natCast]
  have e2 : ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) ^ (l ^ j) =
      ((ζ - 1) ^ (l ^ j)) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hxy, kap_add, e1, e2, kap_tmul_one_mul, kap_tmul_one_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hlnorm]
    calc ((l : ℝ)⁻¹) ^ 2 * ‖kap o x k‖ ≤ ((l : ℝ)⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o x k) (by positivity)
      _ = (l : ℝ) ^ (-(2 : ℝ)) := by
          rw [mul_one, inv_pow, Real.rpow_neg (by positivity)]
          norm_cast
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl]
          have h3 : -1 ≤ -(1 : ℝ) / ((l : ℝ) - 1) := by
            rw [neg_div, neg_le_neg_iff, div_le_one hq]
            linarith
          linarith
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hζn]
    calc ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * ‖kap o y k‖
        ≤ ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o y k) (by positivity)
      _ = (l : ℝ) ^ (-(l : ℝ) / ((l : ℝ) - 1)) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          have hp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by positivity
          have hpow : ((l ^ j : ℕ) : ℝ) = (l : ℝ) * (l : ℝ) ^ (j - 1) := by
            rw [Nat.cast_pow, ← pow_succ']
            congr 1
            omega
          rw [hpow]
          field_simp
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl, div_lt_div_iff_of_pos_right hq]
          linarith

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem actMat_props {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t)
    [CommRing C] (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N)
    (A : O → Matrix (Fin d) (Fin d) C) (hA : ∀ a i j, A a i j = φ (b.repr (a • b j) i)) :
    (∀ a a', A (a + a') = A a + A a') ∧ (∀ (x : Z) a, A (x • a) = φ x • A a) ∧ A 1 = 1 ∧
      ∀ a a', A (a * a') = A a * A a' := by
  have hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t) := by
    intro a x t
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  refine ⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩
  · ext i j
    simp only [hA, Matrix.add_apply, add_smul, map_add (f := _), Finsupp.add_apply]
  · ext i j
    have hx : (x • a) • b j = x • (a • b j) := by
      rw [Algebra.smul_def, mul_smul, ← hs]
    simp only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · ext i j
    rw [hA, one_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]
  · ext i j
    rw [Matrix.mul_apply, hA, mul_smul]
    conv_lhs => rw [← b.sum_repr (a' • b j)]
    rw [Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
      smul_eq_mul, map_mul, hA]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {l : ℕ} [Fact l.Prime]

theorem lamMul_lam_add {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x y : OCO LL) :
    lam o A (x + y) = lam o A x + lam o A y := by
  simp only [lam, kap_add, add_smul, Finset.sum_add_distrib]

theorem lamMul_lam_zero {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) :
    lam o A 0 = 0 := by
  simp only [lam, kap_zero, zero_smul, Finset.sum_const_zero]

theorem lam_mul_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  intro l _ K LL T d f M A o h
  letI := zlMod LL T
  obtain ⟨b, -, hA⟩ := h
  let φ : ℤ_[l] →+* PadicComplex l := (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, φ x = zC x := fun _ => rfl
  obtain ⟨Pa, Ps, P1, Pm⟩ := actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T)
    (fun _ _ => rfl) φ b A (fun a i j => hA a i j)
  have hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k) := by
    intro a
    have e := map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ
    simp only [AddMonoidHom.mk'_apply, o.sum_repr] at e
    rw [e]
    simp only [Ps, hφ]
  have ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a := by
    intro c a
    rw [hsum a, Finset.smul_sum]
    simp only [lam, kap_tmul, mul_smul]
  refine ⟨ht, P1, Pm, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [lamMul_lam_zero]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp [lamMul_lam_zero]
    | tmul c' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPowe
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp.Coord

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem inC_zero (F : IntermediateField ℚ_[l] (Om l)) : (0 : PadicComplex l) ∈ inC F :=
  ⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩

theorem inC_add {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x + y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩

theorem inC_mul {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x * y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩

theorem inC_zC (F : IntermediateField ℚ_[l] (Om l)) (x : ℤ_[l]) : zC x ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩

theorem inC_sum {F : IntermediateField ℚ_[l] (Om l)} {ι : Type} (s : Finset ι)
    (g : ι → PadicComplex l) (h : ∀ i ∈ s, g i ∈ inC F) : ∑ i ∈ s, g i ∈ inC F :=
  Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h

theorem kap_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {ι : Type}
    (s : Finset ι) (g : ι → OCO LL) (k : Fin f) :
    kap o (∑ i ∈ s, g i) k = ∑ i ∈ s, kap o (g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]

theorem kap_mul_one_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (x : OCO LL) (a : ↥(OL LL)) (k : Fin f) :
    kap o (x * ((1 : OC l) ⊗ₜ[ℤ_[l]] a)) k = ∑ j, kap o x j * zC (o.repr (o j * a) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]
  rw [Finset.sum_mul, kap_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
    kap_tmul, smul_eq_mul, mul_one, mul_one]
  rfl

theorem let_split {O : Type} [CommRing O] {n : ℕ} [NeZero n] (a : LetA O n) :
    ∃ a' : LetA O n, a = ∑ i, letE i * algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i))
      + letπ * a' := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]
    rw [add_comm]
    exact PowerSeries.eq_X_mul_shift_add_const (a j)
  · intro i _ hij
    simp [letE, Pi.single_eq_of_ne hij.symm]
  · simp

theorem coord (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n]
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l)
    (hO : ∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a)
    (hπ : φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) (hc : ‖(c : PadicComplex l)‖ < 1)
    (hcF : (c : PadicComplex l) ∈ inC (Ks K m))
    (hE : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) :
    ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  haveI := GlobalTheory.TateDecomp.finite_Ks K m
  have hcl : IsClosed (intC (Ks K m)) := (GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed
  have key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m),
      ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r := by
    intro N k
    induction N with
    | zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha⟩ := let_split a
      obtain ⟨s, hs, r, hr, h⟩ := ih a'
      refine ⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k
        + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩
      · rw [kap_mul_one_tmul]
        exact inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)
      · have e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))
            + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a' := by
          refine (congrArg φ ha).trans ((φ.map_add _ _).trans ?_)
          congr 1
          · refine (map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
            exact (φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))
          · exact (φ.map_mul _ _).trans (congrArg (· * φ a') hπ)
        rw [e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]
  intro a k
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hc
  obtain ⟨s, hs, r, hr, h⟩ := key N k a
  have hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) hr
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · have e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r) := by rw [h]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)
    rw [norm_neg]
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)
  · rw [dist_eq_norm, h, add_sub_cancel_left]
    exact hb.trans_lt hN

end GlobalTheory.Cyc.Decomp.Coord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowMulInvPowMemAinfFilLattice
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem exists_exponent_small {l s : ℕ} (hl : l.Prime) (hs : Lev l s) (M n k : ℕ) (hM : 1 ≤ M)
    (hk : 2 * (M + n) ≤ k) : ∃ N : ℕ, k + 1 ≤ (l - 1) * N ∧ N + M - 1 + n ≤ s * k := by
  obtain ⟨h1, h2⟩ := hs
  by_cases h : l = 2
  · refine ⟨k + 1, by subst h; omega, ?_⟩
    have := Nat.mul_le_mul_right k (h2 h)
    omega
  · have h3 : 2 ≤ l - 1 := by have := hl.two_le; omega
    refine ⟨k / 2 + 1, ?_, ?_⟩
    · have := Nat.mul_le_mul_right (k / 2 + 1) h3
      omega
    · have := Nat.mul_le_mul_right k h1
      omega

theorem pow_mul_inv_pow_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ)
    (hs : Lev l s) (u : P.R.BdR) (hu : u ∈ FilB P 0) (hx : io AI AI.π₁ * u = 1) (M n : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l,
      (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  refine ⟨2 * (M + n), fun k hk a => ?_⟩
  have hu' : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu (k + 1)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · apply FilB_le_Lat
    have := FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * a)) hu'
    simpa only [map_mul, map_pow, map_natCast, Nat.cast_zero] using this
  obtain ⟨N, hN1, hN2⟩ := exists_exponent_small (Fact.out : l.Prime) hs M n k hM hk
  obtain ⟨a', b', hab⟩ := Ideal.mem_span_pair.mp (_root_.GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator l P AI (k + 1) N M hM hN1)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hN2
  have hio := congrArg (io AI) hab
  simp only [map_mul, map_pow, map_natCast, map_add (f := _)] at hio
  have hxk : io AI AI.π₁ ^ (k + 1) * u ^ (k + 1) = 1 := by rw [← mul_pow, hx, one_pow]
  have hξ : io AI AI.ξ ^ M ∈ FilB P (M : ℤ) := by simpa using FilB_pow (io_ξ_mem AI) M
  refine ⟨((l : ℕ) : Ainf l) ^ e * a * a', ?_⟩
  have := FilB_zero_mul
    (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * ((l : ℕ) : Ainf l) ^ e * a * b')) hu') hξ
  convert this using 1
  rw [he, pow_add, pow_add _ (N + M - 1), ← hio]
  simp only [map_mul, map_pow, map_natCast]
  linear_combination ((l : P.R.BdR) ^ n * (l : P.R.BdR) ^ e * io AI a * io AI a') * hxk

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCount
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

theorem card_eq_finrank_mul_card {Z O R T : Type} [CommRing Z] [Nontrivial Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing R] [Nontrivial R] [Algebra O R]
    [AddCommGroup T] [Module O T] [Module.Free O T] [Module Z T] [IsScalarTower Z O T]
    {d : ℕ} (b : Module.Basis (Fin d) Z T) {ι : Type} [Fintype ι] (v : ι → R ⊗[O] T)
    (h1 : LinearIndependent R v) (h2 : Submodule.span R (Set.range v) = ⊤) :
    d = Module.finrank Z O * Fintype.card ι := by
  have e1 : Module.finrank Z T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have e2 : Module.finrank R (R ⊗[O] T) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk h1 h2.ge)
  rw [← e1, ← e2, Module.finrank_baseChange, Module.finrank_mul_finrank]

theorem nontrivial_tensor_of_free {Z O S : Type} [CommRing Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing S] [Nontrivial S] [Algebra Z S] :
    Nontrivial (O ⊗[Z] S) := by
  haveI : Module.FaithfullyFlat Z O := inferInstance
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem rank_count : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  intro l _ K LL T d M A ι _ v hM h1 h2
  haveI := freeOL LL
  haveI := finiteOL LL
  letI := zlMod LL T
  obtain ⟨b, -, -⟩ := hM
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : Nontrivial (RW LL) := nontrivial_tensor_of_free
  have h := card_eq_finrank_mul_card (R := RW LL) b v h1 h2
  refine ⟨Module.finrank ℤ_[l] ↥(OL LL), Module.finBasis _ _, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simpa using h

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
section
noncomputable section

namespace GlobalTheory.MirAvg

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

def mirSet {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) : Prop :=
  if b then ∀ x : Fin r → ZMod g, ∃ c : ZMod g, (h : Mt g r).mulVec x - x = c • a
  else ∀ x : Fin r → ZMod g, a ⬝ᵥ x = 0 → (h : Mt g r).mulVec x = x


open Classical in
def mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) : MonoidAlgebra ℂ (Gn g r) :=
  ∑ h : Gn g r, MonoidAlgebra.single h (if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0)

def SeriesKillsAvg : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (r : ℕ) (f : (ZMod g)[X]) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c → ¬ f.IsRoot c → ¬ f.IsRoot c⁻¹ → ∀ (a : Fin r → ZMod g) (b : Bool), a ≠ 0 →
      eSerC L r f * mirEl θ a b = 0

end GlobalTheory.MirAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAddStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repr_smul_add : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (c : k) (z z' : G → Fin A.m → k) (b g b' g' : ZMod n → Vc k A.m), Repr F A z b g → Repr F A z' b' g' → Repr F A (c • z + z') (c • b + b') (c • g + g') := by
  first | exact @GlobalTheory.TopSteps.Repr.smul_add | exact GlobalTheory.TopSteps.Repr.smul_add | (intros; apply GlobalTheory.TopSteps.Repr.smul_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  first | exact @GlobalTheory.MemLoc.σF_root_of_unity | exact GlobalTheory.MemLoc.σF_root_of_unity | (intros; apply GlobalTheory.MemLoc.σF_root_of_unity <;> assumption)
end

