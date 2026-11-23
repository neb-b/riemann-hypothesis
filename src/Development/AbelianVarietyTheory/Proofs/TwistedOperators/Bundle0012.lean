module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotLocallyFiniteQuadraticMulAddDegreeNonraising
section
namespace GlobalTheory.Chain.RealIt

open MvPolynomial

theorem totalDegree_mulLeft_add {σ : Type} (Q : MvPolynomial σ ℂ)
    (L : Module.End ℂ (MvPolynomial σ ℂ)) (hQ : Q ≠ 0) (hh : Q.IsHomogeneous 2)
    (hL : ∀ P, (L P).totalDegree ≤ P.totalDegree) (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) :
    ((LinearMap.mulLeft ℂ Q + L) φ).totalDegree = φ.totalDegree + 2 := by
  have h1 : (Q * φ).totalDegree = φ.totalDegree + 2 := by
    rw [totalDegree_mul_of_isDomain hQ hφ, hh.totalDegree hQ, add_comm]
  have h2 : (L φ).totalDegree < (Q * φ).totalDegree := by
    have := hL φ
    omega
  rw [LinearMap.add_apply, LinearMap.mulLeft_apply, totalDegree_add_eq_left_of_totalDegree_lt h2, h1]

theorem exists_totalDegree_le_of_finiteDimensional {σ : Type} (F : Submodule ℂ (MvPolynomial σ ℂ))
    (hF : FiniteDimensional ℂ F) : ∃ N : ℕ, ∀ P ∈ F, P.totalDegree ≤ N := by
  obtain ⟨s, hs⟩ : F.FG := (Submodule.fg_iff_finiteDimensional F).2 hF
  refine ⟨s.sup totalDegree, fun P hP => ?_⟩
  have hle : F ≤ restrictTotalDegree σ ℂ (s.sup totalDegree) := by
    rw [← hs, Submodule.span_le]
    intro x hx
    exact (mem_restrictTotalDegree σ _ x).2 (Finset.le_sup (f := totalDegree) hx)
  exact (mem_restrictTotalDegree σ _ P).1 (hle hP)

theorem not_locallyFinite_mulLeft_add :
    ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)),
      Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) →
      ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ),
        FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  intro σ _ Q L hQ hh hL φ hφ F hF hall
  obtain ⟨N, hN⟩ := exists_totalDegree_le_of_finiteDimensional F hF
  have key : ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ≠ 0 ∧
      (((LinearMap.mulLeft ℂ Q + L) ^ n) φ).totalDegree = φ.totalDegree + 2 * n := by
    intro n
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      have h := totalDegree_mulLeft_add Q L hQ hh hL _ ih.1
      rw [pow_succ', Module.End.mul_apply]
      refine ⟨fun h0 => ?_, by rw [h, ih.2]; ring⟩
      rw [h0, totalDegree_zero] at h
      omega
  have h1 := hN _ (hall (N + 1))
  rw [(key (N + 1)).2] at h1
  omega

end GlobalTheory.Chain.RealIt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
section
open MeasureTheory

namespace GlobalTheory.UnfoldNormal

def pairGroup {H : Type} [Group H] (Γ N : Subgroup H) (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) :
    Subgroup (H × H) where
  carrier := {p | p.1 ∈ Γ ∧ p.2 ∈ Γ ∧ p.1 * p.2⁻¹ ∈ N}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hb, hab⟩ ⟨hc, hd, hcd⟩
    refine ⟨Γ.mul_mem ha hc, Γ.mul_mem hb hd, ?_⟩
    have e : a * c * (b * d)⁻¹ = (a * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [e]
    exact N.mul_mem hab (hN b hb _ hcd)
  one_mem' := ⟨Γ.one_mem, Γ.one_mem, by simp [N.one_mem]⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    refine ⟨Γ.inv_mem ha, Γ.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹⁻¹ = a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    simp only [Prod.fst_inv, Prod.snd_inv]
    rw [e]
    exact hN _ (Γ.inv_mem ha) _ (N.inv_mem hab)

def shear {H : Type} [Group H] (N : Subgroup H) (p : N × H) : H × H := ((p.1 : H) * p.2, p.2)

end GlobalTheory.UnfoldNormal

namespace GlobalTheory.UnfoldNormal

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

def shearEquiv : H × H ≃ᵐ H × H where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.mul measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.mul measurable_snd.inv).prodMk measurable_snd

theorem shear_eq (N : Subgroup H) : shear N = shearEquiv ∘ Prod.map Subtype.val id := rfl

theorem measurableEmbedding_shear {N : Subgroup H} (hN : IsClosed (N : Set H)) :
    MeasurableEmbedding (shear N) := by
  rw [shear_eq]
  exact shearEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hN.measurableSet).prodMap MeasurableEmbedding.id)

theorem nullMeasurableSet_shear_image {N : Subgroup H} (hN : IsClosed (N : Set H)) (κ : Measure N)
    (ν : Measure H) {A : Set N} {B : Set H} (hA : NullMeasurableSet A κ) (hB : NullMeasurableSet B ν) :
    NullMeasurableSet (shear N '' (A ×ˢ B)) ((κ.prod ν).map (shear N)) := by
  have he := measurableEmbedding_shear hN
  have hAB : NullMeasurableSet (A ×ˢ B) (κ.prod ν) := hA.prod hB
  refine (he.measurableSet_image.2 (measurableSet_toMeasurable (κ.prod ν) (A ×ˢ B))).nullMeasurableSet.congr ?_
  refine (he.ae_map_iff (p := fun y => (y ∈ shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) ↔
    (y ∈ shear N '' (A ×ˢ B)))).2 ?_
  filter_upwards [hAB.toMeasurable_ae_eq] with x hx
  have e1 : shear N x ∈ shear N '' toMeasurable (κ.prod ν) (A ×ˢ B) ↔ x ∈ toMeasurable (κ.prod ν) (A ×ˢ B) :=
    he.injective.mem_set_image
  have e2 : shear N x ∈ shear N '' (A ×ˢ B) ↔ x ∈ (A ×ˢ B) := he.injective.mem_set_image
  rw [e1, e2]
  exact hx

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial
section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace GlobalTheory

theorem posDef_conjTranspose_mul_self_eq_exp_polynomial :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g →
      ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
        Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  intro n g hg
  set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh
  have hpd : h.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)
  have hsp : IsStrictlyPositive h := hpd.isStrictlyPositive
  have hsa : IsSelfAdjoint h := hpd.isHermitian
  have hfin : (spectrum ℝ h).Finite := Matrix.finite_real_spectrum
  classical
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x := by
    intro x hx
    have hxs : x ∈ s := hfin.mem_toFinset.mpr hx
    exact Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs
  refine ⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩
  · have : IsSelfAdjoint (CFC.log h) := by
      unfold CFC.log; exact cfc_predicate _ _
    exact this
  · rw [Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]
    unfold CFC.log
    exact cfc_congr (fun x hx => (hq x hx).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowSubCreationVacuumFockBound
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem annihilation_pow_vacuum {T : Type} [AddCommGroup T] [Module ℂ T]
    (a c : Module.End ℂ T) (s : ℝ) (v : T)
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0) (k : ℕ) :
    a (((c - a) ^ (k + 1)) v) = (((k : ℂ) + 1) * (s : ℂ)) • ((c - a) ^ k) v := by
  have hc : ∀ w, a (c w) = c (a w) + (s : ℂ) • w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ T => f w) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [← h]; abel
  have hD : ∀ w, a ((c - a) w) = (c - a) (a w) + (s : ℂ) • w := by
    intro w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hc]; abel

  have key : ∀ (k : ℕ) (w : T), a (((c - a) ^ (k + 1)) w) =
      ((c - a) ^ (k + 1)) (a w) + (((k : ℂ) + 1) * (s : ℂ)) • ((c - a) ^ k) w := by
    intro k
    induction k with
    | zero =>
      intro w
      simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, Module.End.one_apply, one_mul]
      exact hD w
    | succ k ih =>
      intro w
      have e1 : ((c - a) ^ (k + 1 + 1)) w = ((c - a) ^ (k + 1)) ((c - a) w) := by
        rw [pow_succ, Module.End.mul_apply]
      have e2 : ((c - a) ^ (k + 1)) w = ((c - a) ^ k) ((c - a) w) := by
        rw [pow_succ, Module.End.mul_apply]
      have e3 : ((c - a) ^ (k + 1 + 1)) (a w) = ((c - a) ^ (k + 1)) ((c - a) (a w)) := by
        rw [pow_succ, Module.End.mul_apply]
      have e4 : (s : ℂ) + ((k : ℂ) + 1) * (s : ℂ) = (((k + 1 : ℕ) : ℂ) + 1) * (s : ℂ) := by
        push_cast; ring
      rw [e1, ih, e3, hD, map_add (f := _), map_smul, ← e2, add_assoc, ← add_smul, e4]
  have := key k v
  rw [hv, map_zero, zero_add] at this
  exact this

theorem pow_vacuum_mem {T : Type} [AddCommGroup T] [Module ℂ T]
    (a c : Module.End ℂ T) (s : ℝ) (v : T)
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0)
    (K : Submodule ℂ T) (hvK : v ∈ K) (hcK : ∀ x ∈ K, c x ∈ K) (k : ℕ) :
    ((c - a) ^ k) v ∈ K ∧ ((c - a) ^ (k + 1)) v ∈ K := by
  induction k with
  | zero =>
    refine ⟨by simpa using hvK, ?_⟩
    simpa [hv] using hcK v hvK
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      annihilation_pow_vacuum a c s v hcomm hv k]
    exact K.sub_mem (hcK _ h2) (K.smul_mem _ h1)

theorem pow_vacuum_fock_bound (T H : Type) [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H)
    (a c : Module.End ℂ T) (s : ℝ) (v : T) (hs : 0 ≤ s)
    (hadj : ∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y)))
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0) :
    (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧
      ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  have hc : ∀ w, a (c w) = c (a w) + (s : ℂ) • w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ T => f w) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [← h]; abel
  refine ⟨fun K hvK hcK k => (pow_vacuum_mem a c s v hcomm hv K hvK hcK k).1, ?_⟩
  have hcn : ∀ y, ‖Φ (c y)‖ ^ 2 = ‖Φ (a y)‖ ^ 2 + s * ‖Φ y‖ ^ 2 := by
    intro y
    have e : inner ℂ (Φ (c y)) (Φ (c y)) =
        inner ℂ (Φ (a y)) (Φ (a y)) + (s : ℂ) * inner ℂ (Φ y) (Φ y) := by
      rw [hadj, hc, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
      congr 1
      rw [← inner_conj_symm (Φ y) (Φ (c (a y))), hadj]
      exact inner_conj_symm _ _
    simp only [inner_self_eq_norm_sq_to_K] at e
    apply Complex.ofReal_injective
    push_cast
    linear_combination e
  have hDn : ∀ y, ‖Φ ((c - a) y)‖ ^ 2 ≤ 2 * ‖Φ (c y)‖ ^ 2 + 2 * ‖Φ (a y)‖ ^ 2 := by
    intro y
    rw [LinearMap.sub_apply, map_sub]
    have h := norm_sub_le (Φ (c y)) (Φ (a y))
    have h2 : ‖Φ (c y) - Φ (a y)‖ ^ 2 ≤ (‖Φ (c y)‖ + ‖Φ (a y)‖) ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖Φ (c y)‖ - ‖Φ (a y)‖)]
  have hsm : ∀ k : ℕ, ‖Φ (a (((c - a) ^ (k + 1)) v))‖ =
      ((k : ℝ) + 1) * s * ‖Φ (((c - a) ^ k) v)‖ := by
    intro k
    rw [annihilation_pow_vacuum a c s v hcomm hv k, map_smul, norm_smul]
    congr 1
    have e : ((k : ℂ) + 1) * (s : ℂ) = ((((k : ℝ) + 1) * s : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) hs)]

  have main : ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial ∧
      ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 ≤
        ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      have h := hcn v
      rw [hv, map_zero, norm_zero] at h
      simp only [zero_add, pow_one, LinearMap.sub_apply, hv, sub_zero, Nat.factorial_one,
        Nat.cast_one, mul_one]
      rw [h]
      nlinarith [mul_nonneg hs (sq_nonneg ‖Φ v‖)]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      rw [pow_succ' (c - a) (k + 1), Module.End.mul_apply]
      have hA := mul_le_mul_of_nonneg_left h1
        (show (0 : ℝ) ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 by positivity)
      have hB := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 * s by linarith)
      calc ‖Φ ((c - a) (((c - a) ^ (k + 1)) v))‖ ^ 2
          ≤ 2 * ‖Φ (c (((c - a) ^ (k + 1)) v))‖ ^ 2
              + 2 * ‖Φ (a (((c - a) ^ (k + 1)) v))‖ ^ 2 := hDn _
        _ = 4 * (((k : ℝ) + 1) * s) ^ 2 * ‖Φ (((c - a) ^ k) v)‖ ^ 2
              + 2 * s * ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 := by
          rw [hcn, hsm]; ring
        _ ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 * (‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial)
              + 2 * s * (‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial) := add_le_add hA hB
        _ = ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1 + 1) * (k + 1 + 1).factorial := by
          rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]; push_cast; ring
  exact fun k => (main k).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
section
namespace GlobalTheory


open Finset in
theorem prod_eq_sum_of_factorwise_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  intro K _ X I S x a b A B h1 h2 h3 hne
  classical
  have key : ∀ T : Finset K, ∀ q : ∀ n, X n,
      ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) =
        ∏ n, (if n ∈ T then B n else A n (q n)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro q; simpa using (h3 q).symm
    | insert m T hm ih =>
      intro q
      obtain ⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n)) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m,
          (if n ∈ T then b n i else a n i (q n)) := ⟨_, rfl⟩
      have hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c := by
        intro t
        have h := ih (Function.update q m t)
        have e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) =
            a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
          intro i
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        have e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c := by
          rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        rw [e2] at h
        simp only [e1] at h
        rw [← h, hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) =
          b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
        intro i
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      have e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c := by
        rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      rw [e4]
      simp only [e3]
      have hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) =
          ∑ i ∈ S, y i * b m i := by
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      by_cases hc0 : c = 0
      · rw [hc0, mul_zero]
        apply h1 m y
        intro t
        rw [hL t, hc0, mul_zero]
      · have hB := h2 m (fun i => y i / c) (by
          intro t
          have : ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [this, hL t, mul_div_cancel_right₀ _ hc0])
        rw [hB, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  obtain ⟨q⟩ : Nonempty (∀ n, X n) := ⟨fun n => Classical.choice (hne n)⟩
  simpa using (key Finset.univ q).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdMapMulSingleApply
section
universe u_1 u_2

namespace GlobalTheory.ProdMapMulSingle

theorem prod_map_mulSingle_apply {ι : Type u_1} [DecidableEq ι] {M : ι → Type u_2}
    [(i : ι) → Monoid (M i)] (x : (i : ι) → M i) (l : List ι) (hl : List.Nodup l) (w : ι) :
    List.prod (List.map (fun (i : ι) ↦ Pi.mulSingle i (x i)) l) w
      = if w ∈ l then x w else (1 : M w) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl']
    by_cases h : w = a
    · subst h
      rw [if_neg ha, if_pos List.mem_cons_self, Pi.mulSingle_eq_same, mul_one]
    · rw [Pi.mulSingle_eq_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

end GlobalTheory.ProdMapMulSingle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSubProdLe
section
namespace GlobalTheory.ProdSubProdBound

theorem prod_sub_prod_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}
    (ha : ∀ i, v (a i) ≤ 1) (hb : ∀ i, v (b i) ≤ 1) (hab : ∀ i, v (a i - b i) ≤ c) :
    v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have hB : v (∏ i ∈ s, b i) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' (fun i _ => hb i)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · rw [v.map_mul]
      calc v (a j) * v (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ 1 * c := mul_le_mul' (ha j) ih
        _ = c := one_mul c
    · rw [v.map_mul]
      calc v (a j - b j) * v (∏ i ∈ s, b i) ≤ c * 1 := mul_le_mul' (hab j) hB
        _ = c := mul_one c

theorem main : ∀ {K Γ : Type} [inst : Field K] [inst_1 : LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}, (∀ (i : ι), (v : K → Γ) (a i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (b i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (a i - b i) ≤ c) → (v : K → Γ) (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c :=
  fun s => prod_sub_prod_le s

end GlobalTheory.ProdSubProdBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumFourSwap
section
namespace GlobalTheory.SumFourSwap

theorem sum_four_swap {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : α, ∑ c : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.SumFourSwap
end

