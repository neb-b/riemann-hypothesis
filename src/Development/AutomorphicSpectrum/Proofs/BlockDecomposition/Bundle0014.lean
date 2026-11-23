module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowSmulEqZero
section
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TensorComplete

section Elementary

variable {A : Type} [CommRing A] (π : A)

theorem smodEq_span_iff {M : Type} [AddCommGroup M] [Module A M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem isAdicComplete_span_iff {M : Type} [AddCommGroup M] [Module A M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_span_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule A M)] := by
        intro m n hmn
        rw [smodEq_span_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_span_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_span_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

variable {π}

theorem isAdicComplete_of_linearEquiv {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have : e.symm x = 0 := h1 _ fun n => by
      obtain ⟨z, hz⟩ := hx n
      exact ⟨e.symm z, by rw [← map_smul, hz]⟩
    simpa using this
  · obtain ⟨L, hL⟩ := h2 (fun n => e.symm (u n)) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩
    refine ⟨e L, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    exact ⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩

theorem isAdicComplete_prod {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : IsAdicComplete (Ideal.span {π}) M)
    (h' : IsAdicComplete (Ideal.span {π}) M') : IsAdicComplete (Ideal.span {π}) (M × M') := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  obtain ⟨h1', h2'⟩ := (isAdicComplete_span_iff π).1 h'
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · refine Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.1, by rw [← hz]; rfl⟩
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.2, by rw [← hz]; rfl⟩
  · obtain ⟨L, hL⟩ := h2 (fun n => (u n).1) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.1, by simpa using congrArg Prod.fst hz⟩
    obtain ⟨L', hL'⟩ := h2' (fun n => (u n).2) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.2, by simpa using congrArg Prod.snd hz⟩
    refine ⟨(L, L'), fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    obtain ⟨z', hz'⟩ := hL' n
    exact ⟨(z, z'), Prod.ext hz hz'⟩

theorem isAdicComplete_fin_pi {M : Type} [AddCommGroup M] [Module A M]
    (h : IsAdicComplete (Ideal.span {π}) M) (n : ℕ) :
    IsAdicComplete (Ideal.span {π}) (Fin n → M) := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · funext i
    refine h1 _ fun k => ?_
    obtain ⟨z, hz⟩ := hx k
    exact ⟨z i, by rw [← hz]; rfl⟩
  · choose z hz using hu
    have key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L := fun i =>
      h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩
    choose L hL using key
    refine ⟨L, fun k => ?_⟩
    choose w hw using fun i => hL i k
    exact ⟨w, funext hw⟩

theorem isAdicComplete_of_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module A M] (E : ℕ)
    (h : ∀ x : M, π ^ E • x = 0) : IsAdicComplete (Ideal.span {π}) M := by
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · obtain ⟨z, rfl⟩ := hx E
    exact h z
  · have tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k) := by
      intro n k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨w, hw⟩ := hu (n + k)
        refine ⟨z + π ^ k • w, ?_⟩
        rw [smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]
        abel
    refine ⟨u E, fun n => ?_⟩
    obtain ⟨z, hz⟩ := tel n E
    obtain ⟨w, hw⟩ := tel E n
    rw [h w, add_comm E n] at hw
    refine ⟨z, ?_⟩
    rw [hz, ← sub_eq_zero.1 hw.symm]

end Elementary

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

theorem irreducible_dvd_of_not_isUnit {q r : R} (hq : Irreducible q) (hr : ¬IsUnit r) : q ∣ r := by
  have hmax : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq
  have heq : Ideal.span {q} = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← Ideal.mem_span_singleton, heq]
  exact (IsLocalRing.mem_maximalIdeal r).2 hr

theorem exists_pow_smul_directSum_eq_zero {ι : Type} [Fintype ι] (q : ι → R)
    (hq : ∀ i, Irreducible (q i)) (e : ι → ℕ) {r : R} (hr : ¬IsUnit r) :
    ∃ E : ℕ, ∀ x : DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}), r ^ E • x = 0 := by
  classical
  refine ⟨∑ i, e i, fun x => ?_⟩
  refine DFinsupp.ext fun i => ?_
  have hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i} := by
    rw [Submodule.mem_span_singleton]
    have h1 : q i ^ e i ∣ r ^ (∑ i, e i) :=
      (pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans
        (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
  change r ^ (∑ i, e i) • x i = 0
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem _ y hmem

theorem pow_natCast_smul_tensor_eq_zero {O T : Type} [CommRing O] [Algebra R O] [AddCommGroup T]
    [Module R T] (p E : ℕ) (h : ∀ x : T, (p : R) ^ E • x = 0) (t : O ⊗[R] T) :
    (p : O) ^ E • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o x =>
    have h1 : (p : O) ^ E * o = (p : R) ^ E • o := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

end Tensor

theorem isAdicComplete_tensor : ∀ (p : ℕ) [Fact p.Prime] (R O : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [CommRing O] [Algebra R O]
    [IsAdicComplete (Ideal.span {(p : O)}) O],
    (p : R) ≠ 0 → ¬IsUnit (p : R) →
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] N) := by
  intro p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := N)
  obtain ⟨E, hE⟩ := exists_pow_smul_directSum_eq_zero q hq e hp2
  have hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R)) :=
    isAdicComplete_of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans
        (TensorProduct.finsuppScalarRight R O O (Fin n)).symm)
      (isAdicComplete_fin_pi inferInstance n)
  have htors : IsAdicComplete (Ideal.span {(p : O)})
      (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i})) :=
    isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)
  exact isAdicComplete_of_linearEquiv
    ((TensorProduct.prodRight R O O _ _).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm)
    (isAdicComplete_prod hfree htors)

end GlobalTheory.CompanionTheory.TensorComplete
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization
section
namespace GlobalTheory.CompanionTheory.IntClosedAway

open Polynomial

theorem mem_span_of_eq_mul_integral {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (t a : A) (hred : IsReduced (A ⧸ Ideal.span {t})) (z : K)
    (hz : IsIntegral A z) (h : algebraMap A K a = algebraMap A K t * z) :
    a ∈ Ideal.span {t} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hinj := IsFractionRing.injective A K
  have h1 : (p.scaleRoots t).eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]
  have h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree := by
    have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    ext i
    rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, zero_pow (by omega), mul_zero]
    · subst hi
      simp [hp.coeff_natDegree]
    · rw [if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  have h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0 := by
    have h4 := congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2] at h4
    simpa using h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)

theorem isIntegrallyClosed_of_away :
    ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) →
      IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  intro A _ _ t ht hred hcl
  have hle : Submonoid.powers t ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  let K := FractionRing A
  letI : Algebra (Localization.Away t) K :=
    (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K)
      (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra
  haveI : IsScalarTower A (Localization.Away t) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  haveI : IsFractionRing (Localization.Away t) K :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hxB : IsIntegral (Localization.Away t) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj t y
  have hxa : algebraMap A K a = x * algebraMap A K t ^ n := by
    have h5 := congrArg (algebraMap (Localization.Away t) K) hna
    rw [map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K,
      ← IsScalarTower.algebraMap_apply A (Localization.Away t) K] at h5
    exact h5.symm
  have ht' : algebraMap A K t ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht
  clear hna
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using hxa⟩
  | succ n ih =>
    have hz : IsIntegral A (x * algebraMap A K t ^ n) := hx.mul (isIntegral_algebraMap.pow n)
    have hmem : a ∈ Ideal.span {t} :=
      mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih b (mul_left_injective₀ ht' ?_)
    simp only [map_mul] at hxa
    simp only [hxa]
    ring

end GlobalTheory.CompanionTheory.IntClosedAway
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
section
open Matrix Filter Topology ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalFieldChar

theorem circle_eq_one_of_forall_re_pow_pos (z : Circle)
    (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  have hsq : ∀ w : Circle, (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
    intro w
    have := Circle.normSq_coe w
    rw [Complex.normSq_apply] at this
    nlinarith
  by_contra hz
  have ha0 : (z : ℂ).re < 1 := by
    by_contra hge
    push_neg at hge
    have h2 := hsq z
    have him : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re - 1)]
    have hre : (z : ℂ).re = 1 := by
      rw [him] at h2
      nlinarith
    exact hz (Circle.ext (Complex.ext (by simpa using hre) (by simpa using him)))
  set a : ℕ → ℝ := fun j => ((z ^ (2 ^ j) : Circle) : ℂ).re with ha
  have hstep : ∀ j, a (j + 1) = 2 * a j ^ 2 - 1 := by
    intro j
    have h2 := hsq (z ^ (2 ^ j))
    have hp : z ^ (2 ^ (j + 1)) = z ^ (2 ^ j) * z ^ (2 ^ j) := by
      rw [pow_succ, pow_mul, sq]
    simp only [ha]
    rw [hp, Circle.coe_mul, Complex.mul_re]
    nlinarith
  have hlow : ∀ j, (2 : ℝ) ^ j * (1 - (z : ℂ).re) ≤ 1 - a j := by
    intro j
    induction j with
    | zero => simp [ha]
    | succ j ih =>
      have hpos : 0 < a j := h _
      have hle : a j ≤ 1 := by
        have := hsq (z ^ (2 ^ j))
        have h3 : a j ^ 2 ≤ 1 := by
          simp only [ha]
          nlinarith [sq_nonneg ((z ^ (2 ^ j) : Circle) : ℂ).im]
        nlinarith
      rw [hstep, pow_succ]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
  have hd : 0 < 1 - (z : ℂ).re := by linarith
  rw [div_lt_iff₀ hd] at hj
  have := hlow j
  have hpos : 0 < a j := h _
  linarith

theorem isOpen_addChar_ker : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by
  intro k _ _ _ _ ψ hψ
  let H : AddSubgroup k :=
    { carrier := {x | ψ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  have hV : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_induced_dom)
  have hU : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) :=
    (hV.preimage hψ).mem_nhds (by simp)
  obtain ⟨γ, hγ, hball⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hU
  have hsmul : ∀ x : k, valuation k x < γ → ∀ n : ℕ, valuation k (n • x) < γ := by
    intro x hx n
    induction n with
    | zero => simpa using zero_lt_iff.2 hγ
    | succ n ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_lt _ ih hx
  have hone : ∀ x : k, valuation k x < γ → x ∈ H := by
    intro x hx
    refine circle_eq_one_of_forall_re_pow_pos (ψ x) fun n => ?_
    have h1 : 0 < ((ψ (n • x) : Circle) : ℂ).re := hball (hsmul x hx n)
    rwa [AddChar.map_nsmul_eq_pow] at h1
  have hnh : (H : Set k) ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨γ, hγ, fun x hx => hone x hx⟩
  exact H.isOpen_of_mem_nhds hnh

end GlobalTheory.CompanionTheory.LocalFieldChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedFDerivSubApply
section
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter

namespace GlobalTheory.CompanionTheory.SchwartzBaire

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_sub_apply' (f g : 𝓢(E, F)) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (⇑(f - g)) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x := by
  have h : (⇑(f - g) : E → F) = ⇑f - ⇑g := by
    ext x
    simp
  rw [h]
  exact iteratedFDeriv_sub_apply (f.smooth l).contDiffAt (g.smooth l).contDiffAt

theorem cauchy_weighted (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖ ≤ ε := by
  have h0 := hf.tendsto_uniformity
  rw [uniformity_eq_comap_nhds_zero 𝓢(E, F), tendsto_comap_iff] at h0
  have h1 := ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ 0).1 h0 (k, l) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h1
  refine ⟨max N₁ N₂, fun m hm m' hm' x => ?_⟩
  have hmm := hN (m', m) ⟨le_trans (le_max_left _ _) hm', le_trans (le_max_right _ _) hm⟩
  simp only [Function.comp_apply, Prod.map_apply, sub_zero] at hmm
  rw [← iteratedFDeriv_sub_apply']
  exact (SchwartzMap.le_seminorm ℝ k l (f m - f m') x).trans hmm.le

theorem exists_tendsto [CompleteSpace F] (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) :
    ∃ g : 𝓢(E, F), Tendsto f atTop (𝓝 g) := by
  have hpt : ∀ l x, CauchySeq (fun n => iteratedFDeriv ℝ l (f n) x) := by
    intro l x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_weighted f hf 0 l (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn N le_rfl x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm]
    linarith
  choose G hG using fun l x => cauchySeq_tendsto_of_complete (hpt l x)
  have hlim : ∀ k l {δ : ℝ}, 0 < δ → ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖ ≤ δ := by
    intro k l δ hδ
    obtain ⟨N, hN⟩ := cauchy_weighted f hf k l hδ
    refine ⟨N, fun m hm x => ?_⟩
    have ht : Tendsto (fun m' => ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖)) :=
      ((tendsto_const_nhds.sub (hG l x)).norm).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m' hm' => hN m hm m' hm' x⟩)
  have hunif : ∀ l, TendstoUniformly (fun n x => iteratedFDeriv ℝ l (f n) x) (G l) atTop := by
    intro l
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlim 0 l (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h := hN n hn x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  let g₀ : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x l => G l x
  have hT : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) g₀ p := by
    refine ⟨fun x => rfl, fun m _ x => ?_, fun m _ => ?_⟩
    · have hU : TendstoUniformly (fun n y => (iteratedFDeriv ℝ (m + 1) (f n) y).curryLeft)
          (fun y => (G (m + 1) y).curryLeft) atTop :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hunif (m + 1))
      exact hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ m (f n) y) hU
        (fun n y => ((f n).smooth ⊤).ftaylorSeries.fderiv m (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)) y)
        (fun y => hG m y) x
    · exact (hunif m).continuous (Frequently.of_forall fun n => ((f n).smooth m).continuous_iteratedFDeriv le_rfl)
  have hg : ∀ l x, iteratedFDeriv ℝ l g₀ x = G l x := fun l x =>
    (hT.eq_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) x).symm
  have hdecay : ∀ k l : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l g₀ x‖ ≤ C := by
    intro k l
    obtain ⟨N, hN⟩ := hlim k l one_pos
    refine ⟨1 + SchwartzMap.seminorm ℝ k l (f N), fun x => ?_⟩
    rw [hg]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k l (f N) x
    have h3 : ‖G l x‖ ≤ ‖iteratedFDeriv ℝ l (f N) x‖ + ‖iteratedFDeriv ℝ l (f N) x - G l x‖ := by
      calc ‖G l x‖ = ‖iteratedFDeriv ℝ l (f N) x - (iteratedFDeriv ℝ l (f N) x - G l x)‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hxk : 0 ≤ ‖x‖ ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hxk]
  let g : 𝓢(E, F) := ⟨g₀, hT.contDiff, hdecay⟩
  have hcoe : (⇑g : E → F) = g₀ := rfl
  refine ⟨g, ?_⟩
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds _ _]
  intro i ε hε
  obtain ⟨N, hN⟩ := hlim i.1 i.2 (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hb : SchwartzMap.seminorm ℝ i.1 i.2 (f m - g) ≤ ε / 2 :=
    SchwartzMap.seminorm_le_bound ℝ i.1 i.2 _ (by positivity) fun x => by
      rw [iteratedFDeriv_sub_apply', hcoe, hg]
      exact hN m hm x
  exact lt_of_le_of_lt hb (half_lt_self hε)

theorem completeSpace [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun f hf => exists_tendsto f hf

theorem baireSpace [CompleteSpace F] : BaireSpace 𝓢(E, F) := by
  have : CompleteSpace 𝓢(E, F) := completeSpace
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory.CompanionTheory.SchwartzBaire
end

