module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

section Alg

variable {I R D : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing D] [Algebra R D]


omit [DecidableEq I] in
theorem mvAeval_add_of_mul_eq_zero (t n : I → D) (hn : ∀ i j, n i * n j = 0)
    (P : MvPolynomial I R) :
    MvPolynomial.aeval (fun i ↦ t i + n i) P =
      MvPolynomial.aeval t P + ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * n i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p j hp =>
    have h1 : (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * n j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hn, mul_zero]
    have h2 : ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
        (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * t j +
          MvPolynomial.aeval t p * n j := by
      have h3 : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
          MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i * t j +
            if j = i then MvPolynomial.aeval t p * n i else 0 := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add (f := _), map_mul, map_mul, MvPolynomial.aeval_X,
          MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
    rw [map_mul, map_mul, hp, h2, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    linear_combination h1

theorem aeval_truncTotal_succ (N : ℕ) (t : I → D) (F : MvPowerSeries I R) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) F) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  have h : MvPowerSeries.truncTotal (N + 1) F =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F) := by
    ext d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finset.sum_ite_eq,
      Finset.mem_range, Finsupp.degree_eq_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]


omit [Fintype I] [DecidableEq I] in
theorem ideal_pow_eq_bot_of_prod {J : Ideal D} {k : ℕ}
    (h : ∀ s : Fin k → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) : J ^ k = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  rw [List.prod_ofFn]
  exact h _ fun a => (f a).2


omit [DecidableEq I] in
theorem aeval_pderiv_truncTotal_mul {J : Ideal D} {N : ℕ} (hJ : J ^ (N + 1) = ⊥) {t : I → D}
    (ht : ∀ i, t i ∈ J) {x : D} (hx : x ∈ J) (F : MvPowerSeries I R) (i : I) :
    MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPowerSeries.truncTotal (N + 1) F)) * x =
      MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) (MvPowerSeries.pderiv (R := R) i F)) * x := by
  classical
  rw [← sub_eq_zero, ← sub_mul, ← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : N ≤ m.degree := by
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hm ?_
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_truncTotal _
      (by rw [map_add (f := _), Finsupp.degree_single]; omega), MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_pderiv, sub_self]
  have h1 : ∏ j, t j ^ m j ∈ J ^ N := by
    refine Ideal.pow_le_pow_right hdeg ?_
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (ht j) _
  have h2 : (∏ j, t j ^ m j) * x = 0 := by
    rw [← Ideal.mem_bot, ← hJ, pow_succ]
    exact Ideal.mul_mem_mul h1 hx
  rw [mul_assoc, h2, mul_zero]

end Alg

theorem taylor_add_of_mul_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  intro I _ _ D _ _ N t n hs hn f hf
  have key : ∀ (u : I → D) (g : (I → ℂ) → ℂ), AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N u g =
      MvPolynomial.aeval u (MvPowerSeries.truncTotal (N + 1) (GlobalTheory.taylor g)) := fun u g hg => by
    rw [aeval_truncTotal_succ, taylor_eq_sum_coeff_taylor N u g hg]
  rw [key _ _ hf, key _ _ hf, mvAeval_add_of_mul_eq_zero t n hn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key _ _ (GlobalTheory.analyticAt_fderiv_apply hf _), GlobalTheory.taylor_fderiv hf]
  exact aeval_pderiv_truncTotal_mul (ideal_pow_eq_bot_of_prod hs)
    (fun j => Ideal.subset_span (Or.inl ⟨j, rfl⟩)) (Ideal.subset_span (Or.inr ⟨i, rfl⟩)) _ i

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

section

variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]

theorem exists_prod_dvd_monomial (t : I → D) (k : ℕ) :
    ∀ m : I →₀ ℕ, k ≤ m.degree → ∃ s : Fin k → I, ∏ a, t (s a) ∣ ∏ i, t i ^ m i := by
  induction k with
  | zero => intro m _; exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro m hm
    have h : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    obtain ⟨s, hs⟩ := ih m' (by rw [map_add (f := _), Finsupp.degree_single] at hm; omega)
    refine ⟨Fin.cons i s, ?_⟩
    have h1 : ∏ j, t j ^ (Finsupp.single i 1 : I →₀ ℕ) j = t i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finsupp.add_apply, pow_add,
      Finset.prod_mul_distrib, h1]
    exact mul_dvd_mul_left _ hs

variable [Algebra ℂ D]

theorem aeval_eq_zero_of_coeff_eq_zero {N : ℕ} {t : I → D}
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (P : MvPolynomial I ℂ)
    (hP : ∀ m : I →₀ ℕ, m.degree < N + 1 → P.coeff m = 0) : MvPolynomial.aeval t P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have h : N + 1 ≤ m.degree := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hm (hP m (by omega))
  obtain ⟨s, hs⟩ := exists_prod_dvd_monomial t (N + 1) m h
  rw [ht, zero_dvd_iff] at hs
  rw [hs, mul_zero]


omit [Algebra ℂ D] [CommRing D] in
theorem coeff_sum_monomial_finsuppAntidiag (N : ℕ) (F : MvPowerSeries I ℂ) (n : I →₀ ℕ)
    (hn : n.degree < N + 1) :
    AddMonoidAlgebra.coeff (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) n = MvPowerSeries.coeff n F := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← Finsupp.degree_eq_sum, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hn)]

theorem aeval_sum_monomial_finsuppAntidiag (N : ℕ) (t : I → D) (F : MvPowerSeries I ℂ) :
    MvPolynomial.aeval t (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (t i))]

end

theorem taylor_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) =
        GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  intro I _ _ D _ _ N t ht f g hf hg
  change GlobalTheory.PeriodFamily.taylor N t (f * g) = _
  rw [GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ (hf.mul hg), GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hf, GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hg,
    GlobalTheory.taylor_mul hf hg, ← aeval_sum_monomial_finsuppAntidiag,
    ← aeval_sum_monomial_finsuppAntidiag, ← aeval_sum_monomial_finsuppAntidiag, ← map_mul,
    ← sub_eq_zero, ← map_sub]
  refine aeval_eq_zero_of_coeff_eq_zero ht _ fun m hm => ?_
  rw [MvPolynomial.coeff_sub, coeff_sum_monomial_finsuppAntidiag _ _ _ hm, MvPolynomial.coeff_mul,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, map_add (f := _)] at hm
  rw [coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega),
    coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMap
section
open TopologicalSpace TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

section General

variable {R H : Type} [CommRing R] [Algebra ℂ R] [CommRing H] [Algebra ℂ H]

def redCoef (π : R →ₐ[ℂ] ℂ) : R ⊗[ℂ] H →ₐ[ℂ] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ H).comp π) (AlgHom.id ℂ H) (fun _ _ ↦ Commute.all _ _)

theorem redCoef_tmul (π : R →ₐ[ℂ] ℂ) (d : R) (y : H) :
    redCoef π (d ⊗ₜ[ℂ] y) = algebraMap ℂ H (π d) * y := by
  simp [redCoef, Algebra.TensorProduct.lift_tmul]

theorem sub_redCoef_mem (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] H) :
    x - 1 ⊗ₜ[ℂ] redCoef π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d y =>
    rw [redCoef_tmul]
    have e : d ⊗ₜ[ℂ] y - (1 : R) ⊗ₜ[ℂ] (algebraMap ℂ H (π d) * y) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) (d - algebraMap ℂ R (π d)) * ((1 : R) ⊗ₜ[ℂ] y) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  | add x y hx hy =>
    have e : x + y - 1 ⊗ₜ[ℂ] redCoef π (x + y) = (x - 1 ⊗ₜ[ℂ] redCoef π x) + (y - 1 ⊗ₜ[ℂ] redCoef π y) := by
      rw [map_add (f := _), TensorProduct.tmul_add]; abel
    rw [e]; exact Ideal.add_mem _ hx hy

end General

theorem fn_redCoef {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {R : Type} [CommRing R]
    [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] Hol W) {p : E} (hp : p ∈ W) :
    (redCoef π x).fn p = π (evT R p hp x) := by
  rw [← Hol.ev_apply p hp]
  change ((Hol.ev p hp).comp (redCoef π)) x = (π.comp (evT R p hp)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun d y ↦ ?_
  simp only [AlgHom.comp_apply, redCoef_tmul, evT, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.commutes,
    AlgHom.id_apply, Algebra.ofId_apply]
  simp

theorem taylor_red {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ)
    (t : I → R) (π : R →ₐ[ℂ] ℂ) (ht : ∀ i, π (t i) = 0) (f : (I → ℂ) → ℂ) :
    π (GlobalTheory.PeriodFamily.taylor N t f) = f 0 := by
  have h := GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t f
  have hle : Ideal.span (Set.range t) ≤ RingHom.ker π := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  have := hle h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  simpa using this

theorem taylor_reduces_to_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  intro I _ _ g R _ _ N t π ht W W₀ _ ρ hρ h h₀ hh₀
  have hq : redCoef π (ρ h) = h₀ := Hol.ext_fn fun p hp ↦ by
    rw [fn_redCoef π _ hp, hρ h p hp, taylor_red N t π ht, hh₀ p hp]
  have := sub_redCoef_mem (H := Hol W₀) π (ρ h)
  rwa [hq] at this

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenContractTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.AnPer

open GlobalTheory.CatCoh

attribute [local instance] Charts.Obj.cAlg

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {D : Type} [CommRing D] [Algebra ℂ D]

def Charts.Obj.tenContract (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) : T.ten D →ₗ[ℂ] T.C :=
  (TensorProduct.lid ℂ T.C).toLinearMap ∘ₗ LinearMap.rTensor T.C ℓ

theorem Charts.Obj.tenContract_tmul (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) (d : D) (c : T.C) :
    T.tenContract ℓ (d ⊗ₜ c) = ℓ d • c := rfl

theorem Charts.Hom.tenContract_ten (ℓ : D →ₗ[ℂ] ℂ) {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.tenContract ℓ (Charts.Hom.ten D f x) = f.φ (T.tenContract ℓ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    rw [Charts.Hom.ten_tmul, Charts.Obj.tenContract_tmul, Charts.Obj.tenContract_tmul]
    exact (map_smul (Charts.Hom.φc f) (ℓ d) c).symm

theorem Charts.tenZ_eq_zero (K : Charts F) (hK : K.Rich) (hz : ∃ z, z ∈ F.V) {D : Type} [CommRing D] [Algebra ℂ D]
    (p : Λ →+ D) (h : H1.mk _ (K.tenZ p) = 0) : p = 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨G, hG⟩ := H1.mk_eq_zero.1 h
  refine AddMonoidHom.ext fun l ↦ (Module.forall_dual_apply_eq_zero_iff ℂ (p l)).1 fun ℓ ↦ ?_
  let q : Λ →+ Hol F.V := ((algebraMap ℂ (Hol F.V)).toAddMonoidHom.comp ℓ.toAddMonoidHom).comp p
  have h0 : K.perZ 0 = 0 := Subtype.ext (by
    funext T T' f
    exact map_zero (algebraMap (Hol F.V) T'.C))
  have hq : K.perCl q = K.perCl 0 := by
    unfold Charts.perCl
    rw [h0, map_zero]
    refine H1.mk_eq_zero.2 ⟨fun T ↦ T.tenContract ℓ (G T), ?_⟩
    funext T T' f
    have e : G T' - Charts.Hom.ten D f (G T) = (p f.deg ⊗ₜ[ℂ] (1 : T'.C) : T'.ten D) :=
      congrFun (congrFun (congrFun hG T) T') f
    have e' := congrArg (T'.tenContract ℓ) e
    rw [map_sub, Charts.Hom.tenContract_ten, Charts.Obj.tenContract_tmul, ← Algebra.algebraMap_eq_smul_one] at e'
    exact e'
  have h1 : algebraMap ℂ (Hol F.V) (ℓ (p l)) = 0 := DFunLike.congr_fun (GlobalTheory.T.periodClass_injective_of_rich_charts K hK q 0 hq) l
  have h2 := congrArg (Hol.ev z hz) h1
  rwa [AlgHom.commutes, map_zero] at h2

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenFib
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFib

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} (D : Type) [CommRing D]
  [Algebra ℂ D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀)

def inc (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) : CoefMap (algebraMap ℂ D) (O (dp0 ℂ) s₀) (K₀.Ten D) where
  G := r₀.functor
  α T := (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom
  naturality _ _ := rfl
  smul T a b := by
    subst hσ
    change ((1 : D) ⊗ₜ[ℂ] (a • (show T.C from b)) : T.ten D) = algebraMap ℂ D a • ((1 : D) ⊗ₜ[ℂ] (show T.C from b) : T.ten D)
    rw [tmul_smul, algebraMap_smul]

theorem ten_fib : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) (j₀ : ℂ →+* D₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' j₀ φ), (∀ a, io (j₀ a) = algebraMap ℂ D a) → ∀ (c : FirstDeRham s₀) (p : Λ → ℂ) (per : Λ →+ Hol F₀.V) (q : Λ →+ D), (∀ l, per l = algebraMap ℂ _ (p l)) → (∀ l, q l = algebraMap ℂ D (p l)) → r₀.coef.pull1 c = K₀.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (k.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ j₀ φ hφ k hj c p per q hper hq hc
  subst hφ
  let θ : (inc D r₀ hσ).G ⟶ (k.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom with
            commutes' := fun a ↦ by
              subst hσ
              change (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D) (algebraMap ℂ T.C a) =
                algebraMap D (T.ten D) (io (j₀ a))
              rw [AlgHom.commutes, hj, ← IsScalarTower.algebraMap_apply] }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun b ↦ congrArg (Ideal.Quotient.mk T.J) (by
            change (show T.C from b) = T.red π (1 ⊗ₜ (show T.C from b))
            rw [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul])
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat T.δ (T.tenδ π)
            (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom fun b hb ↦ by
              change T.red π (1 ⊗ₜ b) ∈ T.J
              rwa [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul]
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (r₀.obj T).x = (r₀.obj T).x ≫ 𝟙 X₀
            rw [Cris.spMap_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e := (inc D r₀ hσ).pullCohomologyOne_eq_of_natTrans _ θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp] at e
  refine e.symm.trans ?_
  obtain ⟨f, rfl⟩ := CatCoh.H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := CatCoh.H1.mk_eq_mk.1 hc
  refine CatCoh.H1.mk_eq_mk.2 ⟨fun T ↦ ((1 : D) ⊗ₜ[ℂ] (show T.C from G T) : T.ten D), ?_⟩
  funext T T' ψ
  have h1 := congrFun (congrFun (congrFun hG T) T') ψ
  have h2 : ((1 : D) ⊗ₜ[ℂ] ((show T'.C from G T') - ψ.φ (G T)) : T'.ten D) = (1 : D) ⊗ₜ[ℂ] (show T'.C from f.1 _ _ (r₀.functor.map ψ)) -
      (1 : D) ⊗ₜ[ℂ] (algebraMap (Hol F₀.V) T'.C (per ψ.deg)) := by
    rw [← tmul_sub]; exact congrArg _ h1
  refine (tmul_sub _ _ _).symm.trans (h2.trans ?_)
  congr 1
  change _ = algebraMap D (T'.ten D) (q ψ.deg)
  rw [hper, hq]
  exact (Algebra.TensorProduct.includeRight : T'.C →ₐ[ℂ] T'.ten D).commutes (p ψ.deg)

end GlobalTheory.AnPer.TenFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem uniformisedOneFormEvaluation_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  intro A _ g L u U V a ξ z hz
  obtain ⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  have hVU : V.1 ≤ U.1 := leOfHom a.unop
  have hzU : z ∈ pre u.ex U.1 := hmono _ _ hVU hz
  have evV := _root_.GlobalTheory.CechPer.evForm_rules A g L u V.1 z hz
  have evU := _root_.GlobalTheory.CechPer.evForm_rules A g L u U.1 z hzU
  have hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z := by
    intro b
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hopen V.1).mem_nhds hz] with w hw
    exact hres _ _ hVU b w hw
  have hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [p1_D, evV.2.2, evU.2.2]
    exact hD b
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul b x _ hx =>
    rw [oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]
    congr 1
    exact hres _ _ hVU b z hz

end GlobalTheory.CechPer
end

