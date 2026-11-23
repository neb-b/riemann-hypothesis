module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.DualLattices.RidConvolutionDerivation
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent
section
noncomputable section

open ReciprocityTheory.PGsh

namespace GlobalTheory.HeightOneHopf

theorem aeval_surjective_of_span_cotangent {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (hnil : IsNilpotent (RingHom.ker ε)) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin d → R, y - ∑ i, l i • x i ∈ RingHom.ker ε ^ 2) :
    Function.Surjective (MvPolynomial.aeval (R := R) x) := by
  first
  | exact @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | (apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker ..)

theorem exists_isPtDer_dual {k H : Type*} [Field k] [CommRing H] [Bialgebra k H] {d : ℕ}
    (x : Fin d → H) (hx : ∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H))
    (hind : ∀ l : Fin d → k,
      ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) :
    ∃ δ : Fin d → H →ₗ[k] k, (∀ i, IsPtDer (δ i)) ∧
      ∀ i j, δ i (x j) = if i = j then 1 else 0 := by
  classical
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI
  set J : Submodule k H := (I ^ 2).restrictScalars k with hJ
  let φ : (Fin d → k) →ₗ[k] H ⧸ J := J.mkQ ∘ₗ Fintype.linearCombination k x
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    apply hind l
    have h1 : Fintype.linearCombination k x l ∈ J := (Submodule.Quotient.mk_eq_zero J).1 hl
    rw [Fintype.linearCombination_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective hφ
  let π : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit
  have hπ : ∀ y ∈ I, π y = y := by
    intro y hy
    rw [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
    simp [π, hy]
  refine ⟨fun i => LinearMap.proj i ∘ₗ g ∘ₗ J.mkQ ∘ₗ π, fun i => ?_, fun i j => ?_⟩
  · apply isPtDer_of
    · simp [π]
    · intro f hf
      have hfI : f ∈ I := Ideal.pow_le_self two_ne_zero hf
      have h0 : J.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hf
      simp only [LinearMap.comp_apply, hπ f hfI, h0, map_zero]
  · have e : J.mkQ (x j) = φ (Pi.single j 1) := by
      simp [φ]
    have e2 : g (φ (Pi.single j 1)) = Pi.single j 1 := LinearMap.congr_fun hg _
    simp only [LinearMap.comp_apply, hπ _ (hx j), e, e2, LinearMap.proj_apply, Pi.single_apply]

theorem truncated_polynomial : TruncatedPolynomialStatement := by
  intro p hp k H _ _ _ _ _ d x hpow hx hspan hind
  have : IsNoetherianRing H := isNoetherian_of_tower k inferInstance
  have hnil : IsNilpotent (RingHom.ker (Bialgebra.counitAlgHom k H)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := aeval_surjective_of_span_cotangent _ hnil x hx hspan
  refine ⟨hsurj, le_antisymm ?_ ?_⟩
  · obtain ⟨δ, hδ, hδx⟩ := exists_isPtDer_dual x hx hind
    intro P hP
    apply mem_span_pow_of_coeff
    refine coeff_eq_zero_of_stable (Bialgebra.counitAlgHom k H) x hx (fun i => convD (δ i))
      (fun i => convD_mul _ (hδ i)) (fun i j => ?_) hsurj (CharP.cast_eq_zero k p)
      (fun n h0 hn => ?_) {0} ?_ ?_ P hP
    · rw [Bialgebra.counitAlgHom_apply, counit_convD, hδx]
    · rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff k p]
      exact Nat.not_dvd_of_pos_of_lt h0 hn
    · rintro a rfl; simp
    · rintro i a rfl; simp
  · intro P hP
    exact aeval_eq_zero_of_mem_span x (fun j => hpow _ (hx j)) hP

end GlobalTheory.HeightOneHopf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramified
section
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GenEigen

theorem mem_of_add_nil {B : Type*} [CommRing B] (J : Ideal B) (u N y : B)
    (hu : ∀ b, u * b ∈ J → b ∈ J) (k : ℕ) (hN : N ^ k ∈ J) (h : (u + N) * y ∈ J) : y ∈ J := by
  have hpow : ∀ (j : ℕ) b, u ^ j * b ∈ J → b ∈ J := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      apply hu
      apply ih
      rwa [← mul_assoc, ← pow_succ]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow u (-N) k
  apply hpow k
  have e : u ^ k * y = c * ((u + N) * y) + ((-1) ^ k * y) * N ^ k := by
    have : u ^ k = (u - -N) * c + (-N) ^ k := by rw [← hc]; ring
    rw [this, neg_pow N]; ring
  rw [e]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ hN)

theorem step {O B : Type*} [CommRing O] [CommRing B] (a p : O →+* B) (J : Ideal B)
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d) (ε : O)
    (h1 : ∃ y, ε * ε - ε = (l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (l ^ d) - x) = (l : O) * y)
    (hS : ∀ y, (l : B) * (a y - p y) ∈ J)
    (hreg : ∀ (e : O) b, p (1 + l * e) * b ∈ J → b ∈ J)
    (hnil : ∀ x, ∃ k : ℕ, (a x - p x) ^ k ∈ J)
    (hlim : ∃ n : ℕ, 1 - a (ε ^ (l ^ n)) ∈ J) (x : O) : a x - p x ∈ J := by
  have hε : a ε - p ε ∈ J := by
    obtain ⟨y, hy⟩ := h1
    obtain ⟨k, hk⟩ := hnil ε
    have ha : a ε * a ε - a ε = l * a y := by simpa using congrArg a hy
    have hp : p ε * p ε - p ε = l * p y := by simpa using congrArg p hy
    refine mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_
    · intro b hb
      apply hreg (4 * y)
      have : p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b) := by
        simp only [map_add (f := _), map_mul, map_one, map_natCast, map_ofNat]
        linear_combination (-4 * b) * hp
      rw [this]
      exact J.mul_mem_left _ hb
    · have : (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y) := by
        linear_combination ha - hp
      rw [this]
      exact hS y
  have ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J := by
    obtain ⟨y, hy⟩ := h2 x
    obtain ⟨n, hn⟩ := hlim
    have ha : a ε * (a x ^ (l ^ d) - a x) = l * a y := by simpa using congrArg a hy
    have hp : p ε * (p x ^ (l ^ d) - p x) = l * p y := by simpa using congrArg p hy
    set s := a x ^ (l ^ d) - a x
    set t := p x ^ (l ^ d) - p x
    have h3 : a ε * (s - t) ∈ J := by
      have : a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε) := by
        linear_combination ha - hp
      rw [this]
      exact J.sub_mem (hS y) (J.mul_mem_left _ hε)
    obtain ⟨j, hj⟩ : ∃ j, l ^ n = j + 1 := ⟨l ^ n - 1, by have := pow_pos hl n; omega⟩
    rw [hj, map_pow] at hn
    have : s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t)) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)
  obtain ⟨H, hH⟩ := Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)
  obtain ⟨k, hk⟩ := hnil x
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1)
    (H * (a x - p x)) _ ?_ k ?_ ?_
  · intro b hb
    apply hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))
    have : p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b =
        -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b) := by
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]
      ring
    rw [this]
    exact J.neg_mem hb
  · rw [mul_pow]; exact J.mul_mem_left _ hk
  · have e : p x + (a x - p x) = a x := by ring
    rw [e] at hH
    have : (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x)
        = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x) := by
      rw [hH]; ring
    rw [this]
    exact ht

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_one_add_mul {e z : C} {m : ℝ} (he : V.Ge 1 e) (h : V.Ge m ((1 + e) * z)) :
    V.Ge m z := by
  have h0 : V.v (1 + e) = 0 := by
    have : V.v 1 < V.v e := by
      rw [V.v.map_one]
      exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) he
    rw [V.v.map_add_eq_of_lt_left this, V.v.map_one]
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, zero_add] at h

theorem exists_ge (z : C) : ∃ m : ℝ, V.Ge m z := by
  unfold VF.Ge
  induction V.v z using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem eq_zero_of_forall_ge {z : C} (m : ℝ) (h : ∀ k : ℕ, V.Ge (m + k) z) : z = 0 := by
  by_contra hz
  have hne : V.v z ≠ ⊤ := by
    intro ht
    have h1 : V.v (z * z⁻¹) = ⊤ := by rw [V.v.map_mul, ht, top_add]
    rw [mul_inv_cancel₀ hz, V.v.map_one] at h1
    exact WithTop.zero_ne_top h1
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk⟩ := exists_nat_gt (t - m)
  have := h k
  unfold VF.Ge at this
  rw [← ht] at this
  have : m + k ≤ t := by exact_mod_cast this
  linarith

theorem ge_mulVec {κ : Type} [Fintype κ] {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j))
    {z : κ → C} {m : ℝ} (hz : ∀ i, V.Ge m (z i)) (i : κ) : V.Ge m (M.mulVec z i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)

def levelIdeal {κ : Type} [Fintype κ] [DecidableEq κ] {B : Type} [CommRing B]
    (Φ : B →+* Matrix κ κ C) (hΦ : ∀ b i j, V.Ge 0 (Φ b i j)) (w : κ → C) (m : ℝ) : Ideal B where
  carrier := {b | ∀ i, V.Ge m ((Φ b).mulVec w i)}
  add_mem' := by
    intro a b ha hb i
    rw [map_add (f := _), Matrix.add_mulVec]
    exact (ha i).add (hb i)
  zero_mem' := by
    intro i
    rw [map_zero, Matrix.zero_mulVec]
    exact VF.Ge.zero m
  smul_mem' := by
    intro c b hb i
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec]
    exact ge_mulVec (hΦ c) hb i

theorem eigen_of_gen_eigen (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type)
    [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C) (hL : ∀ x i j, V.Ge 0 (L x i j))
    (d : ℕ) (hd : 0 < d) (ε : O) (h1 : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) (ψ : O →+* C) (w : κ → C)
    (hψ : ∀ x, V.Ge 0 (ψ x))
    (hnil : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0)
    (hlim : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i))
    (x : O) : (L x).mulVec w = ψ x • w := by
  let P : O →+* Matrix κ κ C := (algebraMap C (Matrix κ κ C)).comp ψ
  have hP : ∀ x, P x = ψ x • (1 : Matrix κ κ C) := fun x => Algebra.algebraMap_eq_smul_one (ψ x)
  let Φ : O ⊗[ℤ] O →+* Matrix κ κ C :=
    (Algebra.TensorProduct.lift L.toIntAlgHom P.toIntAlgHom
      (fun x y => (Algebra.commutes (ψ y) (L x)).symm)).toRingHom
  have hΦt : ∀ x y, Φ (x ⊗ₜ y) = ψ y • L x := by
    intro x y
    change L x * P y = _
    rw [hP, Matrix.mul_smul, mul_one]
  have hΦ : ∀ b i j, V.Ge 0 (Φ b i j) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => intro i j; rw [map_zero]; exact VF.Ge.zero 0
    | tmul x y => intro i j; rw [hΦt]; exact (hψ y).mul_int (hL x i j)
    | add a b ha hb => intro i j; rw [map_add (f := _)]; exact (ha i j).add (hb i j)
  let a : O →+* O ⊗[ℤ] O := Algebra.TensorProduct.includeLeftRingHom
  let p : O →+* O ⊗[ℤ] O := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] O ⊗[ℤ] O).toRingHom
  have ha : ∀ x, Φ (a x) = L x := fun x => by
    change Φ (x ⊗ₜ 1) = _
    rw [hΦt, map_one, one_smul]
  have hp : ∀ x, Φ (p x) = ψ x • (1 : Matrix κ κ C) := fun x => by
    change Φ (1 ⊗ₜ x) = _
    rw [hΦt, map_one]
  have mem : ∀ m b, b ∈ levelIdeal Φ hΦ w m ↔ ∀ i, V.Ge m ((Φ b).mulVec w i) :=
    fun _ _ => Iff.rfl
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, ∀ i, V.Ge m0 (w i) := by
    choose f hf using fun i => exists_ge (V := V) (w i)
    obtain ⟨m0, hm0⟩ := (Set.finite_range f).bddBelow
    exact ⟨m0, fun i => (hf i).mono (hm0 ⟨i, rfl⟩)⟩
  have key : ∀ (k : ℕ) y, a y - p y ∈ levelIdeal Φ hΦ w (m0 + k) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [mem]
      rw [Nat.cast_zero, add_zero]
      exact ge_mulVec (hΦ _) hm0
    | succ k ih =>
      refine step a p _ V.l d V.l_prime.pos hd ε h1 h2 ?_ ?_ ?_ ?_
      · intro y
        rw [mem]
        intro i
        have := ((mem _ _).1 (ih y) i).l_mul
        rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec]
        exact this.mono (by push_cast; linarith)
      · intro e b hb
        rw [mem] at hb ⊢
        intro i
        have := hb i
        rw [map_mul, hp, Matrix.smul_mul, one_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
          map_add, map_one, map_mul, map_natCast] at this
        exact ge_of_one_add_mul (by simpa using (hψ e).l_mul) this
      · intro y
        obtain ⟨j, hj⟩ := hnil y
        refine ⟨j, (mem _ _).2 fun i => ?_⟩
        rw [map_pow, map_sub, ha, hp, hj]
        exact VF.Ge.zero _
      · obtain ⟨N, hN⟩ := exists_nat_ge (m0 + (k + 1 : ℕ))
        choose f hf using hlim N
        obtain ⟨n, hn⟩ := (Set.finite_range f).bddAbove
        refine ⟨n, (mem _ _).2 fun i => ?_⟩
        rw [map_sub, map_one, ha, Matrix.sub_mulVec, Matrix.one_mulVec]
        exact (hf i n (hn ⟨i, rfl⟩)).mono hN
  funext i
  have := eq_zero_of_forall_ge (V := V) m0 fun k => (mem _ _).1 (key k x) i
  rw [map_sub, ha, hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.GenEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootOfDerivationZeroStatement
section
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pth_root_of_derivation_zero : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K), (∀ D : Derivation ℤ K K, D f = 0) → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | exact GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemSupSpanXPowIffAndIsAdicComplete
section
namespace GlobalTheory.ChF

open MvPowerSeries

section

variable {R : Type*} [CommRing R] (I : Ideal R) {κ : Type*} [Finite κ]

private theorem mem_sup_pow_iff (n : ℕ) (f : MvPowerSeries κ R) :
    f ∈ (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) ^ n ↔
      ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree) := by
  first
  | exact @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | (apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem ..)

private theorem smodEq_pow_iff {S : Type*} [CommRing S] (J : Ideal S) (n : ℕ) (x y : S) :
    x ≡ y [SMOD (J ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

private theorem isAdicComplete_sup (hI : IsAdicComplete I R) :
    IsAdicComplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
  have hH : IsHausdorff (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun x hx => ?_⟩
    ext e
    refine hI.toIsHausdorff.haus _ fun n => ?_
    have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hx (n + e.degree))) e
    rw [smodEq_pow_iff]
    simpa using this
  have hP : IsPrecomplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun f hf => ?_⟩
    have hf' : ∀ {m n : ℕ}, m ≤ n → ∀ e : κ →₀ ℕ,
        coeff e (f m) - coeff e (f n) ∈ I ^ (m - e.degree) := fun h e => by
      have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hf h)) e
      rwa [map_sub] at this
    have hL : ∀ e : κ →₀ ℕ, ∃ L : R, ∀ n,
        coeff e (f (n + e.degree)) ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun e =>
      hI.toIsPrecomplete.prec (f := fun n => coeff e (f (n + e.degree))) fun {m n} h => by
        rw [smodEq_pow_iff]
        simpa using hf' (Nat.add_le_add_right h e.degree) e
    choose L hL using hL
    refine ⟨L, fun n => ?_⟩
    refine (smodEq_pow_iff _ _ _ _).2 ((mem_sup_pow_iff I _ _).2 fun e => ?_)
    have h1 := (smodEq_pow_iff _ _ _ _).1 (hL e (n - e.degree))
    have h2 := hf' (show n ≤ n - e.degree + e.degree by omega) e
    have h3 := add_mem h2 h1
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact IsAdicComplete.mk

end

theorem mem_sup_span_X_pow_iff_and_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : Type) [Finite κ], (∀ (n : ℕ) (f : MvPowerSeries κ R), f ∈ (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) ^ n ↔ ∀ e : κ →₀ ℕ, MvPowerSeries.coeff e f ∈ I ^ (n - e.degree)) ∧ (IsAdicComplete I R → IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)) :=
  fun _ _ I _ _ => ⟨mem_sup_pow_iff I, isAdicComplete_sup I⟩

end GlobalTheory.ChF
end

