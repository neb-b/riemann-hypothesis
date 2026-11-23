module

public import Mathlib
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.DualLattices.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisGram
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma gram_zero (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h
  have e : z * z = z := B.pairing_unique N 0 y _ _ h hz
  have e1 : z = 1 := by simpa using e
  rwa [e1] at hz

private lemma gram_nsmul (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (m : ℕ) : B.IsPairing N (m • x) y (z ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact gram_zero B N y h.2.1
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ y _ _ ih h

private lemma gram_sum {κ : Type} (s : Finset κ) (N : ℕ) (x : κ → B.G R) (y : B.G R)
    (z : κ → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact gram_zero B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ y _ _ (h a) ih

end SlopeTestRemainingChoices

private lemma gram_limit {p : ℕ} [Fact p.Prime] (k : ℕ → ℕ)
    (hk : ∀ n, k n ≡ k (n + 1) [MOD p ^ (n + 1)]) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow (n + 1) a = (k n : ZMod (p ^ (n + 1))) := by
  have hi : ∀ i : ℕ, (p : ℤ) ^ i ∣ (fun i : ℕ => (k (i - 1) : ℤ)) (i + 1) -
      (fun i : ℕ => (k (i - 1) : ℤ)) i := by
    intro i
    cases i with
    | zero => simp
    | succ n =>
      have h := (Nat.modEq_iff_dvd.1 (hk n))
      simpa using h
  have key := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i : ℕ => (k (i - 1) : ℤ)) p hi
  refine ⟨_, fun n => (key (n + 1)).trans ?_⟩
  simp only [Nat.add_sub_cancel, Int.cast_natCast]

private lemma gram_ext {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, h,
    PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) b]

private lemma gram_toZMod {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (k : ℕ)
    (h : PadicInt.toZModPow (0 + 1) a = (k : ZMod (p ^ (0 + 1)))) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : a - (k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (0 + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, h, sub_self]
  rw [PadicInt.ker_toZModPow, zero_add, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h1
  exact h1

theorem tateBasis_gram :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by
  intro R₀ _ p hp g B Tw _ _ _ hζ hζp τ htors hcomp hbasis hnd
  have hex : ∀ i j n, ∃ k : ℕ, k < p ^ (n + 1) ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := by
    intro i j n
    obtain ⟨z, hz⟩ := B.pairing_exists _ _ _ (htors i n) (htors j n)
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    obtain ⟨k, hk, e⟩ := (hζ n).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ z).2 (B.pairing_pow _ _ _ _ hz))
    exact ⟨k, hk, e ▸ hz⟩
  choose k hklt hk using hex
  have hcompat : ∀ i j n, k i j n ≡ k i j (n + 1) [MOD p ^ (n + 1)] := by
    intro i j n
    have h1 := gram_nsmul B _ _ _ _ (hk i j (n + 1)) p
    rw [← hcomp, pow_succ p (n + 1)] at h1
    have h2 := B.pairing_mul _ p _ _ _ (htors i n)
      (by rw [← pow_succ]; exact htors j (n + 1)) h1
    rw [← hcomp, ← pow_mul, mul_comm, pow_mul, hζp] at h2
    have h3 := B.pairing_unique _ _ _ _ _ (hk i j n) h2
    rwa [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf] at h3
  choose E hE using fun i j => gram_limit (k i j) (hcompat i j)
  have hanti : ∀ i j, E j i = -E i j := by
    intro i j
    refine gram_ext _ _ fun n => ?_
    have h1 := B.pairing_unique _ _ _ _ _ (hk j i n) (B.pairing_sw _ _ _ _ (hk i j n))
    rw [eq_inv_iff_mul_eq_one, ← pow_add, (hζ n).pow_eq_one_iff_dvd,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_add] at h1
    rw [map_neg, hE, hE]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Matrix.of E, ⟨?_, fun i => ?_⟩, ?_, fun i j n => ?_⟩
  · apply Matrix.ext
    intro i j
    exact hanti i j
  · exact self_eq_neg.1 (hanti i i)
  · by_contra hu
    have hd : (Matrix.of E).det ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      exact hu
    rw [RingHom.mem_ker, RingHom.map_det] at hd
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have ht0 : ∀ i, p • τ i 0 = 0 := fun i => by simpa using htors i 0
    have hpt : ∀ t : Ix g → ZMod p, p • ptOf B τ t = 0 := fun t => by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by rw [ht0, smul_zero]
    have hrow : ∀ j, B.IsPairing p (ptOf B τ s) (τ j 0) 1 := by
      intro j
      have h1 := gram_sum B Finset.univ (p ^ (0 + 1)) (fun i => (s i).val • τ i 0) (τ j 0)
        (fun i => (Tw.ζ 0 ^ k i j 0) ^ (s i).val) (htors j 0)
        (fun i => gram_nsmul B _ _ _ _ (hk i j 0) _)
      have h2 : ∏ i, (Tw.ζ 0 ^ k i j 0) ^ (s i).val = 1 := by
        simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum, (hζ 0).pow_eq_one_iff_dvd, zero_add, pow_one,
          ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (congrFun hs j)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm, ← gram_toZMod _ _ (hE i j 0)]
        rfl
      rw [h2, zero_add, pow_one] at h1
      exact h1
    have hx : ptOf B τ s = 0 := by
      refine hnd _ (hpt s) fun y hy => ?_
      obtain ⟨t, rfl, -⟩ := hbasis y hy
      have h1 := gram_sum B Finset.univ p (fun j => (t j).val • τ j 0) (ptOf B τ s)
        (fun j => (1⁻¹) ^ (t j).val) (hpt s)
        (fun j => gram_nsmul B _ _ _ _ (B.pairing_sw _ _ _ _ (hrow j)) _)
      have h2 := B.pairing_sw _ _ _ _ h1
      simp only [inv_one, one_pow, Finset.prod_const_one] at h2
      exact h2
    have h0 : (0 : B.G Tw.O) = ptOf B τ (0 : Ix g → ZMod p) := by simp [ptOf]
    exact hs0 ((hbasis 0 (smul_zero p)).unique hx.symm h0)
  · rw [Matrix.of_apply, hE, ZMod.val_cast_of_lt (hklt i j n)]
    exact hk i j n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
section
namespace GlobalTheory

private theorem tateMat_val_smul {Γ : Type} [AddCommGroup Γ] {N : ℕ} [NeZero N] {x : Γ}
    (hx : N • x = 0) (a : ℤ) : ((a : ZMod N).val) • x = a • x := by
  have h : (N : ℤ) ∣ a - ((a : ZMod N).val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; simp
  obtain ⟨c, hc⟩ := h
  have h2 : a = ((a : ZMod N).val : ℤ) + c * N := by linarith
  conv_rhs => rw [h2, add_smul, mul_smul, natCast_zsmul, natCast_zsmul, hx, smul_zero, add_zero]

section
variable {p : ℕ} [hp : Fact p.Prime] {κ Γ : Type} [Fintype κ] [AddCommGroup Γ] {τ : κ → ℕ → Γ}

private theorem tateMat_zero (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (j : κ) (n : ℕ) :
    τ j 0 = (p ^ n) • τ j n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, h2 j n, pow_succ, mul_smul]

private theorem tateMat_step (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (a : κ → ℤ) (n : ℕ) :
    ∑ j, a j • τ j n = p • ∑ j, a j • τ j (n + 1) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 j n, smul_comm]

private theorem tateMat_exists (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ x : Γ, (p ^ (n + 1)) • x = 0 → ∃ a : κ → ℤ, x = ∑ j, a j • τ j n := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨t, ht, -⟩ := h3 x (by simpa using hx)
    exact ⟨fun j => ((t j).val : ℤ), by simpa only [natCast_zsmul] using ht⟩
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha⟩ := ih (p • x) (by rw [← mul_smul, ← pow_succ, hx])
    obtain ⟨t, ht, -⟩ := h3 (x - ∑ j, a j • τ j (n + 1)) (by
      rw [smul_sub, ← tateMat_step h2, ha, sub_self])
    refine ⟨fun j => a j + (((t j).val * p ^ (n + 1) : ℕ) : ℤ), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, mul_smul, ← tateMat_zero h2]
    rw [← ht]; abel

private theorem tateMat_dvd (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ a : κ → ℤ, ∑ j, a j • τ j n = 0 → ∀ j, ((p ^ (n + 1) : ℕ) : ℤ) ∣ a j := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have base : ∀ a : κ → ℤ, ∑ j, a j • τ j 0 = 0 → ∀ j, (p : ℤ) ∣ a j := by
    intro a ha j
    have hu := (h3 0 (smul_zero _)).unique (y₁ := fun j => (a j : ZMod p)) (y₂ := fun _ => 0)
      (by
        rw [← ha]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (tateMat_val_smul (by simpa using h1 k 0) _).symm)
      (by simp)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hu j)
  induction n with
  | zero => intro a ha j; simpa using base a ha j
  | succ n ih =>
    intro a ha j
    have hd := ih a (by rw [tateMat_step h2, ha, smul_zero])
    choose b hb using hd
    have := base b (by
      rw [← ha]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k, tateMat_zero h2 k (n + 1), mul_comm, mul_smul, natCast_zsmul]) j
    rw [hb j, pow_succ p (n + 1)]
    push_cast
    exact mul_dvd_mul_left _ this

private theorem tateMat_congr (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ)
    (a b : κ → ℤ) (h : ∑ j, a j • τ j n = ∑ j, b j • τ j n) (j : κ) :
    ((p ^ (n + 1) : ℕ) : ℤ) ∣ b j - a j := by
  refine tateMat_dvd h1 h2 h3 n (fun j => b j - a j) ?_ j
  simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]

private theorem tateMat_limit (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (f : AddMonoid.End Γ) (j : κ) :
    ∃ c : κ → ℤ_[p], ∀ n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hex : ∀ n, ∃ a : κ → ℤ, f (τ j n) = ∑ k, a k • τ k n := fun n =>
    tateMat_exists h2 h3 n _ (by rw [← map_nsmul, h1, map_zero])
  choose a ha using hex
  have hc : ∀ k i, (p : ℤ) ^ i ∣ (fun i => a (i - 1) k) (i + 1) - (fun i => a (i - 1) k) i := by
    intro k i
    cases i with
    | zero => simp
    | succ m =>
      have := tateMat_congr h1 h2 h3 m (a m) (a (m + 1)) (by
        rw [← ha, tateMat_step h2, ← ha, ← map_nsmul, ← h2]) k
      simpa using this
  refine ⟨fun k => PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k)), fun n => ?_⟩
  rw [ha n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k) (n + 1)]
  exact (tateMat_val_smul (h1 k n) _).symm

private theorem tateMat_unique (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (c d : κ → ℤ_[p]) (b : ℕ → κ → ℤ)
    (hb : ∀ n k, (b n k : ZMod (p ^ (n + 1))) = PadicInt.toZModPow (n + 1) (d k))
    (h : ∀ n, ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n = ∑ k, b n k • τ k n)
    (k : κ) : c k = d k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := tateMat_congr h1 h2 h3 n
      (fun k => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ)) (b n)
      (by simpa only [natCast_zsmul] using h n) k
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hb] at this
    simpa using this

end

theorem tate_basis_matrix :
    (∀ (p : ℕ) [Fact p.Prime] (κ Γ : Type) [Fintype κ] [DecidableEq κ] [AddCommGroup Γ] (τ : κ → ℕ → Γ),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) →
    (∀ n (x : Γ), (p ^ (n + 1)) • x = 0 → ∃! t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n) ∧
    ∃ ρ : AddMonoid.End Γ →+* Matrix κ κ ℤ_[p], ∀ (f : AddMonoid.End Γ) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n) := by
  intro p hp κ Γ _ _ _ τ h1 h2 h3
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨fun n x hx => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := tateMat_exists h2 h3 n x hx
    have key : ∀ t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n →
        t = fun j => (a j : ZMod (p ^ (n + 1))) := by
      intro t ht
      funext j
      have := tateMat_congr h1 h2 h3 n (fun j => ((t j).val : ℤ)) a
        (by simpa only [natCast_zsmul, ← ha] using ht.symm) j
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      simpa using this
    refine ⟨fun j => (a j : ZMod (p ^ (n + 1))), ?_, key⟩
    rw [ha]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (tateMat_val_smul (h1 k n) _).symm
  · choose c hc using tateMat_limit h1 h2 h3
    let r : AddMonoid.End Γ → Matrix κ κ ℤ_[p] := fun f => Matrix.of fun k j => c f j k
    have hr : ∀ f k j, r f k j = c f j k := fun _ _ _ => rfl
    refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, fun f j n => hc f j n⟩
    · apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c 1 j) (fun k => (1 : Matrix κ κ ℤ_[p]) k j)
        (fun _ k => if k = j then 1 else 0) (fun n k => ?_) (fun n => ?_) k
      · by_cases h : k = j <;> simp [Matrix.one_apply, h]
      · rw [← hc]; simp
    · intro f g
      apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c (f * g) j) (fun k => (r f * r g) k j)
        (fun n k => ∑ l, ((PadicInt.toZModPow (n + 1) (c f l k)).val : ℤ) *
          ((PadicInt.toZModPow (n + 1) (c g j l)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp [Matrix.mul_apply, hr]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [← hc, AddMonoid.End.coe_mul, Function.comp_apply, hc g j n, map_sum]
          simp only [Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_nsmul, hc f l n, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul]
    · apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c 0 j) (fun _ => 0)
        (fun _ _ => 0) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]; simp
    · intro f g
      apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c (f + g) j) (fun k => c f j k + c g j k)
        (fun n k => ((PadicInt.toZModPow (n + 1) (c f j k)).val : ℤ) +
          ((PadicInt.toZModPow (n + 1) (c g j k)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]
        simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, ← hc]
        rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValNatCastSmul
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.EvAct

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

private lemma val_natCast_smul {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (n : ℕ) :
    ((n : ZMod p)).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]

private lemma val_sum_mul_smul {M ι : Type} [AddCommGroup M] [Fintype ι] (x : M) (hx : p • x = 0)
    (u v : ι → ZMod p) : (∑ j, u j * v j).val • x = ∑ j, (v j).val • (u j).val • x := by
  have h : (∑ j, u j * v j) = ((∑ j, (v j).val * (u j).val : ℕ) : ZMod p) := by
    push_cast
    simp [mul_comm]
  rw [h, val_natCast_smul x hx, Finset.sum_smul]
  simp only [mul_smul]

private lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO _) = LHom.id Tw.O ∧ B.map (D.ptMap t) (D.fin.y _) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

private lemma tau_p (D : Dat p g B Tw Dt Oe σ cp) (j : Ix g) : p • D.L.τ j 0 = 0 := by
  have h := D.L.τ_tors j 0
  rwa [zero_add, pow_one] at h

private lemma act_ptOf (D : Dat p g B Tw Dt Oe σ cp) (a : Oe) (t : Nb p g) :
    (D.A.act a Tw.O (LHom.id Tw.O) ⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : B.G Tw.O) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have h : (⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : torP B p Tw.O) =
      ∑ j, (t j).val • (⟨D.L.τ j 0, (mem_torP B p _).2 (tau_p D j)⟩ : torP B p Tw.O) := by
    apply Subtype.ext
    simp [ptOf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, AddSubgroup.val_finsetSum]
  simp only [map_nsmul, AddSubgroup.coe_nsmul]
  simp only [D.L.ρ_spec, Finset.smul_sum]
  rw [Finset.sum_comm, ptOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, val_sum_mul_smul _ (tau_p D k)]
  rfl

private lemma red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext k
  exact (RingHom.map_mulVec PadicInt.toZMod M t k)

private lemma eval_congr (D : Dat p g B Tw Dt Oe σ cp) (F : ∀ i, (D.fin.AAx i : Type))
    {i j : D.fin.ι} (φ : LHom (D.fin.AAx i) Tw.O) (φ' : LHom (D.fin.AAx j) Tw.O) (h : i = j)
    (h' : HEq φ φ') : φ.1 (F i) = φ'.1 (F j) := by
  subst h
  rw [eq_of_heq h']

private lemma evAll_act (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C]
    [Algebra (Tw.O : Type) C] (a : Oe) (F : ∀ i, (D.fin.AAx i : Type)) :
    ∃ F' : ∀ i, (D.fin.AAx i : Type), ∀ t : Nb p g,
      D.evAll C F' t = D.evAll C F (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have key := fun i => D.fin.univ (D.fin.AAx i) (D.fin.sO i)
    (D.A.act a (D.fin.AAx i) (D.fin.sO i) ⟨D.fin.y i, (mem_torP B p _).2 (D.fin.y_p i)⟩ : B.G _)
    ((mem_torP B p _).1 (Subtype.property _))
  choose m α hs hy _ using key
  refine ⟨fun i => (α i).1 (F (m i)), fun t => ?_⟩
  obtain ⟨h1, h2, -⟩ := ptMap_spec D t
  obtain ⟨-, -, h3⟩ := ptMap_spec D (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t)
  have e1 : ((D.ptMap t).comp (α (D.ptIdx t))).comp (D.fin.sO _) = LHom.id Tw.O := by
    rw [← h1, ← hs (D.ptIdx t)]
    rfl
  have e2 : B.map ((D.ptMap t).comp (α (D.ptIdx t))) (D.fin.y _) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
    rw [B.map_comp, hy, D.A.act_nat a _ _ _ h1, ← act_ptOf]
    congr 2
    exact Subtype.ext h2
  obtain ⟨h4, h5⟩ := h3 _ _ e1 e2
  unfold Dat.evAll
  rw [← eval_congr D F _ _ h4 h5]
  rfl

theorem evImg_act_stable :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvActStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ a f hf
  refine ⟨fun t => f (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t), ?_, fun t => by rw [red_mulVec]⟩
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    obtain ⟨F', hF'⟩ := evAll_act D C a F
    exact Submodule.subset_span ⟨F', funext hF'⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.EvAct
end
end

