module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariantStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalThetaExponent_symplectic_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  first | exact @GlobalTheory.SW.canon_exponent_invariant | exact GlobalTheory.SW.canon_exponent_invariant | (intros; apply GlobalTheory.SW.canon_exponent_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by
  obtain ⟨R, hR, hs, hp⟩ := h
  obtain ⟨D, hD, ha⟩ := heisS_exists_den a
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))
  refine ⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩
  · intro x hx k i
    have h1 := hs x (left_ne_zero_of_mul hx) k i
    have : (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [this]; exact (hn D).mul h1
  · intro x y hy
    have e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul]
    have hy' : IntM ((D : ℚ) • y) := fun k i => by
      simpa using (hn D).mul (hy k i)
    have hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))) :=
      IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ)
        = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n := by
      have : (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by simpa using hn'
      rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k
          = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
      rw [this]; ring
    simp only []
    rw [e2, e1, hp x _ hy']
    congr 1
    rw [Rat.cast_add, mul_add, Complex.exp_add]
    have : (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem heisS_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  intro κ ι _ _ _ a b φ hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSB_mul_char a b _ ((_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1
  · intro τ hτ ζ
    unfold thS
    rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, heisS, add_sub_cancel_right]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v := fun u v => by
      simp [dotProduct, qv]
    have hadd : qv ((y + b) k) = qv (y k) + qv (b k) := by
      ext i; simp [qv]
    have hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
    rw [Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]
    push_cast; ring
  · intro a' b'
    funext x
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]
    congr 2
    rw [← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  · funext x
    simp [heisS, dotProduct]
  · intro ψ hψ
    have h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x)) := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1
    have h2 := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι φ _ hφ h1).2.2.1
    have h3 := ((_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2
    unfold ip
    refine Eq.trans ?_ h3
    congr 1
    funext x
    simp only [heisS, Pi.mul_apply, map_mul]
    rw [← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    simp

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ShapeOps

theorem mu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, mul_comm m n, pow_mul, hb]; simp

theorem mu_inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩

theorem mu_conj {a : ℂ} (ha : IsMu a) : IsMu (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [← map_pow, ha, map_one]⟩

theorem mu_ne {a : ℂ} (ha : IsMu a) : a ≠ 0 := by
  obtain ⟨m, hm, ha⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at ha
  exact zero_ne_one ha

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb,
    ← pow_mul]

theorem ph_conj {a : ℂ} (ha : Ph a) : Ph (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← map_pow, ha, map_pow, Complex.conj_ofReal, Complex.norm_conj]

section Quad

variable {M : Type} [AddCommGroup M]

theorem quad_mul {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by
  refine ⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := hf.2 x hx y hy z hz
  have h2 := hg.2 x hx y hy z hz
  calc _ = (f (x + y + z) * f x * f y * f z) * (g (x + y + z) * g x * g y * g z) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem quad_conj {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) : Quad S (fun x => conj (f x)) := by
  refine ⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := congrArg conj (hf.2 x hx y hy z hz)
  simpa only [map_mul] using h1

theorem quad_mono {S S' : AddSubgroup M} {f : M → ℂ} (h : S' ≤ S) (hf : Quad S f) : Quad S' f :=
  ⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩

theorem quad_affine {S : AddSubgroup M} {h : M → ℂ} (h1 : ∀ x ∈ S, IsMu (h x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, h (x + y) * h 0 = h x * h y) : Quad S h := by
  refine ⟨h1, fun x hx y hy z hz => ?_⟩
  have h0 : h 0 ≠ 0 := mu_ne (h1 0 S.zero_mem)
  have e1 : h (x + y) = h x * h y / h 0 := by rw [eq_div_iff h0]; exact h2 x hx y hy
  have e2 : h (y + z) = h y * h z / h 0 := by rw [eq_div_iff h0]; exact h2 y hy z hz
  have e3 : h (x + z) = h x * h z / h 0 := by rw [eq_div_iff h0]; exact h2 x hx z hz
  have e4 : h (x + y + z) = h (x + y) * h z / h 0 := by
    rw [eq_div_iff h0]; exact h2 _ (S.add_mem hx hy) z hz
  rw [e4, e1, e2, e3]
  field_simp

theorem quad_shift {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) {d : M} (hd : d ∈ S) :
    Quad S (fun x => f (x + d)) := by
  have hq : Quad S (fun x => f (x + d) * (f x)⁻¹) := by
    refine quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx)))
      fun x hx y hy => ?_
    have h := hf.2 x hx y hy d hd
    have n0 := mu_ne (hf.1 0 S.zero_mem)
    have nx := mu_ne (hf.1 x hx)
    have ny := mu_ne (hf.1 y hy)
    have nxy := mu_ne (hf.1 _ (S.add_mem hx hy))
    simp only [zero_add]
    field_simp
    linear_combination h
  have hm := quad_mul hf hq
  have key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹) := fun x hx => by
    have nx := mu_ne (hf.1 x hx)
    field_simp
  refine ⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩
  have := hm.2 x hx y hy z hz
  simp only at this ⊢
  rw [← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy),
    ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz),
    ← key _ (S.add_mem (S.add_mem hx hy) hz)] at this
  exact this

end Quad

variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem chr_add (y x x' : Matrix κ ι ℚ) : chr y (x + x') = chr y x * chr y x' := by
  unfold chr
  rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_dotProduct]; rfl

theorem mu_exp (q : ℚ) : IsMu (cexp (2 * Real.pi * I * (q : ℂ))) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℚ) * q) = q.num := Rat.den_mul_eq_num q
  have h' : ((q.den : ℂ) * q) = q.num := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h
  rw [show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem intM_nsmul (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := fun k i => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))

theorem exists_den (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num) := by
    have h := Rat.den_mul_eq_num (y k i)
    simp only [eq_intCast]
    push_cast
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem chr_eq_one {y z : Matrix κ ι ℚ} {N : ℕ} (hy : IntM ((N : ℚ) • y)) (hz : IntM z) :
    chr y ((N : ℚ) • z) = 1 := by
  have h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k) := by
    refine IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_
    have := (hz k i).mul (hy k i)
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    convert this using 1; ring
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  unfold chr
  rw [← hn, mul_comm]
  simp only [eq_intCast, Rat.cast_intCast]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem isSB_mul_chr {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) (y : Matrix κ ι ℚ) :
    IsSB (fun x => φ x * chr y x) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨N, hN, hy⟩ := exists_den y
  refine ⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩
  · have := intM_nsmul N (h1 x (left_ne_zero_of_mul hx))
    rwa [smul_smul, ← Nat.cast_mul] at this
  · have e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    have a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x := by rw [e1]; exact h2 x _ (intM_nsmul N hz)
    have a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x := by
      rw [chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]
    simp only [a1, a2]

theorem shape_conj {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) : Shape (fun x => conj (φ x)) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf,
    fun x => ?_⟩
  simp only [hφ x]
  split_ifs <;> simp

theorem shape_chr {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  have hq : Quad S (fun x => chr y (x + a)) := by
    refine quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_
    simp only [← chr_add]
    congr 1; abel
  refine ⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩
  simp only [hφ x, sub_add_cancel]
  split_ifs <;> simp [mul_assoc]

theorem shape_mul {φ ψ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (h' : Shape ψ) :
    Shape (fun x => φ x * ψ x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  obtain ⟨hs', c', a', S', f', hc', hf', hψ⟩ := h'
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩
  by_cases hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'
  · obtain ⟨b, hb, hb'⟩ := hb
    refine ⟨c * c', b, S ⊓ S', _, ph_mul hc hc',
      quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')),
      fun x => ?_⟩
    have i1 : x - a ∈ S ↔ x - b ∈ S := by
      rw [show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb
    have i2 : x - a' ∈ S' ↔ x - b ∈ S' := by
      rw [show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'
    simp only [hφ x, hψ x, sub_add_sub_cancel]
    by_cases p : x - b ∈ S
    · by_cases p' : x - b ∈ S'
      · rw [if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]; ring
      · rw [if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]
    · rw [if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]
  · refine ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩
    have : φ x * ψ x = 0 := by
      rw [hφ x, hψ x]
      by_cases p : x - a ∈ S
      · have p' : x - a' ∉ S' := fun p' => hb ⟨x, p, p'⟩
        simp [p']
      · simp [p]
    simp [this]

end GlobalTheory.Phase.ShapeOps

theorem GlobalTheory.Phase.shape_conj_chr_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) :=
  fun _ _ _ _ _ _ h => ⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PoissonSummationThetaSeriesRowTermCoset
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ.Row

variable {ι : Type} [Fintype ι]



open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.SW.FourierJ.Row.poisson_class : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : ℕ), 0 < R → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, -τ⁻¹ ∈ _root_.GlobalTheory.SW.Siegel ι →
    IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧
    ∀ (a : ι → ℚ) (ζ : ι → ℂ),
    (Summable fun m : ι → ℤ => ‖_root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    (Summable fun m : ι → ℤ =>
      ‖_root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) *
      ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
    c * ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
      _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) := by
  intro ι _ _ R hR τ hτ hτ' hdet
  have hτS : _root_.GlobalTheory.IsSiegel τ := hτ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef
  have hΩ : _root_.GlobalTheory.IsSiegel Ω := hτS.natCast_smul (pow_pos hR 2)
  have hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]
  have T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ) := by
      funext i
      simp only [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp
      ring
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, _root_.GlobalTheory.SW.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero,
      add_zero]
    generalize (fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x
    congr 1
    simp only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    push_cast
    ring
  have T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ) := by
      funext i
      simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv]
    have hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ := by
      rw [← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]
    have hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) : ℚ)) : ℂ) =
        (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, _root_.GlobalTheory.SW.FourierJ.zv, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) =
        Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ) := rfl
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]
    rw [_root_.GlobalTheory.SW.FourierJ.gs, _root_.GlobalTheory.SW.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]
    generalize (fun i => ((m i : ℤ) : ℂ)) = x
    congr 1
    simp only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]
    first | (field_simp; ring) | field_simp | ring
  refine ⟨_root_.GlobalTheory.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩
  · have h := hΩ.siegelGaussIntegral_sq_mul_det
    rw [hΩdef, smul_smul, Matrix.det_smul] at h
    rw [show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]
    exact h
  have hS1 := hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)
  have hS2 := hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R)
    (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))
  refine ⟨?_, ?_, ?_⟩
  · exact hS1.congr fun m => by rw [T1]
  · refine hS2.congr fun m => ?_
    rw [← T2, norm_mul, _root_.GlobalTheory.SW.FourierJ.norm_ech, one_mul]
  · have e1 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T1 a ζ m
    have e2 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T2 a ζ m
    have hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ := by
      rw [hΩinv]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      first | (field_simp; ring) | field_simp
    rw [e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]
    have hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    linear_combination (_root_.GlobalTheory.siegelGaussIntegral Ω *
      _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp

end GlobalTheory.SW.FourierJ.Row
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → (ip φ φ).im = 0 ∧ 0 ≤ (ip φ φ).re ∧ (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * (ip φ φ).re) ∧ (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (ip φ φ).re ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, IsSB ψ → ‖ip φ ψ‖ ^ 2 ≤ (ip φ φ).re * (ip ψ ψ).re := by
  first | exact @GlobalTheory.SW.ip_self_nonneg_and_bounds | exact GlobalTheory.SW.ip_self_nonneg_and_bounds | (intros; apply GlobalTheory.SW.ip_self_nonneg_and_bounds <;> assumption)
end

