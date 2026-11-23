module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Imports
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem stepC : StepC := by
  intro a b c d ha hd lam hlam hok m _ _ Λa g hθ l hl hiso h1 hl1 h2
  classical
  set θ := cmTheta b d with hθdef
  set S := stdLat (cmL a b d ha hd lam hlam) m with hSdef
  set X := imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hXdef
  have hθn : θ * ((b : ℂ) - θ) = (a : ℂ) * c := theta_norm hok.1
  have hθθ : θ * θ = (b : ℂ) * θ - (a : ℂ) * c := by linear_combination -hθn

  have hXθ : ∀ x ∈ X, θ • x ∈ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨θ • y, hθ y hy, by simp⟩
  have hlin : ∀ p q : ℤ, ∀ x ∈ X, ((p : ℂ) + (q : ℂ) * θ) • x ∈ X := by
    intro p q x hx
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul ℂ p, Int.cast_smul_eq_zsmul ℂ q]
    exact X.add_mem (X.zsmul_mem hx p) (X.zsmul_mem (hXθ x hx) q)

  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℂ, ∀ u, β u = 1 + ((u * l : ℕ) : ℂ) * θ := ⟨_, fun _ => rfl⟩
  obtain ⟨βb, hβb⟩ : ∃ βb : ℕ → ℂ, ∀ u, βb u = 1 + ((u * l : ℕ) : ℂ) * ((b : ℂ) - θ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℤ, ∀ u, K u = 1 + ((u * l : ℕ) : ℤ) * b + ((u * l : ℕ) : ℤ) ^ 2 * a * c :=
    ⟨_, fun _ => rfl⟩
  have hconj : ∀ u, (starRingEnd ℂ) (β u) = βb u := by
    intro u
    rw [hβ, hβb, map_add (f := _), map_one, map_mul, map_natCast, hθdef, theta_conj]
  have hK : ∀ u, β u * βb u = ((K u : ℤ) : ℂ) := by
    intro u
    rw [hβ, hβb, hKdef]
    push_cast
    linear_combination ((u : ℂ) * l) ^ 2 * hθn
  have hKpos : ∀ u, 0 < K u := by
    intro u
    rw [hKdef]
    set U : ℤ := ((u * l : ℕ) : ℤ) with hU
    have h4 := hok.1
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have key : 4 * (1 + U * b + U ^ 2 * a * c) = (2 + U * b) ^ 2 + U ^ 2 * d := by
      linear_combination U ^ 2 * h4
    rcases eq_or_ne U 0 with h0 | h0
    · rw [h0]
      norm_num
    · have hU2 : 1 ≤ U ^ 2 := by
        have := pow_pos (abs_pos.2 h0) 2
        rw [sq_abs] at this
        omega
      nlinarith [sq_nonneg (2 + U * b)]
  have hβ0 : ∀ u, β u ≠ 0 := fun u h => by
    have := hK u
    rw [h, zero_mul] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)
  have hβb0 : ∀ u, βb u ≠ 0 := fun u h => by
    have := hK u
    rw [h, mul_zero] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)

  have hinj : Function.Injective (fun u => (β u / βb u)⁻¹) := by
    intro u v huv
    simp only [inv_inj] at huv
    rw [div_eq_div_iff (hβb0 u) (hβb0 v), hβ, hβ, hβb, hβb] at huv
    have h2θ : 2 * θ - b ≠ 0 := two_theta_sub b hd
    have hmul : (((u * l : ℕ) : ℂ) - ((v * l : ℕ) : ℂ)) * (2 * θ - b) = 0 := by
      linear_combination huv
    rcases mul_eq_zero.1 hmul with h | h
    · have h' : u * l = v * l := Nat.cast_injective (sub_eq_zero.1 h)
      exact Nat.eq_of_mul_eq_mul_right hl.pos h'
    · exact absurd h h2θ

  have hfin := Module.End.finite_hasEigenvalue (g : Module.End ℂ (m → ℂ))
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finite hfin
  set w := β u / βb u with hwdef
  have hw0 : w ≠ 0 := div_ne_zero (hβ0 u) (hβb0 u)
  let δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := g.trans (LinearEquiv.smulOfNeZero ℂ (m → ℂ) w hw0)
  have hδ : ∀ x, δ x = w • g x := fun x => rfl
  have hcb : (starRingEnd ℂ) (βb u) = β u := by rw [← hconj u, Complex.conj_conj]
  have hww : (starRingEnd ℂ) w * w = 1 := by
    rw [hwdef, map_div₀, hconj u, hcb]
    field_simp [hβ0 u, hβb0 u]
  have hisoδ : IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) := by
    intro x y
    show stdH (cmL a b d ha hd lam hlam) m (w • g x) (w • g y) = stdH (cmL a b d ha hd lam hlam) m x y
    rw [LinearMap.map_smul (stdH (cmL a b d ha hd lam hlam) m) w (g x), LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm w, hww, one_mul]
    exact hiso x y
  have himg : imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa = X.map (smulHom w) := by
    rw [hXdef]
    unfold imgLat
    rw [AddSubgroup.map_map]
    congr 1

  set Nn := (K u).toNat with hNndef
  have hNnZ : ((Nn : ℕ) : ℤ) = K u := Int.toNat_of_nonneg (hKpos u).le
  have hNn : ((Nn : ℕ) : ℂ) = β u * βb u := by
    rw [hK u, ← hNnZ, Int.cast_natCast]
  have hN0 : Nn ≠ 0 := by have := hKpos u; omega
  have ha' : ∀ x ∈ X, (Nn : ℂ) • w • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w = (((1 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        (((2 * ((u * l : ℕ) : ℤ) + ((u * l : ℕ) : ℤ) ^ 2 * b : ℤ)) : ℂ) * θ := by
      rw [hNn, hwdef]
      have : β u * βb u * (β u / βb u) = β u * β u := by field_simp [hβb0 u]
      rw [this, hβ]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  have hb' : ∀ x ∈ X, (Nn : ℂ) • w⁻¹ • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w⁻¹ = ((((1 + ((u * l : ℕ) : ℤ) * b) ^ 2 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        ((((u * l : ℕ) : ℤ) ^ 2 * b - 2 * (1 + ((u * l : ℕ) : ℤ) * b) * ((u * l : ℕ) : ℤ) : ℤ) : ℂ) * θ := by
      rw [hNn, hwdef, inv_div]
      have : β u * βb u * (βb u / β u) = βb u * βb u := by field_simp [hβ0 u]
      rw [this, hβb]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  obtain ⟨hi1, hi2⟩ := comm_smul (S := S) (X := X) hw0 hN0 (stdLat_smul_idx _ m hN0) h1 h2 ha' hb'

  have hM : ∀ x ∈ X, (S.relIndex X) • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf X) ⟨x, hx⟩
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [AddSubgroup.relIndex] using this
  have hNl : ¬ l ∣ Nn := by
    intro hdiv
    have h1' : (l : ℤ) ∣ K u := by
      have := Int.natCast_dvd_natCast.2 hdiv
      rwa [hNnZ] at this
    have h2' : (l : ℤ) ∣ K u - 1 :=
      ⟨(u : ℤ) * (b + ((u * l : ℕ) : ℤ) * a * c), by rw [hKdef]; push_cast; ring⟩
    have h3 : (l : ℤ) ∣ 1 := by
      have := Int.dvd_sub h1' h2'
      simpa using this
    have h4 : (l : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
    exact hl.one_lt.ne' (by exact_mod_cast h4)
  have hln : ¬ l ∣ S.relIndex X * Nn := fun h => ((Nat.Prime.dvd_mul hl).1 h).elim hl1 hNl
  have hdvd := not_dvd_relIndex (A := S) (B := X.map (smulHom w)) (l := l) (n := S.relIndex X * Nn) hl hi1
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [smulHom_apply, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ Nn]
      exact hM _ (ha' x hx)) hln
  refine ⟨δ, hisoδ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hx0
    apply hu
    have hgx : (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • x := by
      rw [hδ] at hx
      calc (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • (w • g x) := by rw [inv_smul_smul₀ hw0]; rfl
        _ = w⁻¹ • x := by rw [hx]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
    first
      | exact Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
      | exact ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
  · unfold relIdx
    rw [himg]
    exact hi1
  · unfold relIdx
    rw [himg]
    exact hdvd
  · unfold relIdx
    rw [himg]
    exact hi2

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepBasic
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Form

variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]

theorem rep_H_apply (z w : m → ℂ) :
    stdH L m z w = ((area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem rep_H_conj (z w : m → ℂ) : conj (stdH L m z w) = stdH L m w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rep_H_apply, rep_H_apply, map_mul, map_sum]
  congr 1
  · simp [Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]

theorem rep_H_re (z : m → ℂ) : ((stdH L m z z).re : ℂ) = stdH L m z z :=
  Complex.conj_eq_iff_re.mp (rep_H_conj L m z z)

end Form

section Sat

variable {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ))

theorem rep_sat_of_mem {v : m → ℂ} (hv : v ∈ Λ) (hl : l.Prime) : SatMem l Λ v :=
  ⟨1, by simpa using hl.one_lt.ne' ∘ Nat.dvd_one.mp, by simpa using hv⟩

theorem rep_sat_add (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v + w) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨k, hk, hkw⟩ := hw
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (v + w) = k • (n • v) + n • (k • w) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply]; ring
  rw [e]
  exact Λ.add_mem (Λ.nsmul_mem hnv k) (Λ.nsmul_mem hkw n)

theorem rep_sat_neg {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (-v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  exact ⟨n, hn, by rw [smul_neg]; exact Λ.neg_mem hnv⟩

theorem rep_sat_sub (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v - w) := by
  rw [sub_eq_add_neg]; exact rep_sat_add l Λ hl hv (rep_sat_neg l Λ hw)

theorem rep_sat_ratN (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) (k : ℕ) (hk : ¬ l ∣ k) :
    SatMem l Λ (((r : ℂ) / k) • v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h; exact hk (by rw [Nat.cast_eq_zero.mp h]; exact dvd_zero _)
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (((r : ℂ) / k) • v) = r • (n • v) := by
    funext i; simp only [Pi.smul_apply, nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply, Pi.intCast_apply]; field_simp
  rw [e]
  exact Λ.zsmul_mem hnv _

theorem rep_sat_rat (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) (r s : ℤ) (hs : ¬ (l : ℤ) ∣ s) :
    SatMem l Λ (((r : ℂ) / s) • v) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · simpa using rep_sat_ratN l Λ hl hv r k (fun h => hs (Int.natCast_dvd_natCast.mpr h))
  · have := rep_sat_ratN l Λ hl hv (-r) k (fun h => hs (by simpa using Int.natCast_dvd_natCast.mpr h))
    convert this using 2
    push_cast; rw [div_neg, neg_div]

end Sat

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamDef
section
namespace PI.UnitaryGroupMassFormula.UnimodLocStd

def KeyStartRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → l = d → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SelfDualStd
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma stdH_apply (L : PeriodPair) (m : Type*) [Fintype m] [DecidableEq m] (x y : m → ℂ) :
    stdH L m x y = (∑ i, x i * conj (y i)) * ((area L : ℝ) : ℂ)⁻¹ := by
  simp only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def detD (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

private theorem detD_eq_re_mul_im_sub (L : PeriodPair) :
    detD L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma detD_ne (L : PeriodPair) : detD L ≠ 0 := by
  intro h
  have h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0 := by rw [← detD_eq_re_mul_im_sub]; exact h
  have hi := LinearIndependent.pair_iff.mp L.indep
  have key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    apply hi
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      linarith
  obtain ⟨e1, e2⟩ := key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)
  obtain ⟨f1, f2⟩ := key L.ω₂.re (-L.ω₁.re) (by ring)
    (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)
  exact one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2)
    (by linear_combination (-1 : ℝ) * e2)).1

lemma area_eq (L : PeriodPair) : area L = |detD L| := rfl

lemma im_mul_conj (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by
  rw [detD_eq_re_mul_im_sub]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]
  ring

lemma coords (L : PeriodPair) (z : ℂ) : ∃ s t : ℝ, z = s • L.ω₁ + t • L.ω₂ := by
  refine ⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩
  have h := L.basis.sum_repr z
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
  exact h.symm

lemma int_of_div (L : PeriodPair) {t : ℝ} {k : ℤ} (h : t * detD L / area L = k) : ∃ j : ℤ, t = j := by
  have hD := detD_ne L
  rw [area_eq] at h
  rcases abs_choice (detD L) with hA | hA
  · rw [hA, mul_div_assoc, div_self hD, mul_one] at h
    exact ⟨k, h⟩
  · rw [hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one] at h
    exact ⟨-k, by push_cast; linarith⟩

lemma lattice_iff (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [← h]
    simp [zsmul_eq_mul, Complex.real_smul]
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [h]
    simp [zsmul_eq_mul, Complex.real_smul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

