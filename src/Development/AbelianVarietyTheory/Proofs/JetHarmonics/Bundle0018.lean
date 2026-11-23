module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPosZsmulMemRange
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem quad_add_zsmul (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by
  have h1 := hQ (y + t • w)
  have h2 := hQ y
  have h3 := hQ w
  have h4 := hs w y
  simp only [map_add (f := _), map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1
  have h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w) := by
    linear_combination h1 - h2 + t * h4 - t ^ 2 * h3
  exact mul_left_cancel₀ two_ne_zero h5

theorem quad_zero (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero] at h
  omega

theorem quad_nonneg (hQ : ∀ x, 2 * Q x = Bf x x) (hp : ∀ x, x ≠ 0 → 1 ≤ Q x) (x : X) :
    0 ≤ Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact (quad_zero hQ).ge
  · exact le_trans zero_le_one (hp x hx)

private lemma exists_int_shift_within_bounds (q B N a : ℤ) (hq : 0 < q) (hN : 0 < N) :
    ∃ m : ℤ, -(N * q) ≤ 2 * q * (a + N * m) + B ∧ 2 * q * (a + N * m) + B ≤ N * q := by
  have hD : 0 < 2 * q * N := by positivity
  have h1 := Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)
  have h2 := Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'
  have h3 := Int.emod_lt_of_pos (2 * q * a + B + N * q) hD
  refine ⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩
  · linarith
  · linarith

theorem quad_round_step (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (hw : 0 ≤ Q w) (N : ℤ) (hN : 0 < N) (a : ℤ) :
    ∃ m : ℤ, 4 * Q (y + (a + N * m) • w) ≤ 4 * Q y + N ^ 2 * Q w := by
  have key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w :=
    fun t => quad_add_zsmul hs hQ y w t
  rcases hw.lt_or_eq with hq | hq
  · obtain ⟨m, hm1, hm2⟩ := exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN
    refine ⟨m, ?_⟩
    rw [key]
    set t := a + N * m
    have hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2 := by
      nlinarith
    have hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w) := by
      nlinarith [sq_nonneg (Bf y w)]
    have := le_of_mul_le_mul_left hmul hq
    linarith
  · by_cases hB : 0 ≤ Bf y w
    · refine ⟨-|a|, ?_⟩
      rw [key, ← hq]
      have h1 : a + N * -|a| ≤ 0 := by
        nlinarith [le_abs_self a, abs_nonneg a]
      nlinarith
    · refine ⟨|a|, ?_⟩
      rw [key, ← hq]
      have h1 : 0 ≤ a + N * |a| := by
        nlinarith [neg_abs_le a, abs_nonneg a]
      nlinarith

theorem quad_round_sum (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    {ι : Type} [DecidableEq ι] (v : ι → X) (hv : ∀ j, 0 ≤ Q (v j)) (N : ℤ) (hN : 0 < N)
    (a : ι → ℤ) (s : Finset ι) :
    ∃ m : ι → ℤ, 4 * Q (∑ j ∈ s, (a j + N * m j) • v j) ≤ N ^ 2 * ∑ j ∈ s, Q (v j) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [quad_zero hQ]⟩
  | insert i s hi ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m0, h0⟩ :=
      quad_round_step hs hQ (∑ j ∈ s, (a j + N * m j) • v j) (v i) (hv i) N hN (a i)
    refine ⟨Function.update m i m0, ?_⟩
    have hs' : ∑ j ∈ s, (a j + N * Function.update m i m0 j) • v j
        = ∑ j ∈ s, (a j + N * m j) • v j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hs', Function.update_self, add_comm]
    nlinarith

theorem exists_pos_zsmul_mem_range {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (φ : X →+ X)
    (hφ : Function.Injective φ) (x : X) : ∃ N : ℤ, 0 < N ∧ ∃ y, φ y = N • x := by
  have : Module.Free ℤ X := Module.Free.of_basis b
  have : Module.Finite ℤ X := Module.Finite.of_basis b
  set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf
  set M := LinearMap.toMatrix b b f
  have hinj : Function.Injective f := by
    simpa [hf, AddMonoidHom.coe_toIntLinearMap] using hφ
  have hdet : M.det ≠ 0 := by
    intro h
    rw [LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (LinearMap.ker_eq_bot.mpr hinj)
  have e : Matrix.toLin b b M = f := Matrix.toLin_toMatrix b b f
  have key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id := by
    calc f.comp (Matrix.toLin b b M.adjugate)
        = (Matrix.toLin b b M).comp (Matrix.toLin b b M.adjugate) := by rw [e]
      _ = Matrix.toLin b b (M * M.adjugate) := (Matrix.toLin_mul b b b M M.adjugate).symm
      _ = M.det • LinearMap.id := by rw [Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
  refine ⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩
  have hx : f (Matrix.toLin b b M.adjugate x) = M.det • x := by
    have := congrArg (fun g => g x) key
    simpa using this
  have : φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x) := by
    rw [map_zsmul]; rfl
  rw [this, hx, smul_smul]

end CosetMin

theorem exists_coset_minimiser :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by
  classical
  intro X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x
  have hQφ : ∀ z, Q (φ z) = g * Q z := by
    intro z
    have h : 2 * Q (φ z) = 2 * (g * Q z) := by
      rw [hQ, hφ, ← hQ z]; ring
    exact mul_left_cancel₀ two_ne_zero h
  have hinj : Function.Injective φ := by
    intro u v huv
    by_contra hne
    have h0 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hp (u - v) (sub_ne_zero.mpr hne)
    have h2 := hQφ (u - v)
    rw [h0, quad_zero hQ] at h2
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith
  obtain ⟨N, hN, y, hy⟩ := exists_pos_zsmul_mem_range b φ hinj x
  obtain ⟨m, hm⟩ := quad_round_sum hs hQ (fun j => φ (b j))
    (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ
  set χ0 : X := ∑ j, m j • b j with hχ0
  have hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j) := by
    have hyφ : φ y = ∑ j, b.repr y j • φ (b j) := by
      calc φ y = φ (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr y j • φ (b j) := by rw [map_sum]; simp only [map_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, add_smul]
  have hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z := by
    intro z
    have := quad_add_zsmul hs hQ 0 z N
    simp only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this
    linarith
  have hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j) := by
    have h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j)) := by
      rw [hNx]; exact hm
    rw [hsc] at h1
    simp only [hQφ, ← Finset.mul_sum] at h1
    have hN2 : 0 < N ^ 2 := by positivity
    have h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j)) := by linarith
    exact le_of_mul_le_mul_left h2 hN2
  have hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k :=
    ⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩
  obtain ⟨χ, hχ⟩ := Nat.find_spec hex
  have hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ') := by
    intro χ'
    rw [hχ]
    have := Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩
    calc (Nat.find hex : ℤ) ≤ ((Q (x + φ χ')).toNat : ℤ) := by exact_mod_cast this
      _ = Q (x + φ χ') := Int.toNat_of_nonneg (quad_nonneg hQ hp _)
  refine ⟨χ, ?_, ?_⟩
  · have h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j) := by linarith [hmin χ0]
    have h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc := by
      calc (∑ j, (Q (b j) : ℝ)) ≤ ∑ _j : Fin n, Cc := Finset.sum_le_sum fun j _ => hC j
        _ = n * Cc := by simp
    have h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ) := by exact_mod_cast h1
    have hg' : (0 : ℝ) ≤ g := by positivity
    nlinarith
  · intro q z
    have hz := hmin (χ + z)
    rw [map_add (f := _), ← add_assoc] at hz
    have e1 := quad_add_zsmul hs hQ (x + φ χ) (φ z) 1
    have e2 := quad_add_zsmul hs hQ (x + φ χ) (φ z) q
    rw [one_smul] at e1
    rw [natCast_zsmul] at e2
    rw [e2]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory


open MvPowerSeries in
theorem _root_.GlobalTheory.minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hj : j = n <;> by_cases hi : i = n <;>
      simp [Pi.single_apply, hj, hi]
  have := DFunLike.congr_fun h p
  rw [Derivation.commutator_apply] at this
  simpa [sub_eq_zero] using this


open MvPowerSeries in
theorem _root_.GlobalTheory.minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp

open MvPowerSeries in
private theorem pderiv_mem_supported' {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) (w : σ) :
    MvPolynomial.pderiv w p ∈ MvPolynomial.supported k S := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [MvPolynomial.pderiv_X]
    by_cases h : w = s
    · subst h; simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne' h]; exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)


open MvPowerSeries in
theorem _root_.GlobalTheory.minors_disjoint_columns_harmonic :
    ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → ∀ τ τ' : T, (∀ i i', col τ i ≠ col τ' i') → ∀ (i : Fin (r τ)) (i' : Fin (r τ')), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) (MvPolynomial.pderiv ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), b) P) = 0 := by
  intro k _ T _ _ r n col m P hP τ τ' hdisj i i'
  let S : Set ((Σ τ : T, Fin (r τ)) × Fin n) := {x | ∃ c, col x.1.1 c = x.2}
  have hPS : P ∈ MvPolynomial.supported k S := by
    rw [hP]
    refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_
    refine Subalgebra.pow_mem _ ?_ _
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _
    rw [Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : ∃ c, col τ c = b
  · obtain ⟨c, rfl⟩ := hb
    have hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S := by
      rintro ⟨c', hc'⟩
      exact hdisj c c' hc'.symm
    rw [_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]
  · have hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S := hb
    exact _root_.GlobalTheory.minorHarm_pderiv_eq_zero
      (pderiv_mem_supported' hPS _) hnot

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstIsRingHomOnBounded
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ τ : Type}
  [Fintype σ] {s : σ → MvPowerSeries τ K}

theorem csub_add_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S + T) = csub s S + csub s T := by
  ext μ
  have h1 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).1).1 μ
  rw [map_add (f := _)]
  refine h3.unique ?_
  simpa only [map_add (f := _), add_mul] using h1.add h2

theorem csub_sub_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S - T) = csub s S - csub s T := by
  ext μ
  have h1 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.1).1 μ
  rw [map_sub]
  refine h3.unique ?_
  simpa only [map_sub, sub_mul] using h1.sub h2

theorem csub_mul_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S * T) = csub s S * csub s T := by
  classical
  ext μ
  have h3 := (_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.2).1 μ
  refine h3.unique ?_
  haveI : NonarchimedeanRing K := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  have h4 : HasSum (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      MvPowerSeries.coeff p.1 S * MvPowerSeries.coeff p.2 T *
        MvPowerSeries.coeff μ (∏ i, s i ^ (p.1 + p.2) i))
      (MvPowerSeries.coeff μ (csub s S * csub s T)) := by
    rw [MvPowerSeries.coeff_mul]
    have h5 := hasSum_sum (s := Finset.HasAntidiagonal.antidiagonal μ) (fun q _ =>
      ((_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s S hs hS).1 q.1).mul_of_nonarchimedean
        ((_root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ s T hs hT).1 q.2))
    convert h5 using 2 with p
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, MvPowerSeries.coeff_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h6 := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 h4
  refine h6.sigma fun ν => ?_
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul, ← Finset.sum_coe_sort]
  convert hasSum_fintype _ using 2 with q
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 q.2
  simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, this]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_monomial (s : σ → MvPowerSeries τ K) (ν : σ →₀ ℕ) (a : K) :
    csub s (MvPowerSeries.monomial ν a) = MvPowerSeries.C a * ∏ i, s i ^ ν i := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_C_mul]
  change ∑' ν' : σ →₀ ℕ, MvPowerSeries.coeff ν' (MvPowerSeries.monomial ν a) *
    MvPowerSeries.coeff μ (∏ i, s i ^ ν' i) = _
  rw [tsum_eq_single ν]
  · rw [MvPowerSeries.coeff_monomial_same]
  · intro b hb
    rw [MvPowerSeries.coeff_monomial_ne hb, zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_C (s : σ → MvPowerSeries τ K) (a : K) :
    csub s (MvPowerSeries.C a) = MvPowerSeries.C a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, csub_monomial]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_X (s : σ → MvPowerSeries τ K) (i : σ) :
    csub s (MvPowerSeries.X i) = s i := by
  classical
  rw [MvPowerSeries.X_def, csub_monomial, map_one, one_mul, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, pow_zero]
  · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_one (s : σ → MvPowerSeries τ K) : csub s 1 = 1 := by
  simpa using csub_C s (1 : K)

theorem csub_pow_of_bdd (hs : ∀ i, Small (s i)) {S : MvPowerSeries σ K} (hS : Bdd S) (n : ℕ) :
    csub s (S ^ n) = csub s S ^ n := by
  induction n with
  | zero => simpa using csub_one s
  | succ n ih =>
    rw [pow_succ, pow_succ, csub_mul_of_bdd hs (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.1 S n).2.1 hS) hS, ih]

theorem csub_prod_of_bdd (hs : ∀ i, Small (s i)) {ι : Type} (t : Finset ι)
    (f : ι → MvPowerSeries σ K) (hf : ∀ i ∈ t, Bdd (f i)) :
    csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using csub_one s
  | insert a t ha ih =>
    have ht : ∀ i ∈ t, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      csub_mul_of_bdd hs (hf a (Finset.mem_insert_self a t))
        (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.1 ι t f).2 ht).1, ih ht]

theorem csub_eval₂_of_bdd (hs : ∀ i, Small (s i)) {k ι : Type} [CommRing k] (φ : k →+* K)
    (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k) (ha : ∀ j, Bdd (a j)) :
    csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) =
      MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ)
        (fun j => csub s (a j)) A := by
  have hb := fun B => (GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.2.2.2.1 k ι φ a B ha
  induction A using MvPolynomial.induction_on with
  | C c => simp [csub_C]
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, csub_add_of_bdd hs (hb p) (hb q), hp, hq]
  | mul_X p j hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
      csub_mul_of_bdd hs (hb p) (ha j), hp]

end

theorem csub_ring_map : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  intro K _ _ _ σ τ _ s hs
  exact ⟨fun S T hS hT => ⟨csub_add_of_bdd hs hS hT, csub_sub_of_bdd hs hS hT,
      csub_mul_of_bdd hs hS hT⟩, csub_C s, csub_X s, fun S n hS => csub_pow_of_bdd hs hS n,
    fun ι t f hf => csub_prod_of_bdd hs t f hf,
    fun k ι _ φ a A ha => csub_eval₂_of_bdd hs φ a A ha⟩

end GlobalTheory.ConvSer
end

