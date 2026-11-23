module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur
section
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {n : ℕ}

theorem prod_varL_eq_monomial (S : Finset (Fin n)) :
    ∏ k ∈ S, varL k = monomial (lamS S) := by
  have h : lamS S = ∑ k ∈ S, (Pi.single k 1 : Fin n → ℤ) := by
    funext x
    simp [lamS_apply, Finset.sum_apply, Pi.single_apply]
  rw [h]
  simp only [varL, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

theorem sum_esymmL_mul_pow (i : Fin n) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r * varL i ^ (n - r) = 0 := by
  have h0 : ∏ k : Fin n, (-varL k + varL i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Finset.prod_add, Finset.sum_powerset] at h0
  rw [← h0, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [esymmL, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [Finset.prod_neg, hc, prod_varL_eq_monomial, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, hc]

theorem altQuot_zero' : altQuot (0 : LaurentRing n) = 0 :=
  altQuot_eq_of_mul (by simp)

theorem sum_esymmL_mul_schur (hn : 0 < n) (j : ℤ) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) (j - (r : ℤ))) = 0 := by
  set i₀ : Fin n := ⟨0, hn⟩
  set P : LaurentRing n := monomial (Pi.single i₀ (j - (n : ℤ)) + staircase n) with hP
  have hterm : ∀ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single i₀ (j - (r : ℤ))) =
      altQuot ((-1) ^ r * esymmL n r * varL i₀ ^ (n - r) * P) := by
    intro r hr
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hsym : ∀ σ, permAct σ ((-1) ^ r * esymmL n r) = (-1) ^ r * esymmL n r := by
      intro σ
      rw [map_mul, map_pow, map_neg, map_one, permAct_esymmL]
    rw [mul_assoc ((-1) ^ r * esymmL n r), altQuot_mul_of_symm hsym, schur]
    congr 2
    rw [← monomial_single_natCast, hP, ← monomial_add, ← add_assoc, ← Pi.single_add]
    congr 3
    push_cast [Nat.cast_sub hr']
    ring
  rw [Finset.sum_congr rfl hterm, ← altQuot_sum, ← Finset.sum_mul, sum_esymmL_mul_pow, zero_mul,
    altQuot_zero']

theorem schur_single_eq_zero (hn : 0 < n) {m : ℤ} (h1 : 1 - (n : ℤ) ≤ m) (h2 : m ≤ -1) :
    schur (Pi.single (⟨0, hn⟩ : Fin n) m) = 0 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_zero]
  have hlt : (-m).toNat < n := by omega
  refine (alternant_eq_zero (i := (⟨0, hn⟩ : Fin n)) (j := ⟨(-m).toNat, hlt⟩) ?_ ?_).symm
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · have hne : (⟨(-m).toNat, hlt⟩ : Fin n) ≠ ⟨0, hn⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, staircase]
    have : (((-m).toNat : ℕ) : ℤ) = -m := by omega
    simp only [this]
    ring

theorem schur_zero_eq_one : schur (0 : Fin n → ℤ) = 1 :=
  altQuot_eq_of_mul (by rw [mul_one, zero_add]; rfl)

theorem sum_range_esymmL_mul_schur (hn : 0 < n) {j : ℕ} (hj : 1 ≤ j) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) ((j - r : ℕ) : ℤ)) = 0 := by
  set f : ℕ → LaurentRing n := fun r => (-1) ^ r * esymmL n r *
    schur (Pi.single (⟨0, hn⟩ : Fin n) ((j : ℤ) - (r : ℤ))) with hf
  have h1 : ∑ r ∈ Finset.range (j + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hjr : j < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    by_cases hrn : n < r
    · simp only [hf]
      rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
    · simp only [hf]
      rw [schur_single_eq_zero hn (by omega) (by omega), mul_zero]
  have h2 : ∑ r ∈ Finset.range (n + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hrn : n < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    simp only [hf]
    rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
  have h3 : ∑ r ∈ Finset.range (j + 1), f r = 0 := by
    rw [h1, ← h2]
    exact sum_esymmL_mul_schur hn (j : ℤ)
  rw [← h3]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  simp only [hf]
  rw [Nat.cast_sub hr']

theorem monomialChar_lamS (S : Finset (Fin n)) (z : Fin n → ℂˣ) :
    monomialChar (lamS S) z = ∏ i ∈ S, (z i : ℂ) := by
  rw [monomialChar_apply]
  have h : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1 := by
    intro i
    rw [lamS_apply]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem schur_row_recursion : L8 := by
  intro n hn z
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 : (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ) : Fin n → ℤ) = 0 := by
      simp
    rw [h0, schur_zero_eq_one, map_one]
  · have h := congrArg (evalAt z) (sum_range_esymmL_mul_schur hn hj)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, evalAt_esymmL,
      monomialChar_lamS] at h
    exact h

end GlobalTheory.CompanionTheory.SatakeBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
section
open PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.JSBound

theorem evalAt_esymmL_eq_sum_prod {n : ℕ} (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, (z i : ℂ) := by
  unfold esymmL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [evalAt, monomial, AddMonoidAlgebra.lift_single, one_smul, pointHom, monomialChar,
    MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, lamS]
  rw [← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem prod_one_add_mul_eq {n : ℕ} (w : Fin n → ℂ) (t : ℂ) :
    ∏ j, (1 + t * w j) = ∑ r ∈ Finset.range (n + 1),
      t ^ r * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, w i := by
  have h := Finset.prod_add (fun j => t * w j) (fun _ => (1 : ℂ)) (Finset.univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const] at h
  rw [show (∏ j, (1 + t * w j)) = ∏ j, (t * w j + 1) from Finset.prod_congr rfl fun _ _ => add_comm _ _, h,
    Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_powersetCard.1 hS).2]

theorem prod_add_eq {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    ∏ j, (t + z j) = ∑ r ∈ Finset.range (n + 1),
      t ^ (n - r) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i := by
  rw [show (∏ j, (t + z j)) = ∏ j, (z j + t) from Finset.prod_congr rfl fun _ _ => add_comm _ _,
    Finset.prod_add, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
    (Finset.mem_powersetCard.1 hS).2, mul_comm]

theorem mul_prod_one_add_conj_eq {n : ℕ} (z : Fin n → ℂˣ)
    (h : ∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) =
      evalAt z (esymmL n (n - r))) (t : ℂ) :
    evalAt z (esymmL n n) * ∏ j, (1 + t * starRingEnd ℂ (z j : ℂ)) = ∏ j, (t + (z j : ℂ)) := by
  simp only [evalAt_esymmL_eq_sum_prod] at h ⊢
  rw [prod_one_add_mul_eq, prod_add_eq, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have key := h r hrn
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod] at key
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hrn, ← key]
  ring

theorem symmetric_function_absolute_values : ParameterAbsoluteValues := by
  unfold ParameterAbsoluteValues
  intro n z h i
  have h0 := mul_prod_one_add_conj_eq z h 0
  have h1 := mul_prod_one_add_conj_eq z h (-(z i : ℂ))
  simp only [zero_mul, add_zero, zero_add, Finset.prod_const_one, mul_one] at h0
  have hne : evalAt z (esymmL n n) ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (z j).ne_zero
  have hz : ∏ j, (-(z i : ℂ) + z j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  rw [hz, mul_eq_zero] at h1
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_left hne)
  refine ⟨j, ?_⟩
  have hc : (z i : ℂ) * starRingEnd ℂ (z j : ℂ) = 1 := by linear_combination -hj
  have hn := congrArg norm hc
  rw [norm_mul, Complex.norm_conj, norm_one] at hn
  rw [mul_comm]
  exact hn

end GlobalTheory.CompanionTheory.JSBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoZeroOfSumSqLe
section
open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.Satake

theorem norm_sq_le_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u) (psd : ∀ u, 0 ≤ (B u u).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re :=
  _root_.UpperTheory.Reformulated.B.DYhd3.main B herm psd x y

theorem tendsto_zero_of_sum_sq_le (g : ℕ → ℂ) (D : ℝ)
    (hD : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ D) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hs : Summable fun j => ‖g j‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hD
  have h0 := hs.tendsto_atTop_zero
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun j => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem recursion_scaled {n : ℕ} (s : ℂ) (hs : s ≠ 0) (z : Fin n → ℂ) (h : ℕ → ℂ) (j : ℕ)
    (hrec : ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r) = 0) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = 0 := by
  have key : ∀ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = ((-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r)) / s ^ j := by
    intro r hr
    have hrj : r ≤ j := by simpa [Nat.lt_succ_iff] using hr
    have e1 : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) =
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) / s ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]
    have e2 : s ^ j = s ^ r * s ^ (j - r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, hrec, zero_div]

theorem bound_arith (r : ℝ) (hr : 0 < r) (m j : ℕ) (W H a b : ℝ)
    (hcs : (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 ≤ a * b) :
    W ^ 2 * (H / r ^ j) ^ 2 ≤ a * ((r ^ 2) ^ (j * m) * b) := by
  have hY : (r ^ 2) ^ (j * m) = (r ^ (j * m)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hXY : r ^ ((m + 1) * j) = r ^ j * r ^ (j * m) := by
    rw [← pow_add]
    congr 1
    ring
  have hX : r ^ j ≠ 0 := (pow_pos hr _).ne'
  have hYn : r ^ (j * m) ≠ 0 := (pow_pos hr _).ne'
  have e : W ^ 2 * (H / r ^ j) ^ 2 = (r ^ (j * m)) ^ 2 * (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 := by
    rw [hXY]
    field_simp
  rw [e, hY]
  calc _ ≤ (r ^ (j * m)) ^ 2 * (a * b) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by ring

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_zero_of_mem {g : GL (Fin n) F} (hg : g ∈ unipotent F n) : inU 0 g := by
  refine ⟨hg, fun i j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [hg.2 i, Matrix.one_apply_eq]
  · have hlt : j < i := by
      have : (j : ℕ) < i := by
        have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        omega
      exact this
    rw [hg.1 hlt, Matrix.one_apply_ne hij]

theorem antitone_single (hn : 0 < n) (j : ℕ) :
    Antitone (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) := by
  intro a b hab
  by_cases hb : b = ⟨0, hn⟩
  · have ha : a = ⟨0, hn⟩ := by
      subst hb
      exact Fin.ext (by have h : (a : ℕ) ≤ 0 := hab; show (a : ℕ) = 0; omega)
    rw [ha, hb]
  · by_cases ha : a = ⟨0, hn⟩
    · simp [ha, hb]
    · simp [ha, hb]

theorem rhoPair_single_zero (hn : 0 < n) (j : ℕ) :
    rhoPair (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) = ((n : ℤ) - 1) * j := by
  rw [rhoPair, Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

end

theorem l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound := by
  intro h6 h7 h8 h9
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm hn l B hW hU v z hH hg i
  obtain ⟨g₀, hg₀⟩ := hg
  have hlv : l v ≠ 0 := by
    intro h0
    apply hg₀
    rw [h7 F ψ hψ n V ρ v z hH l hW g₀, h0, zero_mul]
  obtain ⟨B', hI, hbd⟩ := h6 F μ ψ hψ n V ρ hsm l B hn hW hU
  obtain ⟨C, hC⟩ := hbd v hH.1
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set s := sqrtQ F with hsdef
  have hs : s ≠ 0 := sqrtQ_ne_zero
  set r := ‖s‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hs
  have hq : (qF F : ℝ) = r ^ 2 := by
    rw [hrdef, ← norm_pow, hsdef, sqrtQ_sq, Complex.norm_natCast]
  set w := B' v v with hwdef
  have hw : w ≠ 0 := fun h => hlv (hI.null v h)
  have hW' : Whit ρ ψ (B' v) := fun g hg u => hI.equi g (inU_zero_of_mem hg) u v
  let h : ℕ → ℂ := fun j => evalAt z (schur (Pi.single (⟨0, hn0⟩ : Fin (m + 2)) (j : ℤ)))
  let a : ℕ → GL (Fin (m + 2)) F := fun j => torusPow F (m + 2) (Pi.single ⟨0, hn0⟩ (j : ℤ))
  have hC' : ∀ T : ℕ, ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * m) *
      (B' (ρ (a j) v) (ρ (a j) v)).re ≤ C := hC
  have hval : ∀ j, B' v (ρ (a j) v) = w * ((s ^ ((m + 1) * j))⁻¹ * h j) := by
    intro j
    rw [h7 F ψ hψ (m + 2) V ρ v z hH (B' v) hW', sphericalWhittaker_torusPow hψ.1, if_pos (antitone_single hn0 j),
      halfModulus_eq, rhoPair_single_zero]
    congr 2
    rw [_root_.zpow_neg]
    congr 1
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  let g : ℕ → ℂ := fun j => h j / s ^ j
  have hterm : ∀ j, ‖w‖ ^ 2 * ‖g j‖ ^ 2 ≤
      w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) := by
    intro j
    have hcs := norm_sq_le_of_psd B' hI.herm hI.psd v (ρ (a j) v)
    rw [hval j, norm_mul, norm_mul, norm_inv, norm_pow] at hcs
    have := bound_arith r hr m j ‖w‖ ‖h j‖ w.re _ hcs
    rw [hq]
    simpa [g, norm_div, norm_pow] using this
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have hsum : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ w.re * C / ‖w‖ ^ 2 := by
    intro T
    rw [le_div_iff₀ hwpos, Finset.sum_mul]
    calc _ ≤ ∑ j ∈ Finset.range T,
          w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) :=
          Finset.sum_le_sum fun j _ => by rw [mul_comm]; exact hterm j
      _ = w.re * ∑ j ∈ Finset.range T,
          (qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re := by rw [Finset.mul_sum]
      _ ≤ w.re * C := mul_le_mul_of_nonneg_left (hC' T) (hI.psd v)
  have htend := tendsto_zero_of_sum_sq_le g _ hsum
  obtain ⟨h80, h8r⟩ := h8 (m + 2) hn0 z
  have hg0 : g 0 = 1 := by
    simpa [g, h] using h80
  have hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard r, ∏ i ∈ S, (z i : ℂ) / s) * g (j - r) = 0 :=
    fun j hj => recursion_scaled s hs (fun i => (z i : ℂ)) h j (h8r j hj)
  have hfin := h9 (m + 2) (fun i => (z i : ℂ) / s) g hg0 hrec htend i
  have hsq : Real.sqrt (qF F) = r := by rw [hq, Real.sqrt_sq hr.le]
  rw [hsq]
  rw [norm_div, div_lt_one hr] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.Satake
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFinite
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
end

