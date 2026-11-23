module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentity
section
open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertGenFun

theorem hasSum_counts (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by
  set y : ℂ := (q : ℂ) ^ (N + 1) * X with hy
  set F : ℕ → ℂ := fun j => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j with hF
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have hev : HasSum (fun m : ℕ => F (2 * m)) (c * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m)) = fun m => (c : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hodd : HasSum (fun m : ℕ => F (2 * m + 1)) (c * q * X * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m + 1)) = fun m => (c * q * X : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [show (2 * m + 1) / 2 = m by omega, hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hne : (1 : ℂ) - y ^ 2 ≠ 0 := by
    intro h0
    have : ‖y ^ 2‖ = 1 := by
      rw [show y ^ 2 = 1 by linear_combination -h0]
      simp
    linarith
  have hval : (c : ℂ) * (1 + q * X) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * X * (1 - y ^ 2)⁻¹ := by
    field_simp
  rw [hval]
  exact HasSum.even_add_odd hev hodd

theorem hasSum_of_counts {ι : Type} (g : ι → ℕ) (A : ℕ → ℕ) (hA : ∀ j, A j ≠ 0)
    (hc : ∀ j, Nat.card {i // g i ≤ j} = A j) (X s : ℂ)
    (hT : HasSum (fun j : ℕ => (A j : ℂ) * X ^ j) s) :
    HasSum (fun i => X ^ g i) ((1 - X) * s) := by
  have hfinle : ∀ j, Finite {i // g i ≤ j} := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; exact hA j)
  have hfin : ∀ j, Finite {i // g i = j} := fun j =>
    Finite.of_injective (fun c : {i // g i = j} => (⟨c.1, c.2.le⟩ : {i // g i ≤ j}))
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hcard : ∀ j, Nat.card {i // g i = j} + (if j = 0 then 0 else A (j - 1)) = A j := by
    intro j
    rcases j with _ | k
    · simp only [if_true, add_zero, ← hc 0]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by omega))
    · have : ∀ i, g i ≤ k + 1 ↔ g i ≤ k ∨ g i = k + 1 := fun i => by omega
      have e := (Equiv.subtypeEquivRight this).trans
        (subtypeOrEquiv (fun i => g i ≤ k) (fun i => g i = k + 1)
          (Pi.disjoint_iff.2 fun i => Prop.disjoint_iff.2 (by omega)))
      rw [← hc (k + 1), Nat.card_congr e, Nat.card_sum, if_neg (Nat.succ_ne_zero k),
        Nat.add_sub_cancel, ← hc k, add_comm]
  have hfib : ∀ (j : ℕ) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (F : ℕ → M),
      HasSum (fun c : {i // g i = j} => F (g c)) (Nat.card {i // g i = j} • F j) := by
    intro j M _ _ F
    have := hfin j
    have : Fintype {i // g i = j} := Fintype.ofFinite _
    convert hasSum_fintype (fun c : {i // g i = j} => F (g c)) using 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hle : ∀ j, Nat.card {i // g i = j} ≤ A j := fun j => by
    have := hcard j
    omega
  have hnorm : Summable (fun j : ℕ => (A j : ℝ) * ‖X‖ ^ j) := by
    have := hT.summable.norm
    simpa [norm_mul, norm_pow] using this
  have hsum : Summable (fun i => X ^ g i) := by
    apply Summable.of_norm
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    show Summable fun p : (Σ j : ℕ, {i // g i = j}) => ‖X ^ g (p.2 : ι)‖
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (hfib j (fun n => ‖X ^ n‖)).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) hnorm
    have h1 := (hfib j (fun n => ‖X ^ n‖)).tsum_eq
    rw [h1, nsmul_eq_mul, norm_pow]
    gcongr
    exact_mod_cast hle j
  obtain ⟨t, ht⟩ := hsum
  have hsig := ((Equiv.sigmaFiberEquiv g).hasSum_iff.2 ht).sigma
    (fun j => hfib j (fun n => X ^ n))
  have hshift : HasSum (fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) (s * X) := by
    have h0 : HasSum (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1))
        (s * X) := by
      have hfun : (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1)) =
          fun n => (A n : ℂ) * X ^ n * X := by
        funext n
        rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
        ring
      rw [hfun]
      exact hT.mul_right X
    have h1 := (hasSum_nat_add_iff
      (f := fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) 1).1 h0
    simp only [Finset.sum_range_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h1
    exact h1
  have hdiff := hT.sub hshift
  have heq : (fun j : ℕ => (A j : ℂ) * X ^ j - ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) =
      fun j => Nat.card {i // g i = j} • X ^ j := by
    funext j
    rw [nsmul_eq_mul, ← hcard j]
    push_cast
    ring
  rw [heq] at hdiff
  have := hsig.unique hdiff
  rw [this] at ht
  rwa [show (1 - X) * s = s - s * X by ring]

theorem genFun : GenFun := by
  intro ι f l c q N X hc hq hf hcount hX
  have hA : ∀ j, c * q ^ (2 * N * (j / 2) + j) ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hcg : ∀ j, Nat.card {i // f i - l ≤ j} = c * q ^ (2 * N * (j / 2) + j) := by
    intro j
    rw [← hcount j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by have := hf i; omega))
  have h := hasSum_of_counts (fun i => f i - l) (fun j => c * q ^ (2 * N * (j / 2) + j)) hA hcg X _
    (hasSum_counts q N c X hX)
  have key : (fun i => X ^ f i) = fun i => X ^ l * X ^ (f i - l) := by
    funext i
    rw [← pow_add]
    congr 1
    have := hf i
    omega
  rw [key, show (c : ℂ) * X ^ l * jFac q N X =
    X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
  exact h.mul_left _

end GlobalTheory.CompanionTheory.InertGenFun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmith
section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex

noncomputable section

namespace GlobalTheory.CompanionTheory.InertIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def boxLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → ℤ) :
    AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun i => ordBall L (c i)

theorem mem_boxLat {c : Fin n → ℤ} {x : Fin n → L} : x ∈ boxLat L c ↔ ∀ i, x i ∈ ordBall L (c i) := by
  simp [boxLat, AddSubgroup.mem_pi]

theorem relIndex_boxLat (c C : Fin n → ℤ) :
    (boxLat L C).relIndex (boxLat L c) = ∏ i, (ordBall L (C i)).relIndex (ordBall L (c i)) := by
  let f : boxLat L c →+ (∀ i, ordBall L (c i) ⧸ (ordBall L (C i)).addSubgroupOf (ordBall L (c i))) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, mem_boxLat.1 x.2 i⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i => ((y i).out : L), mem_boxLat.2 fun i => (y i).out.2⟩, funext fun i => ?_⟩
    exact (y i).out_eq
  have hc : (boxLat L C).addSubgroupOf (boxLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_boxLat]
    constructor
    · intro h i
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i)
    · intro h i
      exact AddSubgroup.mem_addSubgroupOf.1
        ((QuotientAddGroup.eq_zero_iff (⟨x.1 i, mem_boxLat.1 x.2 i⟩ : ordBall L (c i))).1 (h i))
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem mem_intL_iff {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem vecMul_mem_intV {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) {r : Fin n → L} (hr : r ∈ intV L n) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  change ∑ i, r i * M i j ∈ intL L
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp

theorem mem_preLat_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {d : Fin n → ℤ}
    {a b b' : Matrix (Fin n) (Fin n) L} (hb : IsInt b) (hb' : IsInt b') (eb : b * b' = 1) (r : Fin n → L) :
    r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔ r ᵥ* a ∈ boxLat L (fun i => -d i) := by
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have key : ∀ s : Fin n → L, s ᵥ* Matrix.diagonal (fun i => ϖ ^ d i) ∈ intV L n ↔
      s ∈ boxLat L (fun i => -d i) := fun s => by
    rw [mem_intV, mem_boxLat]
    refine forall_congr' fun i => ?_
    rw [Matrix.vecMul_diagonal, mem_intL_iff, mem_ordBall, map_mul, v_zpow hϖ, neg_neg]
    have e : WithZero.exp (d i) = 1 * (WithZero.exp (-d i))⁻¹ := by rw [WithZero.exp_neg, inv_inv, one_mul]
    rw [e, le_mul_inv_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
  have hr : r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔
      r ᵥ* (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ∈ intV L n := by
    rw [mem_preLat, mem_intV]
  rw [hr, ← key, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  refine ⟨fun h => ?_, fun h => vecMul_mem_intV hb h⟩
  have := vecMul_mem_intV hb' h
  rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this

theorem latIndex (hS : Smith) : LatIndex := by
  intro L _ _ ϖ σ q n hU A k hA hk
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hdet : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hk; exact WithZero.exp_ne_zero hk.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, hAe⟩ := hS L ϖ n hϖ A hdet
  have ea' : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb' : b' * b = 1 := mul_eq_one_comm.1 eb
  have hDe : Matrix.diagonal (fun i => ϖ ^ d i) = a' * A * b' := by
    rw [hAe]
    calc _ = (a' * a) * Matrix.diagonal (fun i => ϖ ^ d i) * (b * b') := by rw [ea, eb]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hD : IsInt (Matrix.diagonal (fun i => ϖ ^ d i)) := hDe ▸ (ha'.mul hA).mul hb'
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hD i i
    rw [Matrix.diagonal_apply_eq, mem_intL_iff, v_zpow hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hprod : ∀ s : Finset (Fin n), ∏ i ∈ s, WithZero.exp (-(d i)) =
      (WithZero.exp (-∑ i ∈ s, d i) : WithZero (Multiplicative ℤ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← WithZero.exp_add, neg_add]
  have hsum : ∑ i, d i = k := by
    have h := hk
    rw [hAe, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, v_det_eq_one ha ha' ea', v_det_eq_one hb hb' eb,
      Matrix.det_diagonal, map_prod, one_mul, mul_one, Finset.prod_congr rfl fun i _ => v_zpow hϖ (d i), hprod,
      WithZero.exp_inj] at h
    omega
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hfa : ∀ r, f r = r ᵥ* a := fun _ => rfl
  have hf : Function.Surjective f := fun s => ⟨s ᵥ* a', by
    rw [hfa, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : intV L n = (boxLat L fun _ => 0).comap f := by
    ext r
    have e : ∀ x : Fin n → L, x ∈ boxLat L (fun _ => 0) ↔ x ∈ intV L n := fun x => by
      rw [mem_boxLat, mem_intV]
      refine forall_congr' fun i => ?_
      rw [mem_ordBall, mem_intL_iff, neg_zero, WithZero.exp_zero]
    rw [AddSubgroup.mem_comap, e, hfa]
    refine ⟨fun h => vecMul_mem_intV ha h, fun h => ?_⟩
    have := vecMul_mem_intV ha' h
    rwa [Matrix.vecMul_vecMul, ea', Matrix.vecMul_one] at this
  have h2 : preLat A = (boxLat L fun i => -d i).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hfa, hAe]
    exact mem_preLat_iff hϖ hb hb' eb r
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf, relIndex_boxLat,
    Finset.prod_congr rfl fun i _ => relIndex_ordBall hU (k := -d i) (K := 0) (by linarith [hd i]),
    Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 2
  have : ((∑ i, (0 - -d i).toNat : ℕ) : ℤ) = k := by
    rw [Nat.cast_sum, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (by linarith [hd i])]
    ring
  exact_mod_cast this

end GlobalTheory.CompanionTheory.InertIndex

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.LeviDecompositionExists
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLevi

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def edge (c d : L) (f : Fin N → L) : Fin (N + 2) → L := Fin.cons c (Fin.snoc f d : Fin (N + 1) → L)

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_zero (c d : L) (f : Fin N → L) : edge c d f 0 = c := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_mid (c d : L) (f : Fin N → L) (j : Fin N) : edge c d f (mid j) = f j := by
  simp [edge, mid]

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_last (c d : L) (f : Fin N → L) : edge c d f (Fin.last (N + 1)) = d := by
  rw [edge, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

def blkMat (x y : L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  fun i j => edge (edge x 0 (fun _ => 0) j) (edge 0 y (fun _ => 0) j) (fun p => edge 0 0 (A p) j) i

theorem gram_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ k, σ (M k i) * M k.rev j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.rev]
  · rw [if_pos (by have := k.isLt; simp only [Fin.val_rev]; omega), mul_one]
  · intro l _ hl
    rw [if_neg, mul_zero, zero_mul]
    intro h
    apply hl
    ext
    have := k.isLt
    have := l.isLt
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blkMat_gram {x y : L} (hxy : σ x * y = 1) (hyx : σ y * x = 1) {A : Matrix (Fin N) (Fin N) L}
    (hA : cT σ A * antiJ L N * A = antiJ L N) :
    cT σ (blkMat x y A) * antiJ L (N + 2) * blkMat x y A = antiJ L (N + 2) := by
  ext i j
  rw [gram_apply, sum_idx]
  simp only [Fin.rev_last, ← mid_rev, Fin.rev_zero]
  rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl
  · simp [blkMat, antiJ]
  · simp [blkMat, antiJ, val_mid, s.isLt.ne]
  · simp [blkMat, antiJ, hxy]
  · simp [blkMat, antiJ, val_mid, r.isLt.ne]
  · have h := congrFun (congrFun hA r) s
    rw [gram_apply] at h
    simp only [blkMat, edge_zero, edge_mid, edge_last, map_zero, zero_mul, mul_zero, zero_add, add_zero]
    rw [h]
    simp only [antiJ]
    have e1 := val_mid r
    have e2 := val_mid s
    by_cases h1 : (r : ℕ) + s + 1 = N
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ, hyx]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ]

theorem leviExists : LeviExists := by
  intro L _ _ ϖ σ q N hU a g₀
  obtain ⟨_, _, hσϖ, hvϖ, _⟩ := hU
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hvϖ
  have hσx : σ (ϖ ^ a) = ϖ ^ a := by rw [map_zpow₀, hσϖ]
  have hσy : σ (ϖ ^ (-a)) = ϖ ^ (-a) := by rw [map_zpow₀, hσϖ]
  have hxy : σ (ϖ ^ a) * ϖ ^ (-a) = 1 := by rw [hσx, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyx : σ (ϖ ^ (-a)) * ϖ ^ a = 1 := by rw [hσy, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero]
  have hA : cT σ (mat g₀) * antiJ L N * mat g₀ = antiJ L N := g₀.2
  have hJJ : antiJ L (N + 2) * antiJ L (N + 2) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, antiJ, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    have hi := i.isLt
    have hj := j.isLt
    rw [Finset.sum_eq_single i.rev]
    · rw [if_pos (by simp only [Fin.val_rev]; omega)]
      by_cases h : i = j
      · subst h
        rw [if_pos (by simp only [Fin.val_rev]; omega), if_pos rfl]
      · rw [if_neg (by simp only [Fin.val_rev]; intro h'; apply h; ext; omega), if_neg h]
    · intro l _ hl
      rw [if_neg]
      intro h'
      apply hl
      ext
      have := l.isLt
      simp only [Fin.val_rev]
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := blkMat (ϖ ^ a) (ϖ ^ (-a)) (mat g₀) with hB
  have hG : cT σ B * antiJ L (N + 2) * B = antiJ L (N + 2) := blkMat_gram hxy hyx hA
  have hCB : antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B = 1 := by
    calc antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B
        = antiJ L (N + 2) * (cT σ B * antiJ L (N + 2) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, hJJ]
  have hBC : B * (antiJ L (N + 2) * cT σ B * antiJ L (N + 2)) = 1 := mul_eq_one_comm.mp hCB
  let U : GL (Fin (N + 2)) L := ⟨B, antiJ L (N + 2) * cT σ B * antiJ L (N + 2), hBC, hCB⟩
  have hU : U ∈ GU σ (N + 2) := hG
  refine ⟨⟨U, hU⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    show B i j = 0
    rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl <;>
      simp [hB, blkMat, blk_zero, blk_mid, blk_last] at hij ⊢
  · show B 0 0 = ϖ ^ a
    simp [hB, blkMat]
  · show B (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a)
    simp [hB, blkMat]
  · intro i j
    show B (mid i) (mid j) = mat g₀ i j
    simp [hB, blkMat]

end GlobalTheory.CompanionTheory.InertLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
section
open Formalism.UG GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

private theorem mem_range_bc_of_entries_mem_intL {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    (g : GL (Fin n) L) (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) :
    g ∈ (Formalism.UG.bc (Formalism.UG.intL L).subtype).range := by
  let M : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h2 i j⟩
  have hM : (Formalism.UG.intL L).subtype.mapMatrix M = g := by ext i j; rfl
  have hM' : (Formalism.UG.intL L).subtype.mapMatrix M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective
      ((Formalism.UG.intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) :=
    fun A B h => Matrix.ext fun i j => Subtype.ext (by simpa [RingHom.mapMatrix_apply] using congrFun (congrFun h i) j)
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext hM⟩
  · rw [map_mul, map_one, hM, hM']
    exact g.mul_inv
  · rw [map_mul, map_one, hM, hM']
    exact g.inv_mul

private theorem entry_lemma_2 {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
    (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : Formalism.UG.GU σ 1) (i j : Fin 1) :
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) i j ∈ Formalism.UG.intL L := by
  have hg : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * Formalism.UG.antiJ L 1 *
      ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = Formalism.UG.antiJ L 1 := g.2
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  set x := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0 with hx
  have e : σ x * x = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.antiJ, hx] using this
  have e2 : Valued.v x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hv x]
    rw [← map_mul, e, map_one]
  refine (Valuation.mem_integer_iff _ _).mpr ?_
  exact (pow_le_one_iff two_ne_zero).mp e2.le

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hσ hn g
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  interval_cases n
  · exact mem_range_bc_of_entries_mem_intL _ (fun i => i.elim0) (fun i => i.elim0)
  · exact mem_range_bc_of_entries_mem_intL _ (entry_lemma_2 hσ.2.1 g) (entry_lemma_2 hσ.2.1 g⁻¹)

end GlobalTheory.CompanionTheory.InertZeta
end

