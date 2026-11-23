module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.PhiOnto
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Formalism.CoboundaryTransfers

theorem phi_map_surjective : StatPhiOnto := by
  intro O A _ _ _ B M D _ _ _ _ W I _ k b hk hMb hQI hφI n hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ : ∃ d, k * b = M + 1 + d := ⟨k * b - (M + 1), by omega⟩

  have hmem : ∀ x : W.N, (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)) ∈ W.N :=
    fun x => W.N.smul_mem _ (W.φ_N x x.2)
  let g : W.N →+ W.N :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hg : ∀ x : W.N, W.φ (B.X ^ b • (x : D)) = B.X ^ b • ((g x : W.N) : D) := by
    intro x
    show _ = B.X ^ b • ((B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)))
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, hd]
    ring
  have hφpow : ∀ (j : ℕ) (r : A), r ∈ I ^ j → B.φ r ∈ I ^ j := by
    intro j r hr
    have h1 : Ideal.map (B.φ : A →+* A) I ≤ I :=
      Ideal.map_le_iff_le_comap.2 (fun a ha => hφI a ha)
    have h2 : (B.φ : A →+* A) r ∈ Ideal.map (B.φ : A →+* A) (I ^ j) := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 j h2
  have hcontr : ∀ j : ℕ, ∀ x ∈ (I ^ j • ⊤ : Submodule A W.N), g x ∈ (I ^ (j + 1) • ⊤ : Submodule A W.N) := by
    intro j x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      have e : g (r • m) = (B.φ r * B.Q) •
          (⟨(B.Q ^ d * v ^ b) • (B.Q ^ M • W.φ (m : D)), W.N.smul_mem _ (W.φ_N m m.2)⟩ : W.N) := by
        ext
        show (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (r • (m : D))) = _
        rw [W.φ_smul]
        simp only [SetLike.mk_smul_mk, smul_smul]
        congr 1
        ring
      rw [e]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hφpow j r hr) hQI
    · intro x y hx hy
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  have hbij := _root_.subIdBijectiveOfContracting_holds A W.N I g hcontr
  obtain ⟨z, hz⟩ := hbij.2 (-(⟨n, hn⟩ : W.N))
  refine ⟨z, z.2, ?_⟩
  rw [hg z, ← smul_sub]
  congr 1
  have : ((g z - z : W.N) : D) = -n := by
    have := congrArg (fun t : W.N => (t : D)) hz
    simpa using this
  have h3 : ((g z : W.N) : D) - (z : D) = -n := by simpa using this
  rw [← neg_sub, h3, neg_neg]

end Formalism.RepresentationBoundsCohomology.N2
end
end

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueSeriesExpansionHolds
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

section Weight

variable {A : Type} [CommRing A]

def wI (L Q : A) (W e : ℕ) : Ideal A :=
  Ideal.span {z | ∃ a b : ℕ, e ≤ a * W + b ∧ z = L ^ a * Q ^ b}

theorem wI_mul (L Q : A) (W : ℕ) {e e' : ℕ} {z z' : A} (hz : z ∈ wI L Q W e)
    (hz' : z' ∈ wI L Q W e') : z * z' ∈ wI L Q W (e + e') := by
  have hle : wI L Q W e * wI L Q W e' ≤ wI L Q W (e + e') := by
    unfold wI
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro _ ⟨x, ⟨a, b, hab, rfl⟩, y, ⟨a', b', hab', rfl⟩, rfl⟩
    refine ⟨a + a', b + b', ?_, by ring⟩
    rw [add_mul]
    linarith
  exact hle (Ideal.mul_mem_mul hz hz')

theorem wI_zero (L Q : A) (W : ℕ) (z : A) : z ∈ wI L Q W 0 := by
  have h1 : (1 : A) ∈ wI L Q W 0 := Ideal.subset_span ⟨0, 0, Nat.zero_le _, by simp⟩
  simpa using Ideal.mul_mem_left _ z h1

theorem wI_pow (L Q : A) (W : ℕ) {e : ℕ} {z : A} (hz : z ∈ wI L Q W e) (n : ℕ) :
    z ^ n ∈ wI L Q W (n * e) := by
  induction n with
  | zero => simpa using wI_zero L Q W 1
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact wI_mul L Q W ih hz

theorem wI_prod (L Q : A) (W : ℕ) (f : ℕ → A) (e : ℕ → ℕ) (j : ℕ)
    (h : ∀ k < j, f k ∈ wI L Q W (e k)) :
    ∏ k ∈ Finset.range j, f k ∈ wI L Q W (∑ k ∈ Finset.range j, e k) := by
  induction j with
  | zero => simpa using wI_zero L Q W 1
  | succ j ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    exact wI_mul L Q W (ih fun k hk => h k (by omega)) (h j (by omega))

theorem wI_le (L Q : A) (W e c y : ℕ) (hW : 1 ≤ W) (h : c * W + y ≤ e + 1) :
    wI L Q W e ≤ Ideal.span {L ^ c, Q ^ y} := by
  rw [wI, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  by_cases hca : c ≤ a
  · have e1 : L ^ a * Q ^ b = L ^ c * (L ^ (a - c) * Q ^ b) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hca]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · push_neg at hca
    have h1 : (a + 1) * W ≤ c * W := Nat.mul_le_mul_right W hca
    rw [add_mul, one_mul] at h1
    have hyb : y ≤ b := by linarith
    have e1 : L ^ a * Q ^ b = Q ^ y * (L ^ a * Q ^ (b - y)) := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hyb]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end Weight

theorem geom_nat (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (j : ℕ) :
    (∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k) + 1 = ℓ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ]
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

theorem sign_character_at_j_holds : StatSigJ := by
  intro A _ ℓ hℓ x U p j y r c hj hr hp hcy
  have hW : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hpk : ∀ k < j, p k ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ k) := by
    intro k hk
    refine (Ideal.span_le.mpr ?_) (hp k hk)
    intro z hz
    rcases hz with rfl | rfl
    · refine Ideal.subset_span ⟨1, 0, ?_, by simp⟩
      simp only [one_mul, add_zero]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · exact Ideal.subset_span ⟨0, ℓ ^ k, by simp, by simp⟩
  have hP : ∏ k ∈ Finset.range j, p k ^ (ℓ - 1) ∈
      wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ j - 1) := by
    have h1 := wI_prod (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (fun k => p k ^ (ℓ - 1))
      (fun k => (ℓ - 1) * ℓ ^ k) j (fun k hk => by
        have h2 := wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (hpk k hk) (ℓ - 1)
        exact h2)
    have hg := geom_nat ℓ (by omega) j
    have e : ∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k = ℓ ^ j - 1 := by omega
    rw [e] at h1
    exact h1
  have hx : x ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 := by
    have hQ : x + (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨0, 1, by simp, by simp⟩
    have hL : (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨1, 0, by simpa using hW, by simp⟩
    have h := Ideal.sub_mem _ hQ hL
    rwa [add_sub_cancel_right] at h
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hmain := wI_mul (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1))
    (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hx r') (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hP (r' + 1))
  have hN : 1 ≤ ℓ ^ j := Nat.one_le_pow _ _ (by omega)
  have e2 : r' * 1 + (r' + 1) * (ℓ ^ j - 1) + 1 = (r' + 1) * ℓ ^ j := by
    rw [Nat.mul_sub_one]
    have h5 : (r' + 1) * 1 ≤ (r' + 1) * ℓ ^ j := Nat.mul_le_mul_left _ hN
    rw [mul_one] at h5
    omega
  have hin := wI_le (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) _ c y hW (by rw [e2]; exact hcy) hmain
  have hfin : x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1)) ∈
      Ideal.span {(ℓ : A) ^ c * x, x * (x + (ℓ : A)) ^ y} := by
    have h1 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hin
    rw [Ideal.span_mul_span'] at h1
    refine Ideal.span_mono ?_ h1
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rcases hv with rfl | rfl
    · exact Or.inl (mul_comm _ _)
    · exact Or.inr rfl
  have e3 : (U * x * ∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1) =
      U ^ (r' + 1) * (x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1))) := by ring
  rw [e3]
  exact Ideal.mul_mem_left _ _ hfin

theorem residue_series_expansion_holds : StatResSeries := by
  intro n _ ℓ c s H hℓ hc hH hs i
  have hq : 0 < ℓ - 1 := by linarith
  have hq1 : 1 < ℓ - 1 := by linarith
  set f : ℕ → ℝ := fun a => (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a with hf
  have hHle : ∀ k, H k ≤ ∑ k', H k' := fun k =>
    Finset.single_le_sum (f := H) (fun k _ => hH k) (Finset.mem_univ k)
  have hf0 : ∀ a, 0 ≤ f a := fun a =>
    div_nonneg (by linarith [hH (i + ((a + 1 : ℕ) : ZMod n))]) (pow_nonneg hq.le _)
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun a => ?_)
      ((summable_geometric_of_lt_one (inv_nonneg.mpr hq.le) (inv_lt_one_of_one_lt₀ hq1)).mul_left
        ((∑ k', H k') + c + 3))
    simp only [hf]
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by linarith [hHle (i + ((a + 1 : ℕ) : ZMod n))])
      (pow_nonneg hq.le _)
  have hunroll : ∀ N : ℕ, s i ≤ ∑ a ∈ Finset.range N, f a + s (i + (N : ZMod n)) / (ℓ - 1) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hk := hs (i + ((N + 1 : ℕ) : ZMod n))
      have e : i + ((N + 1 : ℕ) : ZMod n) - 1 = i + (N : ZMod n) := by push_cast; ring
      rw [e] at hk
      have hpos : 0 < (ℓ - 1) ^ N := pow_pos hq N
      have h2 : s (i + (N : ZMod n)) / (ℓ - 1) ^ N ≤
          f N + s (i + ((N + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (N + 1) := by
        have h3 := div_le_div_of_nonneg_right hk hpos.le
        rw [add_div, div_div, ← pow_succ'] at h3
        simpa only [hf] using h3
      rw [Finset.sum_range_succ]
      linarith
  have hrem : Filter.Tendsto (fun N : ℕ => s (i + (N : ZMod n)) / (ℓ - 1) ^ N) Filter.atTop
      (nhds 0) := by
    refine squeeze_zero_norm (a := fun N => (∑ k, |s k|) * ((ℓ - 1)⁻¹) ^ N) (fun N => ?_) ?_
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq N), inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun k => |s k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ _)) (pow_nonneg hq.le _)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq.le)
        (inv_lt_one_of_one_lt₀ hq1)).const_mul (∑ k, |s k|)
  have hlim : Filter.Tendsto (fun N : ℕ => s i - s (i + (N : ZMod n)) / (ℓ - 1) ^ N)
      Filter.atTop (nhds (s i - 0)) := tendsto_const_nhds.sub hrem
  have hfin := le_of_tendsto' hlim (fun N => by
    have h1 := hunroll N
    have h2 := hsum.sum_le_tsum (Finset.range N) (fun a _ => hf0 a)
    linarith)
  rw [sub_zero] at hfin
  exact hfin

end Formalism.RepresentationBoundsCohomology.N2
end
end

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SizeBoundSecondCase
section
namespace Formalism.RepresentationBoundsCohomology.N2.Size

open Finset

lemma JSet_subset (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    JSet jumps M ⊆ Icc (1 - (M : ℤ)) ((h : ℤ) + M) := by
  intro x hx
  simp only [JSet, eigSet, Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc] at hx
  rw [Finset.mem_Icc]
  rcases hx with ⟨-, ⟨⟨a, t⟩, ⟨ha, ht1, ht2⟩, rfl⟩⟩ | ⟨h1, h2⟩
  · have h3 := hj a ha
    constructor <;> omega
  · constructor <;> omega

lemma JSet_card (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    (JSet jumps M).card ≤ h + 2 * M := by
  calc (JSet jumps M).card ≤ (Icc (1 - (M : ℤ)) ((h : ℤ) + M)).card :=
        Finset.card_le_card (JSet_subset M h jumps hj)
    _ = h + 2 * M := by
        rw [Int.card_Icc]
        omega

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma sum_range_val (n : ℕ) :
    (∑ k ∈ range (n + 1), padicValNat ℓ k) = padicValNat ℓ n.factorial := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Nat.padicValNat_def, Nat.padicValNat_def]
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero n)]
    ring

lemma sum_val_half (n : ℕ) (T : Finset ℤ) (hT : ∀ j ∈ T, j.natAbs ≤ n)
    (hs : (∀ j ∈ T, j < 0) ∨ (∀ j ∈ T, 0 ≤ j)) :
    (∑ j ∈ T, padicValInt ℓ j) ≤ padicValNat ℓ n.factorial := by
  have hinj : Set.InjOn Int.natAbs (T : Set ℤ) := by
    intro x hx y hy hxy
    rcases Int.natAbs_eq_natAbs_iff.1 hxy with h' | h'
    · exact h'
    · rcases hs with h | h
      · have h1 := h x hx
        have h2 := h y hy
        omega
      · have h1 := h x hx
        have h2 := h y hy
        omega
  calc ∑ j ∈ T, padicValInt ℓ j = ∑ j ∈ T, padicValNat ℓ j.natAbs := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [padicValInt, Nat.padicValNat_def]
    _ = ∑ k ∈ T.image Int.natAbs, padicValNat ℓ k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ range (n + 1), padicValNat ℓ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
          rw [Finset.mem_range]
          have := hT j hj
          omega
        · intro _ _ _
          exact Nat.zero_le _
    _ = padicValNat ℓ n.factorial := sum_range_val ℓ n

lemma sum_val_le (a b : ℕ) (T : Finset ℤ) (hT : T ⊆ Icc (-(a : ℤ)) b) :
    (∑ j ∈ T, padicValInt ℓ j) ≤ padicValNat ℓ a.factorial + padicValNat ℓ b.factorial := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun j => j < 0)]
  apply add_le_add
  · apply sum_val_half ℓ a
    · intro j hj
      rw [Finset.mem_filter] at hj
      have h1 := Finset.mem_Icc.1 (hT hj.1)
      omega
    · left
      intro j hj
      exact (Finset.mem_filter.1 hj).2
  · apply sum_val_half ℓ b
    · intro j hj
      rw [Finset.mem_filter] at hj
      have h1 := Finset.mem_Icc.1 (hT hj.1)
      omega
    · right
      intro j hj
      have h1 := (Finset.mem_filter.1 hj).2
      omega

lemma JSet_sum (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    (∑ j ∈ JSet jumps M, padicValInt ℓ j) ≤
      padicValNat ℓ M.factorial + padicValNat ℓ (h + M).factorial := by
  apply sum_val_le ℓ M (h + M) (JSet jumps M)
  intro x hx
  have h1 := Finset.mem_Icc.1 (JSet_subset M h jumps hj hx)
  rw [Finset.mem_Icc]
  push_cast
  constructor <;> omega

lemma legendre (n : ℕ) : (ℓ - 1) * padicValNat ℓ n.factorial ≤ n := by
  rw [Nat.padicValNat_def]
  rw [(Fact.out : ℓ.Prime).sub_one_mul_multiplicity_factorial]
  exact Nat.sub_le _ _

lemma val_factorial_le_self (n : ℕ) : padicValNat ℓ n.factorial ≤ n := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) (legendre ℓ n)

lemma val_factorial_le_div (n : ℕ) :
    (padicValNat ℓ n.factorial : ℝ) ≤ (n : ℝ) / ((ℓ : ℝ) - 1) := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast h2
    linarith
  rw [le_div_iff₀ hpos]
  have h := legendre ℓ n
  have hc : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : (((ℓ - 1) * padicValNat ℓ n.factorial : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_mul] at h'
  rw [hc] at h'
  linarith

end Formalism.RepresentationBoundsCohomology.N2.Size

namespace Formalism.RepresentationBoundsCohomology.N2

open Finset

theorem size_bound_second_case : StatSizeB := by
  intro ℓ _ M h H s jumps hs hMH hj
  unfold eWB eUB
  have h1 := Size.JSet_card M h jumps hj
  have h2 := Size.JSet_sum ℓ M h jumps hj
  have h3 := Size.val_factorial_le_self ℓ (2 * H)
  have h4 := Size.val_factorial_le_self ℓ M
  have h5 := Size.val_factorial_le_self ℓ (h + M)
  have hsum : ∑ j ∈ JSet jumps M, (s + padicValInt ℓ j) =
      (JSet jumps M).card * s + ∑ j ∈ JSet jumps M, padicValInt ℓ j := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsum]
  have h6 : (JSet jumps M).card * s ≤ (h + 2 * M) * s := Nat.mul_le_mul_right s h1
  have h7 : (h + 2 * M) * s ≤ 2 * H * s := Nat.mul_le_mul_right s (by omega)
  have h8 : M * s ≤ H * s := Nat.mul_le_mul_right s (by omega)
  have h9 : H ≤ H * s := Nat.le_mul_of_pos_right H hs
  nlinarith

theorem size_bound_first_case : StatSizeA := by
  intro ℓ _ hℓ M h H jumps hMH hj
  have hp : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by
    have := hp.two_le
    omega
  have h3r : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h3
  set t : ℝ := (ℓ : ℝ) - 1 with ht
  have ht2 : (2 : ℝ) ≤ t := by rw [ht]; linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hMHr : (M : ℝ) + (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hMH
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) :=
    Real.logb_nonneg (by linarith) (by linarith)

  have hW0 : 0 ≤ (H : ℝ) * ℓ / t ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) := by positivity
  have hW : (eWA ℓ H : ℝ) ≤ (H : ℝ) * ℓ / t ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) :=
    Nat.floor_le hW0
  have hW2 : (H : ℝ) * ℓ / t ^ 2 ≤ 3 / 2 * ((H : ℝ) / t) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 3 / 2 * ((H : ℝ) / t) * t ^ 2 = 3 / 2 * (H : ℝ) * t := by
      field_simp
    rw [e]
    have : (ℓ : ℝ) = t + 1 := by rw [ht]; ring
    rw [this]
    nlinarith

  have hv := Size.JSet_sum ℓ M h jumps hj
  have hvr : ((∑ j ∈ JSet jumps M, padicValInt ℓ j : ℕ) : ℝ) ≤
      (padicValNat ℓ M.factorial : ℝ) + (padicValNat ℓ (h + M).factorial : ℝ) := by
    exact_mod_cast hv
  have f2 := Size.val_factorial_le_div ℓ M
  have f3 := Size.val_factorial_le_div ℓ (h + M)
  rw [← ht] at f2 f3
  push_cast at f3

  have ha : (aStar ℓ M : ℝ) ≤ (M : ℝ) / t + 1 := by
    unfold aStar
    push_cast
    have := @Nat.cast_div_le ℝ _ _ _ M (ℓ - 1)
    rw [Nat.cast_sub (by omega), Nat.cast_one, ← ht] at this
    linarith
  have f4 := Size.val_factorial_le_div ℓ (aStar ℓ M)
  rw [← ht] at f4
  have f5 : (aStar ℓ M : ℝ) / t ≤ ((M : ℝ) / t + 1) / 2 := by
    have h0 : (0 : ℝ) ≤ (aStar ℓ M : ℝ) := Nat.cast_nonneg _
    calc (aStar ℓ M : ℝ) / t ≤ (aStar ℓ M : ℝ) / 2 :=
          div_le_div_of_nonneg_left h0 (by norm_num) ht2
      _ ≤ ((M : ℝ) / t + 1) / 2 := by linarith
  have d1 : (M : ℝ) / t ≤ (H : ℝ) / t := div_le_div_of_nonneg_right (by linarith) htpos.le
  have d2 : (M : ℝ) / t + ((h : ℝ) + (M : ℝ)) / t ≤ 2 * ((H : ℝ) / t) := by
    rw [← add_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) htpos.le
  have e0 : 15 / 2 * (H : ℝ) / t = 15 / 2 * ((H : ℝ) / t) := by ring
  have hHt : 0 ≤ (H : ℝ) / t := by positivity
  unfold eUA
  push_cast at hvr ⊢
  rw [e0]
  linarith

end Formalism.RepresentationBoundsCohomology.N2
end

