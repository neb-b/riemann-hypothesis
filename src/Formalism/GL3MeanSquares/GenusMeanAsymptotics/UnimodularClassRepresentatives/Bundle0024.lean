module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0005

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumCoset
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_box_inter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := (finite_boxSet hK hF T).subset fun _ hn => hn.1

theorem sum_le_sum_shift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {A B : Set (𝓞 F)}
    {T T' : ℝ} (y : 𝓞 F) (hy0 : ∀ w, 0 ≤ rEmb w y) (hyT : ∀ w, rEmb w y + T ≤ T')
    (hAB : ∀ n ∈ A, n + y ∈ B) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T' ∧ n ∈ B},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hA := finite_box_inter hK hF T A
  have hB := finite_box_inter hK hF T' B
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  have key : ∀ n ∈ hA.toFinset, n + y ∈ hB.toFinset ∧
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
        (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨hnb, hnA⟩ := hn
    have hb : ∀ w, 0 < rEmb w n ∧ rEmb w n ≤ T := (mem_boxSet_iff hK hF).1 hnb
    have hny : n + y ∈ boxSet K F T' := by
      rw [mem_boxSet_iff hK hF]
      intro w
      rw [map_add (f := _)]
      constructor
      · linarith [(hb w).1, hy0 w]
      · linarith [(hb w).2, hyT w]
    refine ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hny, hAB n hnA⟩, ?_⟩
    have hle : (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ (Ideal.absNorm (Ideal.span {n + y}) : ℝ) := by
      rw [absNorm_eq_prod_of_mem hK hF hnb, absNorm_eq_prod_of_mem hK hF hny]
      apply Finset.prod_le_prod₀
      · intro w _
        exact (hb w).1.le
      · intro w _
        rw [map_add (f := _)]
        linarith [hy0 w]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle _
  calc ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)
      ≤ ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) :=
        Finset.sum_le_sum fun n hn => (key n hn).2
    _ = ∑ n ∈ hA.toFinset.image (· + y), (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
    _ ≤ ∑ n ∈ hB.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
          exact (key n hn).1
        · intro _ _ _
          positivity

theorem exists_shifts {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    ∃ (y y' : 𝓞 F) (R : ℝ), (∀ w, 0 ≤ rEmb w y ∧ rEmb w y ≤ R) ∧ (∀ w, 0 ≤ rEmb w y' ∧ rEmb w y' ≤ R) ∧
      (∀ n, n - x₀ ∈ I → n + y ∈ I) ∧ ∀ n, n ∈ I → n + y' - x₀ ∈ I := by
  classical
  have hN0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  obtain ⟨C, hCw⟩ : ∃ C : ℝ, ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀| ≤ C :=
    ⟨∑ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀|, fun w =>
      Finset.single_le_sum (f := fun w => |rEmb w x₀|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)⟩
  obtain ⟨c, hc⟩ := exists_nat_ge C
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  have hcN : C ≤ ((c * Ideal.absNorm I : ℕ) : ℝ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hmem : ((c * Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := by
    rw [Nat.cast_mul]
    exact I.mul_mem_left _ hNmem
  refine ⟨((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀, ((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀,
    ((c * Ideal.absNorm I : ℕ) : ℝ) + C, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [map_sub, map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro w
    rw [map_add (f := _), map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀) =
        (n - x₀) + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀) - x₀ =
        n + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem

theorem tendsto_ratio (e : ℕ) :
    Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ e) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ e)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun j => ?_
    push_cast
    rfl
  have h2 := (h1.pow 2).pow e
  simp only [one_pow] at h2
  exact h2.congr fun j => by rw [div_pow, div_pow]

private theorem tendsto_scaled_of_interleaved_tendsto (D : ℕ) {u v : ℕ → ℝ} {L : ℝ}
    (hv : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * v j) atTop (𝓝 L))
    (hup : ∀ᶠ j in atTop, u j ≤ v (j + 1))
    (hlo : ∀ᶠ j in atTop, v j ≤ u (j + 1)) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * u j) atTop (𝓝 L) := by
  have hg : ∀ j : ℕ, ((j : ℝ) ^ 2) ^ (-(D : ℤ)) = (((j : ℝ) ^ 2) ^ D)⁻¹ := fun j => by
    rw [zpow_neg, zpow_natCast]
  simp only [hg] at hv ⊢
  have hs := tendsto_ratio D
  have hs1 : Tendsto (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) := by
    have h := hs1.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using h
  have hv2 : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))
      atTop (𝓝 L) :=
    (hv.comp (tendsto_add_atTop_nat 1)).comp (tendsto_add_atTop_nat 1)
  have lowT : Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)) atTop (𝓝 L) := by
    simpa only [one_mul] using hs.mul hv
  have upT : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))) atTop (𝓝 L) := by
    simpa only [one_mul] using ht.mul hv2
  have hup1 : ∀ᶠ j in atTop, u (j + 1) ≤ v (j + 1 + 1) := (tendsto_add_atTop_nat 1).eventually hup
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowT upT ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with j hj hj1
    have hj0 : ((j : ℝ) ^ 2) ^ D ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    calc (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) * ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)
        = ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v j := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul, div_eq_inv_mul]
      _ ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1) := mul_le_mul_of_nonneg_left hj hpos
  · filter_upwards [hup1] with j hj
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    have h0 : ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)))
    calc ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1)
        ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1) := mul_le_mul_of_nonneg_left hj hpos
      _ = ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
          (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1)) := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, div_eq_inv_mul]

theorem tendsto_sum_coset (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  obtain ⟨y, y', R, hy, hy', hyI, hy'I⟩ := exists_shifts hI x₀
  obtain ⟨j0, hj0⟩ := exists_nat_ge R
  refine tendsto_scaled_of_interleaved_tendsto _ (tendsto_sum_ideal hK hF hm hI) ?_ ?_
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := {n | n - x₀ ∈ I}) (B := (I : Set (𝓞 F)))
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y (fun w => (hy w).1) ?_ ?_
    · intro w
      have h1 := (hy w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hyI n hn
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := (I : Set (𝓞 F))) (B := {n | n - x₀ ∈ I})
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y' (fun w => (hy' w).1) ?_ ?_
    · intro w
      have h1 := (hy' w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hy'I n hn

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityField
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

open NormLifting

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

abbrev AQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  𝓞 K ⧸ extP K 𝔭 ^ k

def sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : AQ K 𝔭 k →+* AQ K 𝔭 k :=
  conjQ (extP K 𝔭 ^ k) (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k)

theorem sg_mk (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    sg hF 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (conjO K a) := conjQ_mk _ _ a

theorem sg_sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) :
    sg hF 𝔭 k (sg hF 𝔭 k a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [sg_mk, sg_mk, conjO_conjO]

def InQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) : Prop :=
  ∃ z ∈ extP K 𝔭, Ideal.Quotient.mk (extP K 𝔭 ^ k) z = a

theorem inQ_mk (𝔭 : Ideal (𝓞 F)) {k : ℕ} (hk : 1 ≤ k) (y : 𝓞 K) :
    InQ 𝔭 k (Ideal.Quotient.mk (extP K 𝔭 ^ k) y) ↔ y ∈ extP K 𝔭 := by
  unfold InQ
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hd : z - y ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hzy
    have hd' : z - y ∈ extP K 𝔭 := Ideal.pow_le_self (by omega) hd
    have hy := sub_mem hz hd'
    simpa using hy
  · intro hy
    exact ⟨y, hy, rfl⟩

def cnt (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (¬ ∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntI (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

theorem cnt_eq_normRepCount (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = normRepCount K (extP K 𝔭 ^ k) M n :=
  (normRepCount_eq _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k) M n).symm

theorem finite_AQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (AQ K 𝔭 k) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal h𝔭))

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  unfold extP
  rw [Ideal.absNorm_algebraMap, ← MeanB.finrank_eq_two hK hF]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

theorem card_AQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Nat.card (AQ K 𝔭 k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, absNorm_extP hK hF, ← pow_mul]

theorem card_split {X : Type*} [Finite X] (p r : X → Prop) :
    Nat.card {x // r x} = Nat.card {x // ¬ p x ∧ r x} + Nat.card {x // p x ∧ r x} := by
  classical
  haveI := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact h1.1 h2.1

theorem cnt_eq_add (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = cntP hF 𝔭 k M n + cntI hF 𝔭 k M n := by
  haveI := finite_AQ (K := K) h𝔭 k
  unfold cnt cntP cntI
  exact card_split (fun x : Fin M → AQ K 𝔭 k => ∀ i, InQ 𝔭 k (x i)) _

theorem exists_tr_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 K} (ha : a ∉ extP K 𝔭) (N : ℕ) :
    ∃ b : 𝓞 K, conjO K a * b + conjO K b * a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  have h1 : ∃ b : 𝓞 K, conjO K a * b + conjO K b * a ∉ extP K 𝔭 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon 1
    have e2 := hcon θ
    apply ha
    have e3 : (θ - conjO K θ) * a ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one]
      have := (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left θ e1) e2
      have e : θ * (conjO K a * 1 + conjO K 1 * a) - (conjO K a * θ + conjO K θ * a) =
          (θ - conjO K θ) * a := by rw [map_one]; ring
      rwa [e] at this
    have := idealPowerSpanBounds.mem_of_unit_mul_mem hθ e3
    rwa [pow_one] at this
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := idealPowerSpanBounds.exists_tr hF (conjO K a * b)
  rw [map_mul, conjO_conjO, mul_comm a] at hc
  have hc𝔭 : c ∉ 𝔭 := by
    intro h
    apply hb
    rw [← hc]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 hc𝔭 N
  refine ⟨(algebraMap (𝓞 F) (𝓞 K)) u * b, ?_⟩
  have e : conjO K a * ((algebraMap (𝓞 F) (𝓞 K)) u * b) + conjO K ((algebraMap (𝓞 F) (𝓞 K)) u * b) * a - 1 = (algebraMap (𝓞 F) (𝓞 K)) (u * c - 1) := by
    rw [map_mul (conjO K), idealPowerSpanBounds.conjO_map hF, map_sub, map_mul, map_one, hc]
    ring
  rw [e, idealPowerSpanBounds.mem_pow_iff]
  exact hu

theorem cntP_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (k + 1) M n = Ideal.absNorm 𝔭 ^ (2 * M - 1) * cntP hF 𝔭 k M n := by
  have hle : extP K 𝔭 ^ (k + 1) ≤ extP K 𝔭 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have := finite_AQ (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta hθ (k + 1)
  have hIn : ∀ a : AQ K 𝔭 (k + 1), InQ 𝔭 k (Ideal.Quotient.factor hle a) ↔ InQ 𝔭 (k + 1) a := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk, inQ_mk 𝔭 (by omega)]
  have h := SecondPropositionFree.card_lift_pred (σ := sg hF 𝔭 (k + 1)) (τ := sg hF 𝔭 k)
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [sg_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, sg_mk])
    (sg_sg hF 𝔭 (k + 1))
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by
      rw [sg_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact he)
    (n := Ideal.Quotient.mk _ n) (by rw [sg_mk, hn]) (Ideal.absNorm 𝔭)
    (by rw [card_AQ hK hF, card_AQ hK hF]; ring) M hM
    (fun x => ¬ ∀ i, InQ 𝔭 k (x i))
    (by
      intro y hy w hw
      push Not at hy
      obtain ⟨i₀, hi₀⟩ := hy
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i₀)
      rw [← ha, Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk] at hi₀
      obtain ⟨b, hb⟩ := exists_tr_one hK hF h𝔭 hi₀ (k + 1)
      refine SecondPropositionFree.mem_range_linPart _ y i₀ (b := Ideal.Quotient.mk _ b) ?_ hw
      rw [← ha, sg_mk, sg_mk, ← map_mul, ← map_mul, ← map_add (f := _), ← map_one (Ideal.Quotient.mk _),
        Ideal.Quotient.eq]
      exact hb)
  rw [Ideal.Quotient.factor_mk] at h
  unfold cntP
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [hIn])

theorem cntP_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) {M : ℕ} (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (j + 1) M n = Ideal.absNorm 𝔭 ^ ((2 * M - 1) * j) * cntP hF 𝔭 1 M n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cntP_succ hK hF h𝔭 (by omega) hM hn, ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

