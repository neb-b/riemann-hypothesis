module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhds
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.RootEx.UnipPow

theorem pow_dvd_choose {q : ℕ} (hq : q.Prime) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    q ^ (m - i) ∣ (q ^ m).choose i := by
  have := Fact.mk hq
  rcases Nat.eq_zero_or_pos ((q ^ m).choose i) with h0 | hpos
  · rw [h0]
    exact dvd_zero _
  have hdvd : q ^ m ∣ (q ^ m).choose i * i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero m hq.ne_zero)
    rw [hN]
    exact ⟨N.choose j, (Nat.add_one_mul_choose_eq N j).symm⟩
  have hv : m ≤ padicValNat q ((q ^ m).choose i) + padicValNat q i := by
    rw [← (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hpos.ne' hi]
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (mul_ne_zero hpos.ne' hi)).mp hdvd
  have hi' : padicValNat q i < i := by
    simpa only [Nat.padicValNat_def] using (padicValNat_le_nat_log i).trans_lt (Nat.log_lt_self q hi)
  exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hpos.ne').mpr (by omega)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_resCard_lt_one : valuation k (resCard k : k) < 1 := by
  have hres : IsLocalRing.residue 𝒪[k] (resCard k : 𝒪[k]) = 0 := by
    let := Fintype.ofFinite 𝓀[k]
    rw [map_natCast, resCard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hnu : ¬ IsUnit (resCard k : 𝒪[k]) := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres
  have hlt := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hnu
  simpa using hlt

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_natCast_le_one (j : ℕ) : valuation k (j : k) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ]
    exact ((valuation k).map_add _ _).trans (max_le ih (by simp))

theorem tendsto_choose (hq : (resCard k).Prime) {i : ℕ} (hi : i ≠ 0) :
    Filter.Tendsto (fun m : ℕ => (((resCard k ^ m).choose i : ℕ) : k)) Filter.atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
  intro γ _
  have hq1 := valuation_resCard_lt_one (k := k)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hq1 γ
  rw [Filter.eventually_atTop]
  refine ⟨n + i, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := pow_dvd_choose hq m hi
  show valuation k (((resCard k ^ m).choose i : ℕ) : k) < γ
  rw [ht, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
  calc valuation k (resCard k : k) ^ (m - i) * valuation k (t : k)
      ≤ valuation k (resCard k : k) ^ (m - i) := mul_le_of_le_one_right' (valuation_natCast_le_one t)
    _ ≤ valuation k (resCard k : k) ^ n := pow_le_pow_right_of_le_one' hq1.le (by omega)
    _ < γ := hn

theorem add_one_pow_eq {R : Type} [Ring R] {a : R} {d : ℕ} (ha : a ^ d = 0) (M : ℕ) :
    (a + 1) ^ M = ∑ i ∈ Finset.range d, (M.choose i) • a ^ i := by
  rw [(Commute.one_right a).add_pow]
  simp only [one_pow, mul_one]
  have key : ∀ s : Finset ℕ, ∑ i ∈ s, a ^ i * (M.choose i : R) = ∑ i ∈ s, M.choose i • a ^ i :=
    fun s => Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]; exact (Nat.cast_comm _ _).symm
  rw [key]
  calc ∑ i ∈ Finset.range (M + 1), M.choose i • a ^ i
      = ∑ i ∈ Finset.range (M + 1 + d), M.choose i • a ^ i := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_
        rw [Finset.mem_range] at hi'
        rw [Nat.choose_eq_zero_of_lt (by omega : M < i), zero_smul]
    _ = ∑ i ∈ Finset.range d, M.choose i • a ^ i := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        rw [pow_eq_zero_of_le (by omega : d ≤ i) ha, smul_zero]

theorem tendsto_pow_of_nilpotent {ι : Type} [Fintype ι] [DecidableEq ι] (hq : (resCard k).Prime)
    {g : Matrix ι ι k} {d : ℕ} (ha : (g - 1) ^ (d + 1) = 0) :
    Filter.Tendsto (fun m : ℕ => g ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
  have hexp : ∀ m : ℕ, g ^ (resCard k ^ m) =
      ∑ i ∈ Finset.range (d + 1), (((resCard k ^ m).choose i : ℕ) : k) • (g - 1) ^ i := by
    intro m
    have h := add_one_pow_eq ha (resCard k ^ m)
    rw [sub_add_cancel] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => (Nat.cast_smul_eq_nsmul k _ _).symm
  have hlim := (tendsto_finsetSum (Finset.range d) fun i _ =>
    (tendsto_choose hq (Nat.succ_ne_zero i)).smul_const ((g - 1) ^ (i + 1))).add
    (tendsto_const_nhds (x := (1 : Matrix ι ι k)))
  simp only [zero_smul, Finset.sum_const_zero, zero_add] at hlim
  refine hlim.congr fun m => ?_
  rw [hexp, Finset.sum_range_succ']
  simp

theorem pow_sub_one_apply {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) (j : ℕ) :
    ∀ r s : n ⊕ Fin c, lev p s < lev p r + j →
      (((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ j) r s = 0 := by
  induction j with
  | zero =>
    intro r s h
    rw [pow_zero, Matrix.one_apply_ne (by rintro rfl; omega)]
  | succ j ih =>
    intro r s h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : lev p t < lev p r + j
    · rw [ih r t ht, zero_mul]
    · rw [Matrix.sub_apply, hg t s (by omega), sub_self, mul_zero]

theorem pow_sub_one_eq_zero {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) :
    ((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ (c + p + 1) = 0 := by
  have hb : ∀ t : n ⊕ Fin c, lev p t ≤ c + p := by
    rintro (t | t)
    · show p ≤ c + p
      omega
    · show t.val + 1 ≤ c + p
      have := t.isLt
      omega
  ext r s
  rw [Matrix.zero_apply]
  exact pow_sub_one_apply hg _ r s (by have := hb s; omega)

theorem inN_of_mem {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : g ∈ N K n c p) : InN p g := by
  have hle : N K n c p ≤ GlobalTheory.RootEx.Model.Nsub K n c p :=
    (Subgroup.closure_le _).mpr fun x hx => hx
  exact hle hg

theorem exists_pow_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ)
    (hq : (resCard k).Prime) :
    ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  intro u hu U hU
  have h1 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem hu))
  have h2 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem (inv_mem hu)))
  have hA : Filter.Tendsto (fun m : ℕ => ((u ^ (resCard k ^ m) : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h1.congr fun m => (Units.val_pow_eq_pow_val _ _).symm
  have hB : Filter.Tendsto (fun m : ℕ => (((u ^ (resCard k ^ m))⁻¹ : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h2.congr fun m => by rw [← inv_pow, Units.val_pow_eq_pow_val]
  have hT : Filter.Tendsto (fun m : ℕ => u ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    have hP := hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)
    simpa [Function.comp_def] using hP
  exact (hT.eventually_mem hU).exists

end GlobalTheory.RootEx.UnipPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.Proof.TwistSupportPeriodicLevels

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩

variable {r s s' : Type} [Fintype r] [DecidableEq r]

theorem intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg

private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]


open Classical in
theorem parPhi_add {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx

variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2

theorem maxM_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)

theorem coords_add (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp

theorem stabLat_le_KO {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)

private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)

end

theorem ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))

end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacter
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
  GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricLowerBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem lower_block_det (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (j : GL (A ⊕ D) k) (hj : j ∈ parahoric k A D) :
    ∃ a b : 𝒪[k], (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k a ∧
      ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k b ∧
      IsLocalRing.residue 𝒪[k] (a * b) = 1 := by
  obtain ⟨⟨h, rfl⟩, hlow⟩ := mem_parahoric.1 hj
  set f := IsLocalRing.residue 𝒪[k]
  set Hb := f.mapMatrix h.val
  set Gb := f.mapMatrix (h⁻¹).val
  have hz : Hb.toBlocks₂₁ = 0 := by
    ext i j'
    exact (residue_eq_zero_iff_val _).2 (hlow i j')
  have hHG : Hb * Gb = 1 := by
    simp only [Hb, Gb, ← map_mul, Units.mul_inv, map_one]
  have h22 : Hb.toBlocks₂₂ * Gb.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hHG
    rw [← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks Gb, fromBlocks_multiply, hz] at this
    have e : (1 : Matrix (A ⊕ D) (A ⊕ D) 𝓀[k]).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, Matrix.one_apply]
    simpa [e] using this
  refine ⟨h.val.toBlocks₂₂.det, (h⁻¹).val.toBlocks₂₂.det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det]; rfl
  · rw [RingHom.map_det, ← map_inv]; rfl
  · rw [map_mul, RingHom.map_det, RingHom.map_det, ← det_mul]
    exact (congrArg det h22).trans det_one

end GlobalTheory.ParahoricLowerBlock

namespace GlobalTheory.ParahoricLowerBlock

theorem lower_block_tame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξ j hj
  obtain ⟨a, b, ha, hb, hab⟩ := lower_block_det A D j hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul, map_zero] at hab
    exact zero_ne_one hab
  refine ⟨?_, fun d d' hd hd' => ?_⟩
  · rw [ha]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[k] k)).2 ha0
  · have hv : valuation k (((d * d' : kˣ) : k) - 1) < 1 := by
      have e : ((d * d' : kˣ) : k) - 1 = algebraMap 𝒪[k] k (a * b - 1) := by
        rw [Units.val_mul, hd, hd', ha, hb, map_sub, map_mul, map_one]
      rw [e, ← residue_eq_zero_iff_val, map_sub, hab, map_one, sub_self]
    have := hξ (d * d') hv
    rw [map_mul] at this
    have := congrArg Units.val this
    simpa using this

end GlobalTheory.ParahoricLowerBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilated
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.Mem.Lift.VacAnn

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
private theorem hasFDerivAt_gau {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w : V) :
    HasFDerivAt (_root_.GlobalTheory.RealWeil.gau : V → ℂ)
      ((-(Real.pi : ℂ) * _root_.GlobalTheory.RealWeil.gau w) • ((Complex.ofRealCLM).comp (innerSL ℝ w))) w := by
  have h1 : HasFDerivAt (fun u : V => ‖u‖ ^ 2) (2 • innerSL ℝ w) w := by
    simpa using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp w h1
  have h3 := (h2.const_mul (-(Real.pi : ℂ) / 2)).cexp
  have hf : (_root_.GlobalTheory.RealWeil.gau : V → ℂ) =
      fun u => Complex.exp (-(Real.pi : ℂ) / 2 * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u; unfold _root_.GlobalTheory.RealWeil.gau; push_cast; ring_nf
  rw [hf]
  refine h3.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  push_cast
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by
  rw [(hasFDerivAt_gau w).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.proj_annihilated : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h x z
  set P := _root_.GlobalTheory.RealWeil.proj h
  set f := P x with hf_def
  have hf : _root_.GlobalTheory.RealWeil.Sm ρ f :=
    _root_.GlobalTheory.RealWeil.Good.sm hJ
      (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hsand : ∀ w : V, P (ρ w f) = _root_.GlobalTheory.RealWeil.gau w • f := fun w =>
    _root_.GlobalTheory.RealWeil.proj_heis_proj hJ h w x
  have hcomp : ∀ w v : V, P (ρ w (_root_.GlobalTheory.Mem.Lift.dH ρ v f)) =
      ((Real.pi : ℂ) * I * (⟪w, J v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w
        - (Real.pi : ℂ) * (⟪w, v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w) • f := by
    intro w v
    rw [_root_.GlobalTheory.Mem.Lift.VacBd.heis_dH h hf v w, map_add (f := _), map_smul, hsand w,
      _root_.GlobalTheory.Mem.Lift.VacBd.fderiv_compress P hf _root_.GlobalTheory.RealWeil.contDiff_gau hsand w v,
      _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply, smul_smul, ← add_smul]
    congr 1
    show (Real.pi : ℂ) * I * ((⟪w, J v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w
        + -(Real.pi : ℂ) * ((⟪w, v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w = _
    ring
  set G := _root_.GlobalTheory.Mem.Lift.dH ρ z f + I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) f
  have hG : _root_.GlobalTheory.RealWeil.Sm ρ G :=
    _root_.GlobalTheory.RealWeil.Osc.sm_add (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf z)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul I (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf (J z)))
  have hzero : ∀ w : V, P (ρ w G) = 0 := by
    intro w
    simp only [G, map_add (f := _), map_smul, hcomp, smul_smul, ← add_smul, hJ z, inner_neg_right]
    apply smul_eq_zero_of_left
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [← (_root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hG).inversion hJ]
  have hzero' : ∀ w : V, _root_.GlobalTheory.RealWeil.proj h (ρ (-w) G) = 0 := fun w => hzero (-w)
  simp only [hzero', map_zero, integral_zero]

end GlobalTheory.Mem.Lift.VacAnn
end

