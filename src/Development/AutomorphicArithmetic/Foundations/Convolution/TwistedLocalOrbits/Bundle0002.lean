module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.RootExistence

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.zero : Bd a (0 : Matrix (Fin n) (Fin n) E) := fun i j => by simp

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd a M) (h' : Bd a N) : Bd a (M - N) := fun i j =>
  Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.smul (h : Bd a M) (x : E) : Bd (valuation E x * a) (x • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul' le_rfl (h i j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.one : Bd 1 (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem Bd.of_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) : Bd 1 M := by
  simpa using (h.mono ha).add Bd.one

private theorem Bd.pow_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) (m : ℕ) : Bd a (M ^ m - 1) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - 1 = (M ^ m - 1) * M + (M - 1) := by
      rw [pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.mul (h.of_sub_one ha)) h

private theorem Bd.pow_sub_pow (hM : Bd a (M - 1)) (hN : Bd a (N - 1)) (ha : a ≤ 1) (hd : Bd b (M - N)) (m : ℕ) :
    Bd (a * b) (M ^ m - N ^ m - m • (M - N)) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - N ^ (m + 1) - (m + 1) • (M - N) =
        M * (M ^ m - N ^ m - m • (M - N)) + (M - 1) * (m • (M - N)) + (M - N) * (N ^ m - 1) := by
      rw [pow_succ', pow_succ', succ_nsmul]
      generalize m • (M - N) = D
      noncomm_ring
    rw [e]
    refine Bd.add (Bd.add ?_ (hM.mul (hd.nsmul m))) ?_
    · simpa using (hM.of_sub_one ha).mul ih
    · rw [mul_comm a b]
      exact hd.mul (hN.pow_sub_one ha m)

private theorem val_nat_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem eq_zero_of_bd {ρ c : ValueGroupWithZero E} (hρ : ρ < 1) {M : Matrix (Fin n) (Fin n) E}
    (h : ∀ k : ℕ, Bd (ρ ^ k * c) M) : M = 0 := by
  ext i j
  by_contra hne
  have hv : valuation E (M i j) ≠ 0 := by simpa using hne
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv (by simpa using h 0 i j)
  haveI : MulArchimedean (ValueGroupWithZero E) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hρ (Units.mk0 (valuation E (M i j) / c) (div_ne_zero hv hc))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc)] at hk
  exact absurd (h k i j) (not_le.mpr hk)

private theorem isCompact_bd (c : ValueGroupWithZero E) : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd c M} := by
  have h := isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ c}})
    fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E c
  exact h

private theorem exists_root (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    (g : Matrix (Fin n) (Fin n) E) (hg : Bd (r * valuation E (q : E)) (g - 1)) :
    ∃ u : Matrix (Fin n) (Fin n) E, Bd r (u - 1) ∧ u ^ q = g := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  haveI : T2Space E := by
    letI := IsTopologicalAddGroup.rightUniformSpace E
    haveI := isUniformAddGroup_of_addCommGroup (G := E)
    infer_instance
  set ρ := r / valuation E (q : E) with hρ
  have hρ1 : ρ < 1 := (div_lt_one₀ hq0).mpr hr
  let S : ℕ → Set (Matrix (Fin n) (Fin n) E) := fun k =>
    {X | Bd r X} ∩ {X | Bd (ρ ^ k * (r * valuation E (q : E))) ((X + 1) ^ q - g)}
  have hcl : ∀ k, IsClosed (S k) := fun k =>
    (isCompact_bd r).isClosed.inter
      ((isCompact_bd (ρ ^ k * (r * valuation E (q : E)))).isClosed.preimage
        (f := fun X : Matrix (Fin n) (Fin n) E => (X + 1) ^ q - g) (by fun_prop))
  have hanti : ∀ k, S (k + 1) ⊆ S k := fun k X hX =>
    ⟨hX.1, Bd.mono hX.2 (mul_le_mul' (pow_le_pow_right_of_le_one' hρ1.le k.le_succ) le_rfl)⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, Bd.zero, ?_⟩
      have := (Bd.zero (n := n)).sub hg
      simpa using this
    | succ k ih =>
      obtain ⟨X, hX, hX'⟩ := ih
      have hD : Bd (ρ ^ k * r) ((q : E)⁻¹ • ((X + 1) ^ q - g)) := by
        have h := Bd.smul hX' (q : E)⁻¹
        rwa [map_inv₀, ← mul_assoc (ρ ^ k), mul_comm (ρ ^ k * r), inv_mul_cancel_left₀ hq0.ne'] at h
      set D := (q : E)⁻¹ • ((X + 1) ^ q - g) with hDdef
      have hqD : q • D = (X + 1) ^ q - g := by
        rw [hDdef, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hq]
      have hXD : Bd r (X - D) :=
        Bd.sub hX (hD.mono (by simpa using mul_le_mul' (pow_le_one' hρ1.le k) (le_refl r)))
      refine ⟨X - D, hXD, ?_⟩
      have h := Bd.pow_sub_pow (M := X + 1) (N := X - D + 1) (a := r) (b := ρ ^ k * r)
        (by simpa using hX) (by simpa using hXD) hr1 (by simpa using hD) q
      have e1 : X + 1 - (X - D + 1) = D := by abel
      rw [e1, hqD] at h
      have h' := (Bd.zero (n := n)).sub h
      have e2 : 0 - ((X + 1) ^ q - (X - D + 1) ^ q - ((X + 1) ^ q - g)) = (X - D + 1) ^ q - g := by abel
      have e3 : r * (ρ ^ k * r) = ρ ^ (k + 1) * (r * valuation E (q : E)) := by
        have : ρ * valuation E (q : E) = r := div_mul_cancel₀ _ hq0.ne'
        calc r * (ρ ^ k * r) = ρ * valuation E (q : E) * (ρ ^ k * r) := by rw [this]
          _ = _ := by rw [pow_succ]; ac_rfl
      rw [e2, e3] at h'
      exact h'
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    ((isCompact_bd r).of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  rw [Set.mem_iInter] at hX
  exact ⟨X + 1, by simpa using (hX 0).1, sub_eq_zero.mp (eq_zero_of_bd hρ1 fun k => (hX k).2)⟩

private theorem root_unique (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    {A C : Matrix (Fin n) (Fin n) E} (hA : Bd r (A - 1)) (hC : Bd r (C - 1)) (h : A ^ q = C ^ q) : A = C := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  have hρ1 : r / valuation E (q : E) < 1 := (div_lt_one₀ hq0).mpr hr
  refine sub_eq_zero.mp (eq_zero_of_bd (c := r) hρ1 fun k => ?_)
  induction k with
  | zero => simpa using hA.sub hC
  | succ k ih =>
    have h1 := Bd.pow_sub_pow hA hC hr1 ih q
    rw [h, sub_self] at h1
    have h2 := ((Bd.zero (n := n)).sub h1).smul (q : E)⁻¹
    rw [zero_sub, zero_sub, neg_neg, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hq, map_inv₀] at h2
    refine h2.mono (le_of_eq ?_)
    rw [pow_succ, div_eq_mul_inv]
    ac_rfl

end UpperTheory.ConvolutionTheory.Loc.RootExistence

open UpperTheory.ConvolutionTheory.Loc.RootExistence in
theorem UpperTheory.ConvolutionTheory.Loc.rootEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ g ∈ ball n (r * valuation E (q : E)), ∃! u, u ∈ ball n r ∧ u ^ q = g := by
  intro E _ _ _ _ n q r hr g hg
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hr
  obtain ⟨u, hu, huq⟩ := exists_root q r hr (g : Matrix (Fin n) (Fin n) E) hg
  have hunit : IsUnit u := (isUnit_pow_iff hq).mp (huq ▸ g.isUnit)
  obtain ⟨w, rfl⟩ := hunit
  refine ⟨w, ⟨hu, Units.ext (by simpa using huq)⟩, fun w' hw' => Units.ext ?_⟩
  refine root_unique q r hr hw'.1 hu ?_
  rw [huq, ← hw'.2, Units.val_pow_eq_pow_val]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.UnitNorm
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem finiteField_norm_trace_surjective {k : Type} [Field k] [Finite k] (τ : k ≃+* k) (q : ℕ) (hq : orderOf τ = q) :
    (∀ u : k, τ u = u → ∃ w : k, ∏ i ∈ Finset.range q, (τ ^ i) w = u) ∧
      ∃ a : k, ∑ i ∈ Finset.range q, (τ ^ i) a = 1 := by
  classical
  subst hq
  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k)) DFunLike.coe_injective
  have hfin : IsOfFinOrder τ := isOfFinOrder_of_finite τ
  let G := Subgroup.zpowers τ
  let F := FixedPoints.subfield G k
  let e : Fin (orderOf τ) ≃ (k ≃ₐ[F] k) :=
    (finEquivZPowers hfin).trans (FixedPoints.toAlgAutMulEquiv G k).toEquiv
  have he : ∀ (i : Fin (orderOf τ)) (x : k), e i x = (τ ^ (i : ℕ)) x := fun i x => rfl
  constructor
  · intro u hu
    have hu' : u ∈ F := by
      rintro ⟨g, hg⟩
      have : Subgroup.zpowers τ ≤ MulAction.stabilizer (k ≃+* k) u := by
        rw [Subgroup.zpowers_le]; exact hu
      exact this hg
    obtain ⟨w, hw⟩ := FiniteField.norm_surjective F k ⟨u, hu'⟩
    refine ⟨w, ?_⟩
    have h := Algebra.norm_eq_prod_automorphisms F w
    rw [hw, ← e.prod_comp] at h
    rw [Finset.prod_range]
    exact h.symm
  · obtain ⟨w, hw⟩ := Algebra.trace_surjective F k 1
    refine ⟨w, ?_⟩
    have h := trace_eq_sum_automorphisms (K := F) w
    rw [hw, ← e.sum_comp, map_one] at h
    rw [Finset.sum_range]
    exact h.symm

private theorem unramified_norm_trace_surjective {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (σ : E ≃+* E) (q : ℕ) (h : Unram σ q) :
    (∀ u : E, valuation E u = 1 → σ u = u →
      ∃ w : E, valuation E w ≤ 1 ∧ valuation E (∏ i ∈ Finset.range q, σ^[i] w - u) < 1) ∧
      ∃ a : E, valuation E a ≤ 1 ∧ valuation E (∑ i ∈ Finset.range q, σ^[i] a - 1) < 1 := by
  let s : 𝒪[E] ≃+* 𝒪[E] := σ.restrict 𝒪[E] 𝒪[E] fun x => by
    simp only [Valuation.mem_integer_iff, h.isom x]
  have hs : ∀ x : 𝒪[E], ((s x : 𝒪[E]) : E) = σ x := fun x => rfl
  have hsi : ∀ (i : ℕ) (x : 𝒪[E]), ((s^[i] x : 𝒪[E]) : E) = σ^[i] x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  let τ : 𝓀[E] ≃+* 𝓀[E] := IsLocalRing.ResidueField.mapEquiv s
  have hτ : ∀ x : 𝒪[E], τ (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s x) := fun x => rfl
  have hτi : ∀ (i : ℕ) (x : 𝒪[E]), (τ ^ i) (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s^[i] x) := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih, hτ]
  have key : ∀ x y : 𝒪[E], IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔ valuation E ((x : E) - y) < 1 := by
    intro x y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rfl
  have hord : orderOf τ = q := by
    rw [orderOf_eq_iff h.pos]
    constructor
    · ext z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      rw [hτi]
      exact congrArg (IsLocalRing.residue 𝒪[E]) (Subtype.ext ((hsi q x).trans (h.ord x)))
    · intro m hm hm0 he
      obtain ⟨x, hx, hx'⟩ := h.res m hm0 hm
      have := hτi m ⟨x, hx⟩
      rw [he, RingAut.one_apply, eq_comm, key, hsi] at this
      exact this.ne hx'
  obtain ⟨h1, z, hz⟩ := finiteField_norm_trace_surjective τ q hord
  constructor
  · intro u hu hσ
    obtain ⟨z, hz⟩ := h1 (IsLocalRing.residue _ (⟨u, hu.le⟩ : 𝒪[E])) (by
      rw [hτ]; congr 1; exact Subtype.ext hσ)
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨x, x.2, ?_⟩
    simp only [hτi] at hz
    rw [← map_prod, key] at hz
    simpa only [SubmonoidClass.coe_finsetProd, hsi] using hz
  · obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨x, x.2, ?_⟩
    simp only [hτi] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_one (IsLocalRing.residue 𝒪[E]), key] at hz
    simpa only [AddSubmonoidClass.coe_finsetSum, hsi, OneMemClass.coe_one] using hz

private theorem prod_expand {E : Type} [Field E] [ValuativeRel E] (d : E) (hd : valuation E d ≤ 1) (x : ℕ → E)
    (hx : ∀ i, valuation E (x i) ≤ 1) (m : ℕ) :
    ∃ c : E, valuation E c ≤ 1 ∧
      ∏ i ∈ Finset.range m, (1 + d * x i) = 1 + d * ∑ i ∈ Finset.range m, x i + d ^ 2 * c := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc, he⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range m, x i) * x m + d * c * x m, ?_, ?_⟩
    · have hS : valuation E (∑ i ∈ Finset.range m, x i) ≤ 1 := Valuation.map_sum_le _ fun i _ => hx i
      refine Valuation.map_add_le _ (Valuation.map_add_le _ hc ?_) ?_
      · rw [map_mul]; exact mul_le_one' hS (hx m)
      · rw [map_mul, map_mul]; exact mul_le_one' (mul_le_one' hd hc) (hx m)
    · rw [Finset.prod_range_succ, Finset.sum_range_succ, he]; ring

open scoped WithZeroTopology in
theorem UpperTheory.ConvolutionTheory.Loc.unitNorm :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (σ : E ≃+* E) (q : ℕ), Unram σ q →
      ∀ u : E, valuation E u = 1 → σ u = u → ∃ w : E, valuation E w = 1 ∧ ∏ i ∈ Finset.range q, σ^[i] w = u := by
  intro E _ _ _ _ σ q h u hu hσu
  obtain ⟨hres, a, ha, hTa⟩ := unramified_norm_trace_surjective σ q h
  obtain ⟨w₀, hw₀, hNw₀⟩ := hres u hu hσu
  have hit : ∀ (i : ℕ) (x : E), σ^[i] x = (σ ^ i) x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih]
  have hiso : ∀ (i : ℕ) (x : E), valuation E (σ^[i] x) = valuation E x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', h.isom, ih]
  have hfix : ∀ (i : ℕ) (x : E), σ x = x → σ^[i] x = x := fun i x hx => Function.iterate_fixed hx i

  have hNfix : ∀ x : E, x ≠ 0 → σ (∏ i ∈ Finset.range q, σ^[i] x) = ∏ i ∈ Finset.range q, σ^[i] x := by
    intro x hx
    have e1 := Finset.prod_range_succ (fun i => σ^[i] x) q
    rw [Finset.prod_range_succ', h.ord] at e1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1
    rw [map_prod]
    exact mul_right_cancel₀ hx e1
  have hTfix : ∀ x : E, σ (∑ i ∈ Finset.range q, σ^[i] x) = ∑ i ∈ Finset.range q, σ^[i] x := by
    intro x
    have e1 := Finset.sum_range_succ (fun i => σ^[i] x) q
    rw [Finset.sum_range_succ', h.ord] at e1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact add_right_cancel e1
  have near : ∀ x y : E, valuation E y = 1 → valuation E (x - y) < 1 → valuation E x = 1 := by
    intro x y hy hxy
    rw [← hy] at hxy ⊢
    exact Valuation.map_eq_of_sub_lt _ hxy
  have hNv : ∀ x : E, valuation E (∏ i ∈ Finset.range q, σ^[i] x) = valuation E x ^ q := by
    intro x
    rw [map_prod]
    simp only [hiso, Finset.prod_const, Finset.card_range]

  obtain ⟨b, hb, hTb⟩ : ∃ b : E, valuation E b ≤ 1 ∧ ∑ i ∈ Finset.range q, σ^[i] b = 1 := by
    have hT1 := near _ _ (map_one _) hTa
    set T := ∑ i ∈ Finset.range q, σ^[i] a with hT
    have hT0 : T ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hT1
      exact zero_ne_one hT1
    refine ⟨a / T, by rw [map_div₀, hT1, div_one]; exact ha, ?_⟩
    have : ∀ i : ℕ, σ^[i] (a / T) = σ^[i] a / T := by
      intro i
      rw [hit, map_div₀, ← hit, ← hit, hfix i T (hTfix a)]
    simp only [this]
    rw [← Finset.sum_div, ← hT, div_self hT0]

  have hcσ : Continuous σ := by
    refine continuous_of_continuousAt_zero σ.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    refine ((IsValuativeTopology.hasBasis_nhds_zero E).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero E)).2 ?_
    intro γ _
    exact ⟨γ, trivial, fun x hx => (h.isom x).trans_lt hx⟩
  have hcont : Continuous fun x : E => valuation E (∏ i ∈ Finset.range q, σ^[i] x - u) :=
    IsValuativeTopology.continuous_valuation.comp
      ((continuous_finsetProd _ fun i _ => hcσ.iterate i).sub continuous_const)
  obtain ⟨w, hw, hmin⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall E 1).exists_isMinOn ⟨w₀, hw₀⟩ hcont.continuousOn
  have hlt : valuation E (∏ i ∈ Finset.range q, σ^[i] w - u) < 1 := lt_of_le_of_lt (hmin hw₀) hNw₀
  have hN1 := near _ _ hu hlt
  have hw1 : valuation E w = 1 := by
    rw [hNv] at hN1
    exact (pow_eq_one_iff_of_nonneg zero_le h.pos.ne').1 hN1
  refine ⟨w, hw1, ?_⟩
  by_contra hne
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hw1
    exact zero_ne_one hw1
  have hNσ := hNfix w hw0
  set N := ∏ i ∈ Finset.range q, σ^[i] w with hN
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN1
    exact zero_ne_one hN1
  set d := (u - N) / N with hd
  have hdσ : σ d = d := by rw [hd, map_div₀, map_sub, hσu, hNσ]
  have hdv : valuation E d = valuation E (N - u) := by
    rw [hd, map_div₀, hN1, div_one, Valuation.map_sub_swap]
  have hd1 : valuation E d < 1 := hdv ▸ hlt
  have hd0 : 0 < valuation E d := by
    rw [hdv, zero_lt_iff, Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  obtain ⟨c, hc, he⟩ := prod_expand d hd1.le (fun i => σ^[i] b) (fun i => (hiso i b).trans_le hb) q
  have hw' : valuation E (w * (1 + d * b)) ≤ 1 := by
    rw [map_mul, hw1, one_mul]
    refine Valuation.map_add_le _ (map_one _).le ?_
    rw [map_mul]; exact mul_le_one' hd1.le hb
  have hle : valuation E (N - u) ≤ valuation E (∏ i ∈ Finset.range q, σ^[i] (w * (1 + d * b)) - u) := hmin hw'
  have e1 : ∀ i : ℕ, σ^[i] (w * (1 + d * b)) = σ^[i] w * (1 + d * σ^[i] b) := by
    intro i
    rw [hit, map_mul, map_add (f := _), map_one, map_mul, ← hit, ← hit, ← hit, hfix i d hdσ]
  simp only [e1] at hle
  rw [Finset.prod_mul_distrib, he, hTb, ← hN, ← hdv] at hle
  have e2 : N * (1 + d * 1 + d ^ 2 * c) - u = N * (d * (d * c)) := by
    have : u = N * (1 + d) := by rw [hd]; field_simp; ring
    rw [this]; ring
  rw [e2, map_mul, hN1, one_mul, map_mul, map_mul] at hle
  have : valuation E d * (valuation E d * valuation E c) < valuation E d :=
    mul_lt_of_lt_one_right hd0 (lt_of_le_of_lt (mul_le_of_le_one_right' hc) hd1)
  exact absurd hle this.not_ge
end

