module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeAction
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem free_mod_eq {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ)
    (a γ γ' : G) (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) (i j : ℕ)
    (h : γ * a * g ^ i = γ' * a * g ^ j) : i % m = j % m := by
  have key : ∀ (γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ i j : ℕ, i < j → j < m →
      γ * a * g ^ i ≠ γ' * a * g ^ j := by
    intro γ γ' hγ hγ' i j hij hj h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    apply hfree a (d + 1) (by omega) (by omega)
    have e : a * g ^ (d + 1) * a⁻¹ = γ'⁻¹ * γ := by
      have h2 : γ * a * g ^ i = (γ' * a * g ^ (d + 1)) * g ^ i := by
        rw [h, mul_assoc (γ' * a), ← pow_add]
        congr 2
        omega
      have h3 := mul_right_cancel h2
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, ← h3, mul_inv_cancel_right]
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem hγ') hγ
  rw [pow_eq_pow_mod i hg, pow_eq_pow_mod j hg] at h
  rcases lt_trichotomy (i % m) (j % m) with hlt | heq | hlt
  · exact absurd h (key γ γ' hγ hγ' _ _ hlt (Nat.mod_lt _ hm))
  · exact heq
  · exact absurd h.symm (key γ' γ hγ' hγ _ _ hlt (Nat.mod_lt _ hm))

def freeSetoid {G : Type} [Group G] (Γ : Subgroup G) (g : G) (m : ℕ) (hm : 0 < m)
    (hg : g ^ m = 1) : Setoid G where
  r x y := ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k
  iseqv :=
    { refl := fun x => ⟨1, Γ.one_mem, 0, by simp⟩
      symm := by
        rintro x y ⟨γ, hγ, k, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k * (m - 1), ?_⟩
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
        have : g ^ k * g ^ (k * (0 + n + 1 - 1)) = 1 := by
          rw [← pow_add]
          have : k + k * (0 + n + 1 - 1) = (0 + n + 1) * k := by
            simp only [zero_add, Nat.add_sub_cancel]
            ring
          rw [this, pow_mul, hg, one_pow]
        rw [mul_assoc, mul_assoc, this, mul_one, inv_mul_cancel_left]
      trans := by
        rintro x y z ⟨γ, hγ, k, rfl⟩ ⟨δ, hδ, l, rfl⟩
        refine ⟨δ * γ, Γ.mul_mem hδ hγ, k + l, ?_⟩
        simp only [pow_add, mul_assoc] }

theorem twInv_apply_pow {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    {Γ : Subgroup G} {g : G} {A : E →ₗ[ℂ] E} {f : G → E} (hf : f ∈ twInv Γ g A) (x : G) (k : ℕ) :
    f (x * g ^ k) = (A ^ k) (f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, hf.2, ih, pow_succ', Module.End.mul_apply]

theorem finrank_twInv_mul_of_free {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ) (hΓ : Γ.FiniteIndex)
    (hE : FiniteDimensional ℂ E) (hm : 0 < m) (hg : g ^ m = 1) (hA : A ^ m = 1)
    (hfree : ∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) :
    FiniteDimensional ℂ (twInv Γ g A) ∧
      Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  classical
  let s := freeSetoid Γ g m hm hg
  have hs : ∀ x y : G, s.r x y ↔ ∃ γ ∈ Γ, ∃ k : ℕ, y = γ * x * g ^ k := fun _ _ => Iff.rfl
  let R := Quotient s
  have hmk : ∀ γ ∈ Γ, ∀ (x : G) (k : ℕ), Quotient.mk s (γ * x * g ^ k) = Quotient.mk s x :=
    fun γ hγ x k => (Quotient.sound (s := s) ((hs _ _).2 ⟨γ, hγ, k, rfl⟩)).symm
  have hout : ∀ x : G, ∃ γ ∈ Γ, ∃ k : ℕ, x = γ * (Quotient.mk s x).out * g ^ k :=
    fun x => (hs _ _).1 (Quotient.mk_out (s := s) x)

  let F : R × Fin m → Quotient (QuotientGroup.rightRel Γ) :=
    fun p => Quotient.mk _ (p.1.out * g ^ (p.2 : ℕ))
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ h
      have h1 := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
      dsimp only at h1
      set γ := d.out * g ^ (j : ℕ) * (c.out * g ^ (i : ℕ))⁻¹ with hγ
      have h2 : 1 * d.out * g ^ (j : ℕ) = γ * c.out * g ^ (i : ℕ) := by
        rw [hγ, mul_assoc _ c.out, inv_mul_cancel_right, one_mul]
      have h3 : d = c := by
        have := congrArg (Quotient.mk s) h2
        rw [hmk 1 Γ.one_mem, hmk γ h1, Quotient.out_eq, Quotient.out_eq] at this
        exact this
      subst h3
      have h4 := free_mod_eq Γ g m hm hg hfree _ _ _ Γ.one_mem h1 _ _ h2
      rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at h4
      rw [Fin.ext h4]
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        obtain ⟨γ, hγ, k, hx⟩ := hout x
        refine ⟨(Quotient.mk s x, ⟨k % m, Nat.mod_lt _ hm⟩), ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.2
        dsimp only
        rw [← pow_eq_pow_mod k hg]
        have : x * ((Quotient.mk s x).out * g ^ k)⁻¹ = γ := by
          rw [mul_inv_eq_iff_eq_mul, ← mul_assoc]
          exact hx
        rw [this]
        exact hγ
  have hcard : Nat.card R * m = Γ.index := by
    have h1 := Nat.card_congr (Equiv.ofBijective F hF)
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)] at h1
    exact h1
  have hR : Finite R := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_mul] at hcard
    exact hΓ.index_ne_zero hcard.symm
  letI : Fintype R := Fintype.ofFinite R

  let ev : twInv Γ g A →ₗ[ℂ] (R → E) :=
    { toFun := fun f c => (f : G → E) c.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    constructor
    · intro f f' h
      apply Subtype.ext
      funext x
      obtain ⟨γ, hγ, k, hx⟩ := hout x
      have h1 : (f : G → E) (Quotient.mk s x).out = (f' : G → E) (Quotient.mk s x).out :=
        congrFun h (Quotient.mk s x)
      rw [hx, twInv_apply_pow f.2, twInv_apply_pow f'.2, f.2.1 γ hγ, f'.2.1 γ hγ, h1]
    · intro φ
      choose γ hγ κ hκ using hout
      have hval : ∀ (x δ : G) (k : ℕ), δ ∈ Γ → x = δ * (Quotient.mk s x).out * g ^ k →
          A ^ κ x = A ^ k := by
        intro x δ k hδ hx
        have := free_mod_eq Γ g m hm hg hfree _ _ _ (hγ x) hδ _ _ ((hκ x).symm.trans hx)
        rw [pow_eq_pow_mod _ hA, this, ← pow_eq_pow_mod _ hA]
      refine ⟨⟨fun x => (A ^ κ x) (φ (Quotient.mk s x)), ?_, ?_⟩, ?_⟩
      · intro δ hδ x
        have e : Quotient.mk s (δ * x) = Quotient.mk s x := by
          simpa using hmk δ hδ x 0
        have := hval (δ * x) (δ * γ x) (κ x) (Γ.mul_mem hδ (hγ x)) (by
          rw [e, mul_assoc, mul_assoc δ, ← mul_assoc (γ x), ← hκ x])
        dsimp only
        rw [this, e]
      · intro x
        have e : Quotient.mk s (x * g) = Quotient.mk s x := by
          simpa using hmk 1 Γ.one_mem x 1
        have := hval (x * g) (γ x) (κ x + 1) (hγ x) (by
          rw [e, pow_succ, ← mul_assoc, ← hκ x])
        dsimp only
        rw [this, e, pow_succ', Module.End.mul_apply]
      · funext c
        have := hval c.out 1 0 Γ.one_mem (by rw [Quotient.out_eq]; simp)
        change (A ^ κ c.out) (φ (Quotient.mk s c.out)) = φ c
        rw [this, Quotient.out_eq]
        simp
  let e := LinearEquiv.ofBijective ev hev
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ← hcard]
  ring

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := _root_.GlobalTheory.sepFamily_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one₀ (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixingSubgroupOfIntermediateFieldProperties
section
open Polynomial

noncomputable section

namespace GlobalTheory.K4.Geo

open Topology GlobalTheory.NeedB

theorem mem_fixingSubgroup_adjoin_of {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (S : Set Ω)
    (g : Ω ≃ₐ[k] Ω) (hg : ∀ x ∈ S, g x = x) : g ∈ (IntermediateField.adjoin k S).fixingSubgroup := by
  have hle : IntermediateField.adjoin k S ≤ IntermediateField.fixedField (fixingSubgroup (Ω ≃ₐ[k] Ω) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((mem_fixingSubgroup_iff _).2 fun x hx => hg x hx)

theorem valuation_lt_one_iff' {Ω : Type} [Field Ω] (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  by_cases hy : y = 0
  · simp [hy]
  · have h0 : B.valuation y ≠ 0 := by simpa using hy
    rw [← B.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
    simp [hy, not_le]

variable (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω]

def equiv : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω where
  toFun g := ⟨g.restrictScalars F, (GlobalTheory.K4.TopW.mem_geo (K := K) _).2 fun z => g.commutes z⟩
  invFun h := AlgEquiv.ofRingEquiv (f := (h : Ω ≃ₐ[F] Ω).toRingEquiv)
    (fun z => (GlobalTheory.K4.TopW.mem_geo (K := K) _).1 h.2 z)
  left_inv g := by ext x; rfl
  right_inv h := by ext x; rfl
  map_mul' g g' := by ext x; rfl

variable [Algebra.IsAlgebraic F Ω]

theorem continuous_restrict :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  have hfd : FiniteDimensional K (IntermediateField.adjoin K (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine Filter.mem_of_superset ((IntermediateField.adjoin K (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _)) ?_
  intro g hg
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_symm : Continuous (equiv F K Ω).symm := by
  apply continuous_of_continuousAt_one (equiv F K Ω).symm
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  have hfd : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine (mem_nhds_subtype _ _ _).2 ⟨_, (IntermediateField.adjoin F (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _), ?_⟩
  intro h hh
  simp only [Set.mem_preimage] at hh ⊢
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_equiv : Continuous (equiv F K Ω) :=
  continuous_induced_rng.2 (continuous_restrict F K Ω)

end GlobalTheory.K4.Geo

theorem GlobalTheory.K4.geo_facts : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  intro F K Ω _ _ _ _ _ _ _ _
  refine ⟨fun g => GlobalTheory.K4.TopW.mem_geo g, ⟨GlobalTheory.K4.Geo.equiv F K Ω, fun g x => rfl, GlobalTheory.K4.Geo.continuous_equiv F K Ω,
    GlobalTheory.K4.Geo.continuous_symm F K Ω⟩, fun _ => ⟨fun n hn g => GlobalTheory.K4.TopW.conj_mem_geo g hn⟩, fun _ => ?_, ?_⟩
  · have hr : (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω)) =
        Set.range (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
      ext h
      constructor
      · intro hh
        exact ⟨(GlobalTheory.K4.Geo.equiv F K Ω).symm ⟨h, hh⟩, AlgEquiv.ext fun _ => rfl⟩
      · rintro ⟨g, rfl⟩
        exact (GlobalTheory.K4.Geo.equiv F K Ω g).2
    rw [hr]
    exact isCompact_range (GlobalTheory.K4.Geo.continuous_restrict F K Ω)
  · intro B r g hr x hx
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap] at hx
    have h1 := hr _ ((B.valuation_le_one_iff _).2 hx)
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff'] at h1
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff']
    have key : (g : Ω →+* Ω) ((g⁻¹ * r * g) x - x) = r ((g : Ω →+* Ω) x) - (g : Ω →+* Ω) x := by
      simp [AlgEquiv.mul_apply]
    rcases h1 with h0 | h0
    · left
      apply g.injective
      have : g ((g⁻¹ * r * g) x - x) = 0 := by simpa using key.trans h0
      rw [this, map_zero]
    · right
      intro hm
      apply h0
      rw [ValuationSubring.mem_comap, map_inv₀, key] at hm
      exact hm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZpStatement
section
open GlobalTheory.K5

private theorem mem_geoField_of_fixed_local {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (O0 p) Ω] (h : IsClo p Ω) (x : Ω)
    (hx : ∀ g ∈ Ggeo (p := p) Ω, g x = x) :
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y}) := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let F : Subfield Ω := Subfield.closure
    (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y})
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ F := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hR
  have hf : (algebraMap F Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  have hAlg : Algebra.IsAlgebraic F Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  letI : Algebra.IsAlgebraic F Ω := hAlg
  haveI : IsAlgClosure F Ω := ⟨h.clo, hAlg⟩
  haveI : CharZero F := ⟨fun m n e => CharZero.cast_injective (congrArg Subtype.val e)⟩
  haveI : IsGalois F Ω := inferInstance
  have hbot : x ∈ (⊥ : IntermediateField F Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo (p := p) Ω := fun y hy =>
      σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo (p := p) Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p hp Ω hΩ hΩalg h x hx
  obtain ⟨S, hS, hxS⟩ := GlobalTheory.K5.GeoFix.exists_finset_of_mem_closure _ _
    (mem_geoField_of_fixed_local h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiag
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulF_eq_trOld (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) :
    0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) •
      (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  intro hl hB
  let ε : SL(2, ℤ) := ⟨!![(l : ℤ), a; (N : ℤ), b], by rw [Matrix.det_fin_two_of]; linear_combination h⟩
  have hε : ε ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [ε]
  have hεB : B ∣[k] toGL (mat ε) = χ (b : ZMod N) • B := by
    rw [← slash_SL_eq, hB ε hε]; rfl
  let u : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]
  have hu : ∀ j, 0 < (u j).det := by
    intro j; simp [u, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hD : (dg (l : ℤ) 1).det ≠ 0 := by
    simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl.ne'
  have key : ∀ j : ℕ, (B ∣[k] toGL (dg l 1)) ∣[k] gaOld N l a b h j =
      χ (b : ZMod N) • (B ∣[k] toGL (u j)) := by
    intro j
    have hg : (mat (gaOld N l a b h j)).det ≠ 0 := by simp [mat]
    have hεd : (mat ε).det ≠ 0 := by simp [mat]
    have hm : dg (l : ℤ) 1 * mat (gaOld N l a b h j) = mat ε * u j := by
      ext i i' <;> fin_cases i <;> fin_cases i' <;>
        simp [dg, gaOld, mat, ε, u, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hg, hm, toGL_mul _ _ hεd (hu j).ne',
      SlashAction.slash_mul, hεB, smul_slash_toGL k _ (hu j)]
  have hsum : trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1) =
      χ (b : ZMod N) • UlF k l B := by
    rw [trOld, add_sub_cancel_left, UlF, hkF, Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    exact (Fin.sum_univ_eq_sum_range (fun j => χ (b : ZMod N) • (B ∣[k] toGL (u j))) l).symm
  have hlb : (l : ZMod N) * (b : ZMod N) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod N)) h
    push_cast at this
    simpa [ZMod.natCast_self] using this
  rw [hsum, smul_smul, ← map_mul, hlb, map_one, one_smul]

end GlobalTheory.HeckeFamilyMatrices
end

