module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonarchimedeanLocalFieldSecondCountableT2Space
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise

namespace GlobalTheory.RootExchangeFixed

section alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem lowU_neg_mul (C : Matrix (Fin c) n k) : lowU (-C) * lowU C = 1 := by
  ext1
  simp [lowU, fromBlocks_multiply]

theorem conj_val (C : Matrix (Fin c) n k) (B : Matrix n (Fin c) k) (h : B * C = 0) :
    (lowU C * upU B * lowU (-C)).val = fromBlocks 1 B 0 (C * B + 1) := by
  simp [lowU, upU, fromBlocks_multiply, h, Matrix.add_mul, Matrix.mul_assoc]

theorem exists_conj (h1 : 1 ≤ p) (hc : p < c) (u β : n → k) :
    ∃ g ∈ N k n c p, simpleSum g = ∑ r, u r * β r ∧
      rowE c p u * colE c (p + 1) β = g * rowE c p u := by
  set C : Matrix (Fin c) n k := Matrix.of fun l s => if l.val + 1 = p then u s else 0 with hC
  set B : Matrix n (Fin c) k := Matrix.of fun r i => if i.val + 1 = p + 1 then β r else 0 with hB
  have hBC : B * C = 0 := by
    ext r s
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with a b
    · omega
    all_goals simp
  have hCB : ∀ l i, (C * B) l i = if l.val + 1 = p ∧ i.val = p then ∑ r, u r * β r else 0 := by
    intro l i
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply]
    by_cases a : l.val + 1 = p <;> by_cases b : i.val = p <;> simp [a, b]
  have hv := conj_val C B hBC
  refine ⟨lowU C * upU B * lowU (-C), Subgroup.subset_closure ?_, ?_, ?_⟩
  · intro r s hrs
    rw [hv]
    rcases r with r | r <;> rcases s with s | s
    · simp [Matrix.one_apply]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₁₂, hB, Matrix.of_apply]
      rw [if_neg (by omega)]; simp
    · simp
    · simp only [lev, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
      rw [if_neg (by omega)]; simp [Matrix.one_apply]
  · unfold simpleSum
    rw [hv]
    simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
    rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), Finset.sum_eq_single (⟨p, hc⟩ : Fin c)]
    · rw [if_pos (by simp; omega), if_pos (by simp; omega), Matrix.one_apply_ne, add_zero]
      intro h
      have := congrArg Fin.val h
      simp at this; omega
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      ext
      simp at h ⊢; omega
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with a b
      · exfalso
        apply hi
        ext
        simp; omega
      · rw [Matrix.one_apply_ne, add_zero]
        intro h
        have := congrArg Fin.val h
        omega
      · rfl
    · simp
  · show lowU C * upU B = _ * lowU C
    rw [mul_assoc, lowU_neg_mul, mul_one]

end alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lowU_mem_KO {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix (Fin c) n k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : lowU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix (Fin c) n 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 0 C' 1, fromBlocks 1 0 (-C') 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [lowU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)

theorem upU_mem_KO {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix n (Fin c) k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : upU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix n (Fin c) 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 C' 0 1, fromBlocks 1 (-C') 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [upU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)

theorem nonarchimedeanLocalField_secondCountable_t2Space : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem vanish {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (u : n → k) (r : n) (hr : ¬ valuation k (u r) ≤ valuation k (s : k)) :
    l (σ (rowE c p u) v) = 0 := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  have hu : 0 < valuation k (u r) := hs.trans (not_le.1 hr)
  have hu0 : u r ≠ 0 := by rintro h; simp [h] at hu
  have hx : ¬ valuation k (u r / s) ≤ valuation k ((1 : kˣ) : k) := by
    rw [map_div₀, div_le_iff₀ hs]; simpa using hr
  rw [← hψ] at hx
  push Not at hx
  obtain ⟨y, hy, hy1⟩ := hx
  obtain ⟨g, hg, hsum, hmul⟩ := exists_conj h1 hc u (Pi.single r (y / u r))
  have hfix := hβ (Pi.single r (y / u r)) (by
    intro t
    by_cases ht : t = r
    · subst ht
      rw [map_div₀, le_div_iff₀ hs] at hy
      rw [Pi.single_eq_same, map_mul, map_div₀, div_mul_eq_mul_div, div_le_iff₀ hu, one_mul]
      exact hy
    · simp [Pi.single_eq_of_ne ht])
  have hy' : simpleSum g = y := by
    rw [hsum, Finset.sum_eq_single r]
    · simp only [Pi.single_eq_same]; field_simp
    · intro t _ ht; simp [Pi.single_eq_of_ne ht]
    · simp
  have key : l (σ (rowE c p u) v) = (ψ y : ℂ) * l (σ (rowE c p u) v) := by
    conv_lhs => rw [← hfix]
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply, hl g hg, hy']
  by_contra hne
  apply hy1
  have : (ψ y : ℂ) = 1 := by
    have h2 : (ψ y : ℂ) * l (σ (rowE c p u) v) = 1 * l (σ (rowE c p u) v) := by
      rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hne h2
  exact Circle.ext (by simpa using this)

variable [MeasurableSpace k] [BorelSpace k]

theorem ball_eq (s : kˣ) : {x : k | valuation k x ≤ valuation k (s : k)} = s • (𝒪[k] : Set k) := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show _ ↔ valuation k (((s⁻¹ : kˣ) : k) * x) ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hs, mul_one]
  rfl

theorem meas_ball (s : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (s : k)} := by
  rw [ball_eq]
  refine (IsOpen.smul ?_ s).measurableSet
  exact Valuation.isOpen_integer

theorem vol_ball (ν : Measure k) (hν : IsUnitVol ν) (s : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (s : k)} = ENNReal.ofReal (nabs k s) := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  rw [ball_eq, ← distribHaarChar_mul ν s, hν.2, nabs]
  simp

theorem exUp_of_fixed {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) (hν : IsUnitVol ν)
    {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (hu : ∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) :
    exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  let S : Set (n → k) := Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k (s : k)}
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => meas_ball s
  have hf : (fun u : n → k => l (σ (rowE c p u) v)) = S.indicator fun _ => l v := by
    funext u
    by_cases h : u ∈ S
    · rw [Set.indicator_of_mem h, hu u fun r => h r trivial]
    · rw [Set.indicator_of_notMem h]
      simp only [S, Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
      obtain ⟨r, hr⟩ := h
      exact vanish h1 hc hψ σ l hl v s hβ u r hr
  have hn : 0 ≤ nabs k s := NNReal.coe_nonneg _
  unfold exUp
  rw [hf, integral_indicator_const _ hS, Measure.real, Measure.pi_pi]
  simp [vol_ball ν hν s, hn]

theorem exUp_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ p σ l) (v : A), (∀ s : kˣ, (∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v) → (∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) → exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v) ∧ ((∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → exUp ν p σ l v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hc ψ hψ ν hν A _ _ σ l hl v
  refine ⟨fun s hβ hu => exUp_of_fixed h1 hc hψ ν hν σ l hl v s hβ hu, fun hK => ?_⟩
  rw [exUp_of_fixed h1 hc hψ ν hν σ l hl v 1]
  · simp [nabs]
  · intro β h
    refine hK _ (upU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h r
    · simp
  · intro u h
    refine hK _ (lowU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h i
    · simp

end GlobalTheory.RootExchangeFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

theorem nabs_le_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    nabs k x ≤ nabs k y := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have hx := measureReal_cball ν x
  have hy := measureReal_cball ν y
  have h2 : ν.real (𝒪[k] : Set k) = 1 := by rw [Measure.real, h1]; simp
  rw [h2, mul_one] at hx hy
  rw [← hx, ← hy]
  have h3 : cball x ⊆ cball y := fun z hz => le_trans (show valuation k z ≤ _ from hz) h
  exact measureReal_mono h3 (isCompact_cball y).measure_lt_top.ne

theorem nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k

theorem nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩

theorem nabs_eq_iff (x y : kˣ) : nabs k x = nabs k y ↔ valuation k (x : k) = valuation k (y : k) := by
  rw [le_antisymm_iff, le_antisymm_iff, nabs_le_iff, nabs_le_iff]

theorem nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by
  rw [← nabs_one k, nabs_eq_iff, Units.val_one, map_one]

variable (k) in
theorem isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdNBlockTriangular
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

section
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem prodN_mul_apply {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem prodN_blockTriangular {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) :
    g.val.BlockTriangular (lev p) := by
  intro i j hij
  rw [hg i j hij.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem prodN_inN_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : InN p g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro r s _; simp
  | mul x y _ _ hx hy =>
    intro r s hrs
    rw [Units.val_mul, prodN_mul_apply (prodN_blockTriangular hx) hy r s hrs]
    exact hx r s hrs
  | inv x _ hx =>
    intro r s hrs
    have : Invertible x.val := ⟨x.inv, x.inv_val, x.val_inv⟩
    have hb : (x⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (prodN_blockTriangular hx)
    have key := prodN_mul_apply hb hx r s hrs
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, eq_comm] at key

end

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIsotropicOrOneClass
section
open scoped Matrix

namespace GlobalTheory.UTrans

open GlobalTheory.UTrans.Calc

private theorem sigma_hf_eq_hf_swap {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x y : Fin n → R) : σ (GlobalTheory.UTrans.hf σ G x y) = GlobalTheory.UTrans.hf σ G y x := by
  unfold GlobalTheory.UTrans.hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private theorem hf_add_smul_self {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (x + c • y) (x + c • y) = GlobalTheory.UTrans.hf σ G x x
      + c * (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y) + c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hc, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private theorem exists_eq_algebraMap_of_fixed' {K L : Type} [Field K] [Field L] [CharZero L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (z : L) (hz : σ z = z) : ∃ k : K, z = algebraMap K L k := by
  obtain ⟨a, b, rfl⟩ := hspan z
  refine ⟨a, ?_⟩
  rw [map_add (f := _), map_mul, hK, hK, hσδ] at hz
  have h2 : (2 : L) * (algebraMap K L b * δ) = 0 := by linear_combination -hz
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · rw [h, add_zero]

private theorem involutive_of_anti_fixed_generator {K L : Type} [Field K] [Field L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (x : L) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := hspan x
  simp only [map_add (f := _), map_mul, hK, hσδ, map_neg, neg_neg]

private theorem hf_smul_smul' {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (c • y) (c • y) = c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem real_isotropic_or_one_class : ∀ (K L : Type) [Field K] [Field L] [CharZero L] [Algebra K L] (σ : L →+* L) (δ : L), (∀ a : K, σ (algebraMap K L a) = algebraMap K L a) → δ ≠ 0 → σ δ = -δ → (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ) → Nonempty (K ≃+* ℝ) → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) L), (∀ a b, σ (G a b) = G b a) → (∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → L, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : L, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x := by
  intro K L _ _ _ _ σ δ hK hδ hσδ hspan ⟨e⟩ n G hG
  have hσ : ∀ a : L, σ (σ a) = a := involutive_of_anti_fixed_generator σ δ hK hσδ hspan
  have hfix : ∀ z : L, σ z = z → ∃ k : K, z = algebraMap K L k :=
    exists_eq_algebraMap_of_fixed' σ δ hK hσδ hspan
  by_cases hiso : ∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0
  · exact Or.inl hiso
  right
  push_neg at hiso
  intro x y hx hy
  obtain ⟨p, hp⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG x x)
  obtain ⟨q, hq⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG y y)
  obtain ⟨m, hm⟩ := hfix (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y)
    (by rw [map_add (f := _), sigma_hf_eq_hf_swap σ G hσ hG, sigma_hf_eq_hf_swap σ G hσ hG, add_comm])
  have hp0 : e p ≠ 0 := by
    intro h
    apply hx
    rw [hp, (map_eq_zero_iff e e.injective).mp h, map_zero]
  have hq0 : e q ≠ 0 := by
    intro h
    apply hy
    rw [hq, (map_eq_zero_iff e e.injective).mp h, map_zero]

  have hpos : 0 < e q / e p := by
    by_contra hneg
    push_neg at hneg
    have hlt : e q * e p < 0 := by
      have h1 : e q / e p < 0 := lt_of_le_of_ne hneg (div_ne_zero hq0 hp0)
      have h2 : e q * e p = e q / e p * (e p * e p) := by field_simp
      rw [h2]
      exact mul_neg_of_neg_of_pos h1 (mul_self_pos.mpr hp0)
    have hd : 0 ≤ discrim (e q) (e m) (e p) := by
      unfold discrim
      nlinarith [sq_nonneg (e m)]
    have hs : discrim (e q) (e m) (e p) = Real.sqrt (discrim (e q) (e m) (e p))
        * Real.sqrt (discrim (e q) (e m) (e p)) := (Real.mul_self_sqrt hd).symm
    have ht := (quadratic_eq_zero_iff hq0 hs ((-(e m) + Real.sqrt (discrim (e q) (e m) (e p)))
      / (2 * e q))).mpr (Or.inl rfl)
    set t : ℝ := (-(e m) + Real.sqrt (discrim (e q) (e m) (e p))) / (2 * e q) with ht_def
    have hT : q * (e.symm t * e.symm t) + m * e.symm t + p = 0 := by
      apply e.injective
      simp only [map_add (f := _), map_mul, RingEquiv.apply_symm_apply, map_zero]
      linear_combination ht
    have hTK : σ (algebraMap K L (e.symm t)) = algebraMap K L (e.symm t) := hK _
    apply hiso (x + algebraMap K L (e.symm t) • y)
    · intro h0
      have hx' : x = (-(algebraMap K L (e.symm t))) • y := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left h0
      have hxx := hf_smul_smul' σ G y (-(algebraMap K L (e.symm t))) (by rw [map_neg, hTK])
      rw [← hx', hp, hq, neg_mul_neg, ← map_mul, ← map_mul] at hxx
      have hpk := congrArg e ((algebraMap K L).injective hxx)
      simp only [map_mul, RingEquiv.apply_symm_apply] at hpk
      rw [hpk] at hlt
      nlinarith [mul_self_nonneg (t * e q)]
    · rw [hf_add_smul_self σ G x y _ hTK, hm, hp, hq, ← map_mul, ← map_mul, ← map_mul, ← map_add (f := _),
        ← map_add, ← map_zero (algebraMap K L)]
      congr 1
      linear_combination hT

  refine ⟨algebraMap K L (e.symm (Real.sqrt (e q / e p))), ?_⟩
  rw [hK, hp, hq, ← map_mul, ← map_mul]
  congr 1
  apply e.injective
  simp only [map_mul, RingEquiv.apply_symm_apply]
  rw [Real.mul_self_sqrt hpos.le]
  field_simp

end GlobalTheory.UTrans
end

