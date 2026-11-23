module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0107
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurableStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
namespace ContractingCosetsPort
open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractingCosets
variable {k : Type} [Field k] [ValuativeRel k]

theorem coe_leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : Matrix (Fin N) (Fin N) k) =
      diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      simp only [Zl.JC.zj, Zl.JC.blockIdx, Equiv.symm_apply_apply]
      split_ifs <;> simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      simp only [Zl.JC.zj]
      split_ifs
      · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, diagonal_apply_ne _ hil]
      · simp [Matrix.one_apply_ne hil]
  · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, l⟩ := fun e =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem le_of_mk_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hpos : ∀ a, 0 < d a) (t : kˣ)
    (ht : valuation k (t : k) < 1) (j : Fin h) (hj : j.val + 1 < h) (m : ℕ)
    {x y x' y' : GL (Fin N) k} (hx : x ∈ congruenceSubgroup k N m)
    (hy : y ∈ congruenceSubgroup k N m) (hx' : x' ∈ congruenceSubgroup k N m)
    (hy' : y' ∈ congruenceSubgroup k N m) {r r' : ℕ}
    (e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
      QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y')) :
    r' ≤ r := by
  have hz := QuotientGroup.eq.1 e
  have hK := congruenceSubgroup_le k N m
  have heq := eq_central_mul hz
  refine le_of_eq_central_mul (δ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1) t ht
    (fun i => ?_) (i₁ := stdBlocks d hd ⟨j, ⟨0, hpos j⟩⟩)
    (i₂ := stdBlocks d hd ⟨⟨j.val + 1, hj⟩, ⟨0, hpos _⟩⟩) ?_ ?_
    (coe_leviEmb_zj d hd t j)
    (mul_mem (inv_mem (hK hx')) (hK hx)) (mul_mem (hK hy) (inv_mem (hK hy'))) hz heq
  · by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · simp [Zl.JC.blockIdx]
  · have : ¬ (⟨j.val + 1, hj⟩ : Fin h) ≤ j := by
      rw [Fin.le_def]; simp
    simp [Zl.JC.blockIdx, this]

end ContractingCosetsPort

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_double_coset_measurable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (GlobalTheory.CompanionTheory.ContractingCosets.isOpen_doubleCoset _
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBound
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ContractVolume

open ValuativeRel Matrix MeasureTheory GroundTheory.Automorphic.GLnLocal

theorem sum_modExp {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    (∑ a, if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a, if a ≤ j then (d a : ℤ) else 0) * ∑ b, if j < b then (d b : ℤ) else 0 := by
  classical
  set T : ℤ := ∑ a, ∑ b, if a ≤ j ∧ b ≤ j then
    (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0 with hT
  have hT0 : T = 0 := by
    have h1 : T = -T := by
      conv_lhs => rw [hT, Finset.sum_comm]
      rw [hT, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a ≤ j ∧ b ≤ j
      · rw [if_pos hab, if_pos hab.symm]; ring
      · rw [if_neg hab, if_neg (fun h => hab h.symm)]; simp
    omega
  have h2 : ∀ a : Fin h, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ b, if a ≤ j ∧ b ≤ j then
        (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0) +
      (if a ≤ j then (d a : ℤ) else 0) * ∑ b, if j < b then (d b : ℤ) else 0 := by
    intro a
    by_cases ha : a ≤ j
    · simp only [ha, if_true, true_and]
      rw [modExp, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fintype.card_fin]
      by_cases hb : b ≤ j
      · have hb' : ¬ j < b := not_lt.2 hb
        simp only [hb, hb', if_true, if_false]
        split_ifs <;> ring
      · have hb' : j < b := not_le.1 hb
        have h3 : a < b := lt_of_le_of_lt ha hb'
        simp [hb, hb', h3, h3.le, not_lt.2 h3.le]
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_add_distrib, ← hT, hT0, zero_add,
    Finset.sum_mul]

theorem sum_toNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (j : Fin h) (n : ℕ) :
    (∑ i : Fin N, ∑ l : Fin N, if i < l then
      ((if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0) -
        (if Zl.JC.blockIdx d hd l ≤ j then (n : ℤ) else 0)).toNat else 0) =
      n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0) := by
  classical
  have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd
  have h1 : ∀ i l : Fin N, (if i < l then
      ((if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0) -
        (if Zl.JC.blockIdx d hd l ≤ j then (n : ℤ) else 0)).toNat else 0) =
      n * ((if Zl.JC.blockIdx d hd i ≤ j then 1 else 0) *
        (if j < Zl.JC.blockIdx d hd l then 1 else 0)) := by
    intro i l
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · by_cases hl : j < Zl.JC.blockIdx d hd l
      · have hil : i < l := by
          by_contra hc
          exact absurd (hmono (not_lt.1 hc)) (not_le.2 (lt_of_le_of_lt hi hl))
        simp [hi, hl, hil, not_le.2 hl]
      · have hl' := not_lt.1 hl
        simp [hi, hl, hl']
    · by_cases hl : j < Zl.JC.blockIdx d hd l
      · simp [hi, not_le.2 hl]
      · have hl' := not_lt.1 hl
        simp only [hi, hl', if_true, if_false, hl]
        split_ifs <;> simp
  have h2 : ∀ P : Fin h → Prop, [DecidablePred P] → (∑ i : Fin N, if P (Zl.JC.blockIdx d hd i) then 1 else 0) =
      ∑ a, if P a then d a else 0 := by
    intro P _
    rw [← Equiv.sum_comp (stdBlocks d hd), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Zl.JC.blockIdx]
  simp only [h1]
  rw [← h2, ← h2, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

theorem coe_congruenceSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) (hm : 1 ≤ m) :
    (congruenceSubgroup k N m : Set (GL (Fin N) k)) =
      {g : GL (Fin N) k | ∀ i j, valuation k
        ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
          valuation k (((uniformizer k : 𝒪[k]) : k) ^ m)} := by
  have hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0 :=
    (Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)
  have hlt : valuation k (((uniformizer k : 𝒪[k]) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' (valuation_uniformizer_lt_one k) (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N _ (pow_ne_zero m hϖ0) hlt
  have hint : ∀ g ∈ H, ∀ i j, (g : GL (Fin N) k) i j ∈ 𝒪[k] := by
    intro g hg i j
    have h1 : g ∈ (H : Set (GL (Fin N) k)) := hg
    rw [hH] at h1
    have h2 := h1 i j
    have h3 : valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
      have h4 : (g : Matrix (Fin N) (Fin N) k) i j =
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) +
            (1 : Matrix (Fin N) (Fin N) k) i j := by ring
      rw [h4]
      refine (Valuation.map_add _ _ _).trans (max_le (h2.trans hlt.le) ?_)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    exact (Valuation.mem_integer_iff _ _).2 h3
  ext g
  rw [SetLike.mem_coe, mem_congruenceSubgroup_iff]
  constructor
  · rintro ⟨-, h2⟩ i j
    rw [map_pow]
    exact h2 i j
  · intro hg
    have hgH : g ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hg
    refine ⟨(mem_integralGL_iff k N).2 ⟨hint g hgH, hint _ (H.inv_mem hgH)⟩, fun i j => ?_⟩
    have := hg i j
    rwa [map_pow] at this

theorem le_valuation_uniformizer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((uniformizer k : 𝒪[k]) : k) := by
  have hxi : x ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hx.le
  have h1 : (⟨x, hxi⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_uniformizer k),
    Ideal.mem_span_singleton] at h1
  exact (Valuation.integer.integers (valuation k)).le_of_dvd h1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow' (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  simp [nabs]

theorem modulus_zj {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) :
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ (∑ a, if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) := by
  have hpos : nabs k t ≠ 0 := (nabs_pos k t).ne'
  have h1 : ∀ a : Fin h, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) ^
        modExp (fun a => Fin (d a)) a =
      nabs k t ^ (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) := by
    intro a
    by_cases ha : a ≤ j
    · have h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.val_det_apply]
      rw [h2, nabs_pow', if_pos ha, _root_.zpow_mul, zpow_natCast]
    · have h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = 1 := by
        simp [Zl.JC.zj, ha]
      rw [h2, if_neg ha]
      simp [nabs]
  rw [modulus, Finset.prod_congr rfl fun a _ => h1 a]
  induction (Finset.univ : Finset (Fin h)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hpos, ih]

theorem exists_decomp (t : kˣ) (ht : valuation k (t : k) < 1) :
    ∃ (n : ℕ) (p u : kˣ), (p : k) = ((uniformizer k : 𝒪[k]) : k) ∧ valuation k (u : k) = 1 ∧
      t = p ^ n * u := by
  have hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0 :=
    (Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)
  have hti : (t : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have ht0 : (⟨t, hti⟩ : 𝒪[k]) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht0 (irreducible_uniformizer k)
  have hu0 : (((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) ≠ 0 := fun h0 =>
    (e⁻¹).ne_zero (Subtype.ext h0)
  refine ⟨n, Units.mk0 _ hϖ0, Units.mk0 _ hu0, rfl, ?_, ?_⟩
  · exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 (e⁻¹).isUnit
  · apply Units.ext
    have h1 : (⟨t, hti⟩ : 𝒪[k]) = GroundTheory.Automorphic.GLnLocal.uniformizer k ^ n * ((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) := by
      rw [← he, mul_assoc, Units.mul_inv, mul_one]
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem diagT_mem_integralGL {N : ℕ} (f : Fin N → kˣ) (hf : ∀ i, valuation k (f i : k) = 1) :
    diagT k (Fin N) f ∈ integralGL k N := by
  have hent : ∀ g : Fin N → kˣ, (∀ i, valuation k (g i : k) = 1) → ∀ i j,
      (diagT k (Fin N) g : GL (Fin N) k) i j ∈ 𝒪[k] := by
    intro g hg i j
    show (diagT k (Fin N) g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]
    rw [val_diagT, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (hg i).le
    · exact zero_mem _
  rw [mem_integralGL_iff]
  refine ⟨hent f hf, ?_⟩
  rw [← map_inv]
  refine hent _ fun i => ?_
  simp [hf i]

theorem measure_le_translate {N : ℕ} [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)]
    (μ : Measure (AdGL k N)) [μ.IsMulLeftInvariant] (K : Subgroup (GL (Fin N) k))
    (s w : GL (Fin N) k) (hc : Commute s w) (hw : ∀ x ∈ K, w * x * w⁻¹ ∈ K) :
    μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * s * y}) ≤
      μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
        {g | ∃ x ∈ K, ∃ y ∈ K, g = x * (s * w) * y}) := by
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * s * y} ⊆
      (fun q => (QuotientGroup.mk w : AdGL k N) * q) ⁻¹'
        ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g | ∃ x ∈ K, ∃ y ∈ K, g = x * (s * w) * y}) := by
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    refine ⟨_, ⟨w * x * w⁻¹, hw x hx, y, hy, rfl⟩, ?_⟩
    show (QuotientGroup.mk _ : AdGL k N) = QuotientGroup.mk (w * (x * s * y))
    congr 1
    rw [hc.eq]
    group
  exact (measure_mono hsub).trans_eq (measure_preimage_mul μ _ _)

end GlobalTheory.CompanionTheory.ContractVolume
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleContra

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullForm (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ f.toLinearMap, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show σ.dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v => by
          have h : σ.dual g l.1 = l.1 := hg
          have h2 := LinearMap.congr_fun h (f v)
          have h3 : σ.dual g l.1 (f v) = l.1 (σ g⁻¹ (f v)) := rfl
          rw [h3, ← f.isIntertwining] at h2
          exact h2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem pullForm_injective (f : π.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (pullForm f) := fun a b h => Subtype.ext (LinearMap.ext fun y => by
  obtain ⟨v, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem mem_range_pullForm (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (l : smoothPart π.dual)
    (hl : ∀ v, f v = 0 → l.1 v = 0) : l ∈ (pullForm f).range := by
  let q : (V ⧸ LinearMap.ker f.toLinearMap) →ₗ[ℂ] ℂ := (LinearMap.ker f.toLinearMap).liftQ l.1 (fun v hv => hl v hv)
  let l' : Module.Dual ℂ W := q ∘ₗ (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl' : ∀ v, l' (f v) = l.1 v := fun v => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show q ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v)) = _
    rw [this]
    rfl
  have hs : l' ∈ smoothPart σ.dual := mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds l.2 (by
      show π.dual 1 l.1 = l.1
      rw [map_one]
      rfl)) fun g hg => LinearMap.ext fun w => by
      obtain ⟨v, rfl⟩ := hf w
      have h : π.dual g l.1 = l.1 := hg
      have h2 := LinearMap.congr_fun h v
      have h3 : π.dual g l.1 v = l.1 (π g⁻¹ v) := rfl
      rw [h3] at h2
      show l' (σ g⁻¹ (f v)) = l' (f v)
      rw [← f.isIntertwining, hl', hl', h2])
  exact ⟨⟨l', hs⟩, Subtype.ext (LinearMap.ext fun v => hl' v)⟩

theorem isSmooth_subContra (S : Subrepresentation (contra π)) : IsSmooth S.toRepresentation := fun l => by
  have : {g : G | S.toRepresentation g l = l} = {g : G | contra π g l.1 = l.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact isSmooth_contra π l.1

def evalForms (hπ : IsSmooth π) (S : Subrepresentation (contra π)) : π.IntertwiningMap (contra S.toRepresentation) where
  toLinearMap :=
    { toFun := fun v => ⟨{ toFun := fun l => l.1.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg =>
          LinearMap.ext fun l => by
            have h : π g v = v := hg
            show ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v = l.1.1 v
            rw [contra_apply, inv_inv, h])⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun l => map_add l.1.1 a b)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun l => map_smul l.1.1 c a) }
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun l => by
    show l.1.1 (π g v) = ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v
    rw [contra_apply, inv_inv])

end General

theorem isSocle_contra_of_isCosocle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  intro k _ _ _ _ hA N V W _ _ _ _ σ π hπ _ hc
  obtain ⟨hi, f, hf, hu⟩ := hc
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hσ : IsSmooth σ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  have hci : (contra σ).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ hσ hi) hi
  refine ⟨hci, pullForm f, pullForm_injective f hf, fun S hS => ?_⟩
  have hSi := GlobalTheory.MaschkeForms.isIrreducible_of_isAtom hS
  have hcS : (contra S.toRepresentation).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (isSmooth_subContra S) hSi) hSi
  let e := evalForms hπ S
  have hr : e.range ≠ ⊥ := fun h0 => hS.1 (eq_bot_iff.2 fun l hl => by
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : e v ∈ (⊥ : Subrepresentation (contra S.toRepresentation)) := h0 ▸ ⟨v, rfl⟩
    have hv0 : e v = 0 := hv
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩)
  have he : Function.Surjective e := fun y => by
    have : y ∈ e.range := by
      have ht : e.range = ⊤ := (eq_bot_or_eq_top _).resolve_left hr
      rw [ht]
      trivial
    exact this
  have hk : e.ker = f.ker := hu _ (isCoatom_ker hcS e he)
  have hle : S ≤ (pullForm f).range := fun l hl => mem_range_pullForm f hf l fun v hv => by
    have hv' : v ∈ e.ker := hk ▸ hv
    have hv0 : e v = 0 := hv'
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩
  exact ((isAtom_range hci _ (pullForm_injective f hf)).le_iff.1 hle).resolve_left hS.1

end GlobalTheory.CompanionTheory.SocleContra

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | exact GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | (intros; apply GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_involutive : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), dualCl (dualCl x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | exact GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | (intros; apply GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGiven
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

private theorem det_updateRow_one' {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (r : n) (b : n → R) : (updateRow (1 : Matrix n n R) r b).det = b r := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl

theorem exists_GL_lastRow_eq (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hN : (updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_updateRow_one']
    simpa using hi
  have hM : ((updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).submatrix id (Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_permute']
    refine mul_ne_zero ?_ hN
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i (Fin.last m))) with h | h <;> simp [h]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m)) (Fin.last m) (Equiv.swap i (Fin.last m) j) = a j
  rw [updateRow_self, Function.comp_apply, Equiv.swap_apply_self]

end GlobalTheory.CompanionTheory.MirFourier
end

