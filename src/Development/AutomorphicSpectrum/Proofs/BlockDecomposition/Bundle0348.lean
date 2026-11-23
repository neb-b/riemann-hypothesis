module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruence
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ZjContract

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal
open GroundTheory.Automorphic.Iwasawa ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diagGL_conj_mem {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α} {m : ℕ}
    (D : Fin n → kˣ)
    (hlt : ∀ i l, β i < β l → valuation k ((D i : k) * ((D l)⁻¹ : kˣ)) ≤ 1)
    (heq : ∀ i l, β i = β l → D i = D l)
    {u : GL (Fin n) k} (hu : u ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β) :
    diagGL k n D * u * (diagGL k n D)⁻¹ ∈
      congruenceSubgroup k n m ⊓ unipotentRadical k n β := by
  have hb : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
        (1 : Matrix (Fin n) (Fin n) k) i l) ≤
          valuation k ((uniformizer k : 𝒪[k]) : k) ^ m := by
    intro w hw i l
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨hwP, hw1⟩ := mem_unipotentRadical.1 hwN
    rw [diagGL_conj_apply]
    rcases lt_trichotomy (β i) (β l) with h | h | h
    · have hil : i ≠ l := fun e => h.ne (by rw [e])
      have hK := ((mem_congruenceSubgroup_iff k n).1 hwK).2 i l
      rw [one_apply_ne hil, sub_zero] at hK ⊢
      have e : (D i : k) * w i l * (((D l)⁻¹ : kˣ) : k) =
          ((D i : k) * (((D l)⁻¹ : kˣ) : k)) * w i l := by ring
      rw [e, map_mul]
      exact (mul_le_mul' (hlt i l h) hK).trans (by rw [one_mul])
    · rw [hw1 i l h, heq i l h]
      have : (D l : k) * (1 : Matrix (Fin n) (Fin n) k) i l * (((D l)⁻¹ : kˣ) : k) =
          (1 : Matrix (Fin n) (Fin n) k) i l := by
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [this, sub_self, map_zero]
      exact zero_le
    · have hil : i ≠ l := fun e => h.ne' (by rw [e])
      have h0 : w i l = 0 := hwP h
      rw [h0, mul_zero, zero_mul, one_apply_ne hil, sub_zero, map_zero]
      exact zero_le
  have hP : diagGL k n D ∈ blockUpper k n β := levi_le_blockUpper (diagGL_mem_levi D)
  have hentry : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l) ≤ 1 := by
    intro w hw i l
    have he : valuation k ((1 : Matrix (Fin n) (Fin n) k) i l) ≤ 1 := by
      by_cases h : i = l <;> simp [Matrix.one_apply, h]
    have eq : (diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l =
        ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
          (1 : Matrix (Fin n) (Fin n) k) i l) + (1 : Matrix (Fin n) (Fin n) k) i l := by ring
    rw [eq]
    exact ((valuation k).map_add _ _).trans
      (max_le ((hb w hw i l).trans (pow_le_one' (valuation_uniformizer_lt_one k).le m)) he)
  refine Subgroup.mem_inf.2 ⟨(mem_congruenceSubgroup_iff k n).2 ⟨?_, hb u hu⟩,
    conj_mem_unipotentRadical hP (Subgroup.mem_inf.1 hu).2⟩
  refine (mem_integralGL_iff k n).2 ⟨hentry u hu, ?_⟩
  have eq : (diagGL k n D * u * (diagGL k n D)⁻¹)⁻¹ =
      diagGL k n D * u⁻¹ * (diagGL k n D)⁻¹ := by group
  rw [eq]
  exact hentry _ (Subgroup.inv_mem _ hu)

def zjDiag {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) : Fin N → kˣ :=
  fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1

theorem leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = diagGL k N (zjDiag d hd t j) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  rw [coe_diagGL]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    have hb : Zl.JC.blockIdx d hd (stdBlocks d hd ⟨a, i⟩) = a := by simp [Zl.JC.blockIdx]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = t := by
          simp only [zjDiag, hb, if_pos hj]
        rw [hz, hD]
        simp
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = 1 := by
          simp only [zjDiag, hb, if_neg hj]
        rw [hz, hD]
        simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        rw [hz]
        simp [hil]
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        rw [hz]
        simp [hil]
  · rw [leviEmb_apply_ne k _ _ hab, diagonal_apply_ne]
    intro e
    exact hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))

theorem zjDiag_ratio {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {t : kˣ}
    (ht : valuation k (t : k) ≤ 1) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i < Zl.JC.blockIdx d hd l) :
    valuation k ((zjDiag d hd t j i : k) * (((zjDiag d hd t j l)⁻¹ : kˣ) : k)) ≤ 1 := by
  unfold zjDiag
  by_cases hi : Zl.JC.blockIdx d hd i ≤ j
  · by_cases hl : Zl.JC.blockIdx d hd l ≤ j
    · simp [if_pos hi, if_pos hl]
    · simpa [if_pos hi, if_neg hl] using ht
  · have hl : ¬ Zl.JC.blockIdx d hd l ≤ j := fun e => hi (hil.le.trans e)
    simp [if_neg hi, if_neg hl]

theorem zjDiag_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l) :
    zjDiag d hd t j i = zjDiag d hd t j l := by
  simp only [zjDiag, hil]

theorem zj_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  intro k _ _ _ _ h N d hd t ht j m
  rw [leviEmb_zj]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · exact diagGL_conj_mem _ (fun i l hil => zjDiag_ratio d hd ht j hil)
      (fun i l hil => zjDiag_eq d hd t j hil) hu
  · have key := diagGL_conj_mem (β := OrderDual.toDual ∘ Zl.JC.blockIdx d hd)
      (zjDiag d hd t j)⁻¹
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd l < Zl.JC.blockIdx d hd i := hil
        have := zjDiag_ratio d hd ht j hil'
        simpa [Pi.inv_apply, mul_comm] using this)
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l := hil
        simp only [Pi.inv_apply, zjDiag_eq d hd t j hil'])
      (u := z) hz
    rw [map_inv, inv_inv] at key
    exact key

end GlobalTheory.CompanionTheory.ZjContract

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurable
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ContractingCosets

open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal

theorem isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (A : G) :
    IsOpen {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} := by
  have h : {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} =
      ⋃ x ∈ K, (fun y => x * A * y) '' (K : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    exact ⟨fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩,
      fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩⟩
  rw [h]
  exact isOpen_biUnion fun x _ => (Homeomorph.mulLeft (x * A)).isOpenMap _ hK

theorem eq_central_mul {G : Type*} [Group G] {x y x' y' A B : G}
    (hz : (x * A * y)⁻¹ * (x' * B * y') ∈ Subgroup.center G) :
    B = ((x * A * y)⁻¹ * (x' * B * y')) * ((x'⁻¹ * x) * A * (y * y'⁻¹)) := by
  have h := Subgroup.mem_center_iff.1 hz (x'⁻¹ * x * A * y)
  calc B = (x'⁻¹ * x * A * y) * ((x * A * y)⁻¹ * (x' * B * y')) * y'⁻¹ := by group
    _ = ((x * A * y)⁻¹ * (x' * B * y')) * (x'⁻¹ * x * A * y) * y'⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k]

theorem entry_bound {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k} {C : ValueGroupWithZero k}
    (hP : ∀ i j, valuation k (P i j) ≤ 1) (hQ : ∀ i j, valuation k (Q i j) ≤ 1)
    (hB : ∀ i j, valuation k (B i j) ≤ C) (i j : Fin N) :
    valuation k ((P * B * Q) i j) ≤ C :=
  _root_.UpperTheory.Reformulated.B.Ylb4.main hP hQ hB i j

theorem coe_pow_of_diag {N : ℕ} {δ : Fin N → k} {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    ((a ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => δ i ^ r := by
  rw [Units.val_pow_eq_pow_val, ha, diagonal_pow]
  rfl

theorem coe_inv_pow_of_diag {N : ℕ} {δ : Fin N → k} (hδ : ∀ i, δ i ≠ 0) {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    (((a ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => (δ i)⁻¹ ^ r := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [coe_pow_of_diag ha, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, mul_inv_cancel₀ (hδ i), one_pow]

theorem val_le_one_of_mem {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : GL (Fin N) k} (hg : g ∈ integralGL k N) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (((mem_integralGL_iff k N).1 hg).1 i j)

theorem le_of_eq_central_mul {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : Fin N → k} (t : kˣ) (ht : valuation k (t : k) < 1)
    (hδ : ∀ i, δ i = t ∨ δ i = 1) {i₁ i₂ : Fin N} (h₁ : δ i₁ = t) (h₂ : δ i₂ = 1)
    {a : GL (Fin N) k} (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ)
    {p q z : GL (Fin N) k} (hp : p ∈ integralGL k N) (hq : q ∈ integralGL k N)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) {r r' : ℕ}
    (h : a ^ r = z * (p * a ^ r' * q)) : r ≤ r' := by
  have hδ0 : ∀ i, δ i ≠ 0 := fun i => by
    rcases hδ i with h | h <;> rw [h]
    · exact t.ne_zero
    · exact one_ne_zero
  have hvt0 : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  have hvt1 : 1 ≤ (valuation k (t : k))⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht |>.le
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  obtain ⟨c', hc'⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1
    (inv_mem hz)
  have hcc : c * c' = 1 := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂)
      (mul_inv_cancel z)
    simp only [Units.val_mul, ← hc, ← hc', Units.val_one] at e
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using e

  have hB : ∀ i j, valuation k (((a ^ r' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
    intro i j
    rw [coe_pow_of_diag ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow]
      refine pow_le_one₀ zero_le' ?_
      rcases hδ i with h | h <;> rw [h]
      · exact ht.le
      · simp
    · rw [diagonal_apply_ne _ hij]; simp

  have hB' : ∀ i j, valuation k ((((a ^ r')⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤
      (valuation k (t : k))⁻¹ ^ r' := by
    intro i j
    rw [coe_inv_pow_of_diag hδ0 ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow, map_inv₀]
      rcases hδ i with h | h <;> rw [h]
      simpa using one_le_pow₀ hvt1
    · rw [diagonal_apply_ne _ hij]; simp

  have hc1 : 1 ≤ valuation k c := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂) h
    simp only [Units.val_mul (a := z), ← hc] at e
    rw [coe_pow_of_diag ha, diagonal_apply_eq, h₂, one_pow, Matrix.scalar_apply,
      Matrix.diagonal_mul] at e
    have b := entry_bound (val_le_one_of_mem hp) (val_le_one_of_mem hq) hB i₂ i₂
    have e' := congrArg (valuation k) e
    rw [map_one, map_mul] at e'
    rw [Units.val_mul, Units.val_mul] at e'
    calc (1 : ValueGroupWithZero k) = _ := e'
      _ ≤ valuation k c * 1 := by gcongr
      _ = valuation k c := mul_one _
  have hc'1 : valuation k c' ≤ 1 := by
    have e : valuation k c * valuation k c' = 1 := by rw [← map_mul, hcc, map_one]
    calc valuation k c' = 1 * valuation k c' := (one_mul _).symm
      _ ≤ valuation k c * valuation k c' := by gcongr
      _ = 1 := e

  have hinv : (a ^ r)⁻¹ = (q⁻¹ * (a ^ r')⁻¹ * p⁻¹) * z⁻¹ := by
    rw [h]; group
  have hle : (valuation k (t : k))⁻¹ ^ r ≤ (valuation k (t : k))⁻¹ ^ r' := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₁ i₁) hinv
    simp only [Units.val_mul (b := z⁻¹), ← hc'] at e
    rw [coe_inv_pow_of_diag hδ0 ha, diagonal_apply_eq, h₁, Matrix.scalar_apply,
      Matrix.mul_diagonal] at e
    have b := entry_bound (val_le_one_of_mem (inv_mem hq)) (val_le_one_of_mem (inv_mem hp)) hB' i₁ i₁
    have e' := congrArg (valuation k) e
    rw [map_pow, map_inv₀, map_mul, Units.val_mul, Units.val_mul] at e'
    rw [e']
    calc _ ≤ (valuation k (t : k))⁻¹ ^ r' * 1 := by gcongr
      _ = _ := mul_one _
  exact (pow_le_pow_iff_right₀ ((one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht)).1 hle

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

theorem images_measurable_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (isOpen_doubleCoset _ (isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm (le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))

end GlobalTheory.CompanionTheory.ContractingCosets

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.GlueGen

variable {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D]

theorem mem_bot (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) (z : CH.Cn (U.ι ⋙ F) n) :
    z ∈ relS (U.ι ⋙ F) (fun T => (⊥ : ObjectProperty C) T.obj) n :=
  fun _ hs => False.elim hs

noncomputable def up (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    CH.Cn (U.ι ⋙ F) n →ₗ[K] (RC F U (cosieve_bot (C := C))).X n :=
  LinearMap.codRestrict _ LinearMap.id (mem_bot F U n)

def inc (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) :
    Cx.Hom (RC F U (cosieve_bot (C := C))) (CH.cx (U.ι ⋙ F)) (RingHom.id K) :=
  ⟨fun _ => Submodule.subtype _, fun _ _ => rfl⟩

theorem inc_bij (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    Function.Bijective ((inc F U).f n) :=
  ⟨Subtype.val_injective, fun z => ⟨⟨z, mem_bot F U n z⟩, rfl⟩⟩

noncomputable def relPr {M : Cx.{1} K} (F : C ⥤ ModuleCat.{0} K) (G : D ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (U' : ObjectProperty D) (p : CxPairing M (CH.cx (U.ι ⋙ F)) (CH.cx (U'.ι ⋙ G))) :
    CxPairing M (RC F U (cosieve_bot (C := C))) (RC G U' (cosieve_bot (C := D))) where
  μ {i j n} h := ((p.μ h).compl₂ ((inc F U).f j)).compr₂ (up G U' n)
  leib h x y := Subtype.ext (p.leib h x y.1)

theorem kun_iff (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K)
    (U : ObjectProperty C) (U' : ObjectProperty D)
    (p : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))) :
    KunE (P := P) (Q := fun a => RC (F a) U (cosieve_bot (C := C))) (T := fun c => RC (E c) U' (cosieve_bot (C := D)))
        (fun {a a' c} ha => relPr (F a') (E c) U U' (p ha)) ↔
      KunE (P := P) (Q := fun a => CH.cx (U.ι ⋙ F a)) (T := fun c => CH.cx (U'.ι ⋙ E c)) (fun {a a' c} ha => p ha) :=
  _root_.GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff _ _ (fun a => Cx.Hom.id (C := P a)) (fun a => inc (F a) U) (fun c => inc (E c) U')
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (fun _ => Function.bijective_id) n)
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (F a) U) n)
    (fun c n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (E c) U') n)
    (fun _ _ _ _ _ _ _ => rfl)

end GlobalTheory.CompanionTheory.KunGlue.GlueGen

open GlobalTheory.CompanionTheory.KunGlue.GlueGen in
theorem GlobalTheory.CompanionTheory.KunGlue.glue_gen : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  intro hmv hcd K _ C D _ _ F E P Rel pr hnat ι _ _ V W cV cW hR hS
  have key := GlobalTheory.T.pairing_restriction_natural hmv (K := K) (ι := ι) P (fun a => covSy (F a) V (cosieve_bot (C := C)))
    (fun c => covSy (E c) W (cosieve_bot (C := D)))
    (fun S {a a' c} ha => relPr (F a') (E c) (capU V S) (capU W S) (pr (capU V S) (capU W S) (hR S) ha))
    (fun {S S'} h {a a' c} ha {i j n} hn x y => Subtype.ext
      (hnat (hR S) (hR S') (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩)
        (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩) ha hn x y.1))
    (fun a => hcd K ι C (F a) V ⊥ cosieve_bot cV)
    (fun c => hcd K ι D (E c) W ⊥ cosieve_bot cW)
    (fun S hne => (kun_iff F E P (capU V S) (capU W S) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)).2 (hS S hne))
  exact (kun_iff F E P (capU V ∅) (capU W ∅) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha)).1 key
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.DerWhit

private theorem twKer_congr' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H = H') (θ : H →* ℂˣ) (θ' : H' →* ℂˣ)
    (hθ : ∀ (x : G) (hx : x ∈ H), θ' ⟨x, h ▸ hx⟩ = θ ⟨x, hx⟩) :
    GlobalTheory.PRep.twKer ρ H θ = GlobalTheory.PRep.twKer ρ H' θ' := by
  subst h
  obtain rfl : θ' = θ := MonoidHom.ext fun x => hθ x x.2
  rfl

theorem colFix_zero (k : Type) [Field k] (N : ℕ) : colFix k N 0 = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  exact fun i hi => absurd hi (Nat.not_lt_zero _)

theorem mem_derUnip_zero (k : Type) [Field k] (N : ℕ) {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N)) :
    g ∈ derUnip k N 0 := by
  unfold GlobalTheory.BZMir.derUnip
  exact Subgroup.mem_inf.2 ⟨hg, GlobalTheory.CompanionTheory.DerWhit.colFix_zero k N ▸ Subgroup.mem_top g⟩

theorem whitCharFrom_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (u : unipB k (Fin N)) :
    whitCharFrom k ψ N 0 u = whitChar ψ N u := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar]
  | (simp only [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar, MonoidHom.coe_mk,
        OneHom.coe_mk]
     congr 2
     exact Finset.sum_congr (by ext p; simp) fun _ _ => rfl)

theorem twKer_derUnip_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  have hU : GlobalTheory.BZMir.derUnip k N 0 = GlobalTheory.SmGL.unipB k (Fin N) :=
    le_antisymm (GlobalTheory.BZMir.derUnip_le_unipB k N 0)
      fun g hg => GlobalTheory.CompanionTheory.DerWhit.mem_derUnip_zero k N hg
  refine twKer_congr' π hU _ _ fun x hx => ?_
  exact (GlobalTheory.CompanionTheory.DerWhit.whitCharFrom_zero ψ N ⟨x, hU ▸ hx⟩).symm

end GlobalTheory.CompanionTheory.DerWhit
end

