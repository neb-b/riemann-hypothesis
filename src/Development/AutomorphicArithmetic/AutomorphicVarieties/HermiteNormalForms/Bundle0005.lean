module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Detlow
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.detlow_num (d : ℕ) (hd : d = 0 ∨ 2 ≤ d) (E P g : ℝ) (hE : 1 ≤ E)
    (hP : 0 ≤ P) (h1 : 1 ≤ (4 * (d : ℝ)) ^ d * g) (h2 : 2 ^ d * g = E * P ^ 2) :
    1 ≤ E * (d : ℝ) ^ d * P := by
  have hq : (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d := by
    rcases hd with rfl | hd2
    · simp
    · apply one_le_pow₀
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hprod : 1 ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
    calc (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d * ((4 * (d : ℝ)) ^ d * g) :=
          one_le_mul_of_one_le_of_one_le hq h1
      _ = E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
        rw [← mul_assoc, ← mul_pow, show (d : ℝ) / 2 * (4 * d) = 2 * d * d by ring, mul_pow,
          mul_pow, ← h2]
        ring
  have hE0 : 0 ≤ E := by linarith
  have hX : 0 ≤ E * (d : ℝ) ^ d * P := mul_nonneg (mul_nonneg hE0 (by positivity)) hP
  have hsq : 1 ≤ (E * (d : ℝ) ^ d * P) ^ 2 := by
    calc (1 : ℝ) ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := hprod
      _ ≤ E * (E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hE) (le_trans zero_le_one hprod)]
      _ = (E * (d : ℝ) ^ d * P) ^ 2 := by ring
  nlinarith

theorem UpperTheory.V.KT.detlow :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (h : HS L N), h ∈ Ry L N →
    1 ≤ (I0 L N : ℝ) * ∏ w, (mat h w).det.re := by
  intro L _ _ _ N h hh
  classical
  obtain ⟨hherm, hquad, hreal, hbij⟩ := gramq L N h
  have hint0 : (intVec (0 : Fin N × BI L → ℤ) : KT.Lat L N) = 0 := by
    funext a
    simp [intVec]
  have hpos : ∀ c : Fin N × BI L → ℤ, c ≠ 0 →
      1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ KT.gram h *ᵥ (fun i => (c i : ℝ)) := by
    intro c hc
    rw [hquad, hreal]
    have hne : intVec c ≠ 0 := fun h0 => hc (hbij.1 (h0.trans hint0.symm))
    exact hh (intVec c) hne
  obtain ⟨_, hdet⟩ := grampd (Fin N × BI L) (KT.gram h) hherm hpos
  have hcard : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  rw [hcard] at hdet
  have hgd := gramdet L N h
  have hPpos : 0 ≤ ∏ w, (mat h w).det.re := by
    apply Finset.prod_nonneg
    intro w _
    exact (Complex.pos_iff.1 ((rypos L N hh w).det_pos)).1.le
  have hE : (1 : ℝ) ≤ (absD L : ℝ) ^ N := by
    apply one_le_pow₀
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero L))
  have hd : dd L N = 0 ∨ 2 ≤ dd L N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · left
      simp [dd, hN]
    · right
      have hr := Module.finrank_pos (R := ℚ) (M := L)
      have h2 : 2 ≤ Module.finrank ℚ L := by
        rw [IsTotallyComplex.finrank] at hr ⊢
        omega
      show 2 ≤ Module.finrank ℚ L * N
      nlinarith
  have key := UpperTheory.V.KT.detlow_num (dd L N) hd ((absD L : ℝ) ^ N) (∏ w, (mat h w).det.re)
    (KT.gram h).det hE hPpos hdet hgd
  have e : ((I0 L N : ℕ) : ℝ) = (absD L : ℝ) ^ N * (dd L N : ℝ) ^ (dd L N) := by
    unfold I0
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [e]
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.good :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), ConeExtensionAcyclic.Good (qc L N) (Psd L N) := by
  intro L _ _ _ N
  obtain ⟨hc, hs, hp, hd⟩ := psdcone L N
  refine ⟨fun h hh => ?_, ?_, hc, hs, ?_, hd⟩
  · rw [poly_qc] at hh
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hh) 1
    refine ⟨Subtype.val ⁻¹' S, hS.preimage Subtype.val_injective.injOn, ?_⟩
    filter_upwards [hev] with k hk y hy
    exact hk y.1 hy
  · rw [poly_qc]; exact ryne L N
  · rw [poly_qc]; exact (rypos L N).trans hp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.stabfin :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    Finite (MulAction.stabilizer (Gm L N) v) := by
  intro L _ _ _ N v
  classical
  have hpoly : v.1 ∈ Ry L N := by
    rw [← poly_qc]
    exact v.2.1
  obtain ⟨S, hSfin, hev⟩ := locfin L N v.1 (rypos L N hpoly) 1
  have hS : ∀ y, q v.1 y = 1 → y ∈ S := by
    intro y hy
    by_contra hyS
    have := hev.self_of_nhds y hyS
    linarith
  have hspan : Spans (minVec v.1) :=
    spanpsd L N _ (fun k _ hk => v.2.2 k (fun y hy => hk y.1 hy))
  obtain ⟨A, hA, hAcol⟩ := exbasis L N _ hspan
  have hinv : ∀ g ∈ MulAction.stabilizer (Gm L N) v, ∀ y, q v.1 y = 1 → q v.1 (g • y) = 1 := by
    intro g hg y hy
    have hgh : g • v.1 = v.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg)
    have hgh' : g⁻¹ • v.1 = v.1 := inv_smul_eq_iff.2 hgh.symm
    calc q v.1 (g • y) = q v.1 (g⁻¹⁻¹ • y) := by rw [inv_inv]
      _ = q (g⁻¹ • v.1) y := (q_smul g⁻¹ v.1 y).symm
      _ = q v.1 y := by rw [hgh']
      _ = 1 := hy
  haveI : Finite S := hSfin.to_subtype
  let φ : MulAction.stabilizer (Gm L N) v → (Fin N → S) := fun g a =>
    ⟨(g : Gm L N) • (fun i => A i a), hS _ (hinv g.1 g.2 _ (hAcol a))⟩
  refine Finite.of_injective φ ?_
  intro g g' hgg
  have hcol : ∀ a, (g : Gm L N) • (fun i => A i a) = (g' : Gm L N) • (fun i => A i a) :=
    fun a => congrArg Subtype.val (congrFun hgg a)
  have hM : ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A :=
    Matrix.ext fun i a => congrFun (hcol a) i
  have hM2 : A.det • ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) =
      A.det • ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) := by
    have h2 := congrArg (· * A.adjugate) hM
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  exact Subtype.ext (Units.ext (smul_right_injective _ hA hM2))
end

