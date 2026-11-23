module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.DdMemUnitary
section
noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

def dd {R : Type*} [CommRing R] (N : ℕ) (u : R) : Matrix (Fin N) (Fin N) R :=
  diagonal fun i => if (i : ℕ) = 0 then u else 1

theorem dd_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (u : R) :
    (dd N u).map f = dd N (f u) := by
  unfold dd
  rw [diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_mul {R : Type*} [CommRing R] (N : ℕ) (u v : R) : dd N u * dd N v = dd N (u * v) := by
  unfold dd
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_one {R : Type*} [CommRing R] (N : ℕ) : dd N (1 : R) = 1 := by
  unfold dd
  simp

theorem det_dd {R : Type*} [CommRing R] {N : ℕ} (hN : 1 ≤ N) (u : R) : (dd N u).det = u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  unfold dd
  rw [det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ]

def ddGL {R : Type*} [CommRing R] (N : ℕ) (u : Rˣ) : GL (Fin N) R :=
  ⟨dd N (u : R), dd N ((u⁻¹ : Rˣ) : R), by rw [dd_mul, Units.mul_inv, dd_one],
    by rw [dd_mul, Units.inv_mul, dd_one]⟩

theorem exists_root {N : ℕ} (hN : N ≠ 0) {d : ℂ} (hd : d ≠ 0) : ∃ z : ℂ, z ≠ 0 ∧ z ^ N * d = 1 := by
  refine ⟨d⁻¹ ^ ((N : ℂ)⁻¹), ?_, ?_⟩
  · intro h
    have := Complex.cpow_nat_inv_pow d⁻¹ hN
    rw [h, zero_pow hN] at this
    exact inv_ne_zero hd this.symm
  · rw [Complex.cpow_nat_inv_pow _ hN, inv_mul_cancel₀ hd]

theorem cancel_left {N : ℕ} {A X B : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {z c : ℂ} (hz : z ≠ 0)
    (h : (z • A) * X = c • (A * B)) : X = (z⁻¹ * c) • B := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h2 : A * (z • X) = A * (c • B) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, h]
  have h3 : z • X = c • B := by
    have := congrArg (fun Y => A⁻¹ * Y) h2
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu] using this
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hz, one_smul]

open NumberField in
theorem units_fin {L : Type*} [Field L] [NumberField L] (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (𝓞 L)ˣ, ∀ u : (𝓞 L)ˣ, ∃ v : (𝓞 L)ˣ, ∃ u0 ∈ S, u = v ^ N * u0 := by
  classical
  let f : Units.torsion L × (Fin (Units.rank L) → Fin N) → (𝓞 L)ˣ :=
    fun p => (p.1 : (𝓞 L)ˣ) * ∏ i, Units.fundSystem L i ^ ((p.2 i : ℕ) : ℤ)
  refine ⟨(Set.finite_range f).toFinset, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod L u
  have h1 : ∀ i, 0 ≤ e i % N := fun i => Int.emod_nonneg (e i) (by omega)
  have h2 : ∀ i, e i % N < N := fun i => Int.emod_lt_of_pos (e i) (by omega)
  refine ⟨∏ i, Units.fundSystem L i ^ (e i / N), f (ζ, fun i => ⟨(e i % N).toNat, by
    have := h2 i; have := h1 i; omega⟩), by simp, ?_⟩
  have hsplit : ∀ i, Units.fundSystem L i ^ e i =
      (Units.fundSystem L i ^ (e i / N)) ^ N * Units.fundSystem L i ^ (((e i % N).toNat : ℕ) : ℤ) := by
    intro i
    rw [Int.toNat_of_nonneg (h1 i), ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 1
    linarith [Int.mul_ediv_add_emod (e i) N]
  rw [hu]
  simp only [f]
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib, Finset.prod_pow]
  ac_rfl

end PositivityTheory.KB.MomentRationality.Cz.Red
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

abbrev G (ι : Type) (N : ℕ) : Type := ι → SpecialLinearGroup (Fin N) ℂ

variable {ι : Type} {N : ℕ}

abbrev mt (x : G ι N) (w : ι) : Matrix (Fin N) (Fin N) ℂ :=
  ((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

def dg (s : Fin N → ℝ) (hs : ∑ i, s i = 0) : G ι N := fun _ =>
  ⟨diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ), by
    rw [det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, hs, Real.exp_zero, Complex.ofReal_one]⟩

def Cone (T : ℝ) (s : Fin N → ℝ) : Prop := ∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T

def W (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then |s i - s j| else 0

def Phi (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if i < j then s i - s j else 0

def PB (M : ℝ) : Set (G ι N) := {p | ∀ w, (mt p w).BlockTriangular id ∧ ∀ i j, ‖mt p w i j‖ ≤ M}

def KS : Set (G ι N) := {k | ∀ w, mt k w ∈ unitaryGroup (Fin N) ℂ}

def OmG [Fintype ι] (M : ℝ) : Set (G ι N) :=
  {p | (∀ w, (mt p w).BlockTriangular id) ∧ (∀ w i j, ‖mt p w i j‖ ≤ M) ∧ (∀ w i, M⁻¹ ≤ ‖mt p w i i‖) ∧
    ∀ i, ∏ w, ‖mt p w i i‖ = 1}

def Sg (P : Set (G ι N)) (T : ℝ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Xb (P : Set (G ι N)) (T : ℝ) (m : Fin N → ℤ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s ∧ (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Zb (R : ℝ) : Set (G ι N) := {z | ∀ w i j, ‖mt z w i j‖ ≤ R}

open scoped Classical in
open Classical in
def nu (w0 : ι) : SpecialLinearGroup (Fin N) GaussianInt →* G ι N :=
  (MonoidHom.mulSingle (fun _ : ι => SpecialLinearGroup (Fin N) ℂ) w0).comp
    (SpecialLinearGroup.map GaussianInt.toComplex)

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end

