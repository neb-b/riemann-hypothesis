module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
section
noncomputable section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRat

theorem exists_proj (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]

theorem val_eq_sum_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (v : VV ℂ lam) :
    v.1 = ∑ a, (bVV ℂ lam).repr v a • bVVfun ℂ lam a := by
  conv_lhs => rw [← (bVV ℂ lam).sum_repr v]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bVV_coe]

theorem coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, AddMonoidAlgebra.coeff (bVVfun ℂ lam a) m ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((AddMonoidAlgebra.coeff P m : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : AddMonoidAlgebra.coeff v.1 m = ∑ b, c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (AddMonoidAlgebra.coeff v.1 m) = AddMonoidAlgebra.coeff v.1 m := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (AddMonoidAlgebra.coeff v.1 m) = ∑ b, φ (c b) * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) :
    AddMonoidAlgebra.coeff (f v).1 m ∈ Set.range κ := by
  refine coeff_mem_of_repr σ' κ _ (fun a => ?_) m
  have e : f v = ∑ b, (bVV ℂ σ).repr v b • f (bVV ℂ σ b) := by
    conv_lhs => rw [← (bVV ℂ σ).sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun b _ => ?_
  exact Subfield.mul_mem _ (RingHom.mem_fieldRange.2 (repr_mem_of_coeff σ κ v hv b)) (RingHom.mem_fieldRange.2 (hf a b))

end GlobalTheory.RowRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBound
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.VolBallPf

theorem double_count {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E) (hφ : Continuous φ) (W : Set G) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 < r) (hW : ∀ g h, ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ 2 * r → h⁻¹ * g ∈ W) :
    μ {g | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
  first
  | exact @_root_.GlobalTheory.SeparatedSetCardBound.main
  | exact _root_.GlobalTheory.SeparatedSetCardBound.main
  | (apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)

def toEuc {m : ℕ} (A : Mat m) : EuclideanSpace ℂ (Fin m × Fin m) := WithLp.toLp 2 fun p => A p.1 p.2

theorem norm_vec {m : ℕ} (A : Mat m) : ‖toEuc A‖ = hsn A := by
  simp [toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem toEuc_sub {m : ℕ} (A B : Mat m) : toEuc A - toEuc B = toEuc (A - B) := by
  ext p; simp [toEuc]

theorem continuous_vec {m : ℕ} : Continuous (toEuc : Mat m → _) := by
  unfold toEuc
  fun_prop

theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hsn (umat g⁻¹) = hsn (umat g) := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := determinant_character_mul_inv g
  have h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
    calc umat g⁻¹ = Jm ε * Jm ε * umat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
      _ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg]
      _ = Jm ε * (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [h2]
  unfold hsn
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem hsn_mul {m : ℕ} (A B : Mat m) : hsn (A * B) ≤ hsn A * hsn B := sqrt_frobenius_mul_le A B

theorem hsn_add {m : ℕ} (A B : Mat m) : hsn (A + B) ≤ hsn A + hsn B := sqrt_frobenius_add_le A B

end GlobalTheory.SepReal.VolBallPf

namespace GlobalTheory.SepReal

open VolBallPf

theorem volBall : VolBall := by
  intro m ε δ R hδ hR
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix m ε).1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ} :=
      isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const
    refine lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)
    · simpa [norm_vec, hsn, umat] using hδ
    · have : ‖toEuc (umat g - 1)‖ < δ := hg
      rw [norm_vec] at this
      exact this.le
  · refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))
    have h1 : hsn (umat g - 1) ≤ δ := hg
    have h2 := hsn_add (umat g - 1) 1
    rw [sub_add_cancel] at h2
    have h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m) := by linarith
    exact (Real.sqrt_le_iff.1 h3).2
  · have key := double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le
      (by positivity) (fun g h hh hgh => by
        rw [norm_vec] at hh
        rw [toEuc_sub, norm_vec] at hgh
        show hsn (umat (h⁻¹ * g) - 1) ≤ δ
        have h1 : umat h⁻¹ * umat h = 1 := by
          have := determinant_character_mul_inv h⁻¹
          rw [inv_inv] at this
          exact this
        have h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h) := by
          rw [Matrix.mul_sub, h1]; rfl
        rw [h2]
        refine (hsn_mul _ _).trans ?_
        rw [hsn_inv]
        calc hsn (umat h) * hsn (umat g - umat h) ≤ R * (2 * (δ / (2 * R))) :=
              mul_le_mul hh hgh (Real.sqrt_nonneg _) hR.le
          _ = δ := by field_simp)
    have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2 := by
      rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [sq]
    have hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ := by field_simp; ring
    simp only [norm_vec, hfr, hq] at key
    exact key

end GlobalTheory.SepReal

end
end

