module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.DiscreteSpecialLinearGroupRingOfIntegers
section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Disc

theorem eq_zero_of_lt_one {L : Type} [Field L] [NumberField L] (a : 𝓞 L)
    (h : ∀ w : InfinitePlace L, w (a : L) < 1) : a = 0 := by
  classical
  by_contra ha
  have hn : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ a : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs hn
    exact_mod_cast this
  have h2 := prod_eq_abs_norm (a : L)
  rw [← Algebra.coe_norm_int] at h2
  have h3 : ∏ w : InfinitePlace L, w (a : L) ^ w.mult < 1 := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]
    have hp : ∏ w ∈ Finset.univ.erase w0, w (a : L) ^ w.mult ≤ 1 :=
      Finset.prod_le_one₀ (fun w _ => pow_nonneg (apply_nonneg _ _) _)
        (fun w _ => pow_le_one₀ (apply_nonneg _ _) (h w).le)
    have hw0 : w0 (a : L) ^ w0.mult < 1 :=
      pow_lt_one₀ (apply_nonneg _ _) (h w0) InfinitePlace.mult_pos.ne'
    calc _ ≤ w0 (a : L) ^ w0.mult * 1 :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg (apply_nonneg _ _) _)
      _ < 1 := by rw [mul_one]; exact hw0
  rw [h2] at h3
  push_cast at h3
  linarith

theorem continuous_entry {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun x : Sp L N => mt x w i j := by
  fun_prop

theorem mt_latS {L : Type} [Field L] [NumberField L] {N : ℕ} (σ : SpecialLinearGroup (Fin N) (𝓞 L))
    (w : InfinitePlace L) (i j : Fin N) :
    mt ((MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)) σ) w i j =
      w.embedding (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j : 𝓞 L) : L) := rfl

theorem countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.injective.countable

end PositivityTheory.KB.MomentRationality.Disc

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Disc

theorem discrete_specialLinearGroup_ringOfIntegers : SDisc := by
  intro L _ _ N
  refine ⟨?_, ?_⟩
  · rw [discreteTopology_iff_isOpen_singleton_one]
    let U : Set (Sp L N) :=
      {x | ∀ w i j, ‖mt x w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun j =>
          isOpen_lt ((continuous_entry w i j).sub continuous_const).norm continuous_const
    refine isOpen_induced_iff.2 ⟨U, hU, ?_⟩
    ext ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγU
      obtain ⟨σ, rfl⟩ := hγ
      have hσ : σ = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have h0 := eq_zero_of_lt_one
          (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) - (1 : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (fun w => ?_)
        · simpa using sub_eq_zero.1 h0
        · have h1 := hγU w i j
          rw [mt_latS] at h1
          rw [← norm_embedding_eq]
          convert h1 using 2
          by_cases hij : i = j
          · subst hij
            simp
          · simp [Matrix.one_apply, hij]
      subst hσ
      apply Subtype.ext
      simp
    · intro h
      have h' : γ = 1 := congrArg Subtype.val h
      subst h'
      intro w i j
      have hone : mt (1 : Sp L N) w = 1 := rfl
      rw [hone, sub_self, norm_zero]
      exact one_pos
  · haveI := countable_O L
    haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
    haveI : Countable (SpecialLinearGroup (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable {A : Matrix (Fin N) (Fin N) (𝓞 L) // A.det = 1})
    exact (MonoidHom.rangeRestrict_surjective
      (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w))).countable

end PositivityTheory.KB

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OfSInvCoe
section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mt_mul (x y : Sp L N) (w : InfinitePlace L) :
    mt (x * y) w = mt x w * mt y w := rfl

theorem mt_one (w : InfinitePlace L) : mt (1 : Sp L N) w = 1 := rfl

theorem mt_inv_mul (x : Sp L N) (w : InfinitePlace L) : mt x⁻¹ w * mt x w = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (x : Sp L N) (w : InfinitePlace L) : mt x w * mt x⁻¹ w = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem ofS_inv_coe (x : Sp L N) (w : InfinitePlace L) :
    ((((ofS L N x) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mt x⁻¹ w := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem q_actL (x : Sp L N) (y : Lat L N) :
    q (actL (ofS L N x) (one L N).1) y = ∑ w, ∑ i, ‖(mt x⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  rw [hm, re_quad]

theorem q_dual (x : Sp L N) (y : Lat L N) :
    q (dualH (actL (ofS L N x) (one L N).1)) y =
      ∑ w, ∑ i, ‖((mt x w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hBM : mt x⁻¹ w * mt x w = 1 := mt_inv_mul x w
  have hMB : mt x w * mt x⁻¹ w = 1 := mt_mul_inv x w
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  have hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ := by
    rw [hm]
    refine Matrix.inv_eq_left_inv ?_
    calc mt x w * (mt x w)ᴴ * ((mt x⁻¹ w)ᴴ * mt x⁻¹ w)
        = mt x w * (mt x⁻¹ w * mt x w)ᴴ * mt x⁻¹ w := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]
  have hd : mat (dualH (actL (ofS L N x) (one L N).1)) w =
      ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ := by
    simp only [dualH, mat_mkHS]
    rw [hinv, Matrix.transpose_mul]
    rfl
  rw [hd, re_quad]

theorem lam_ge (hN : 1 ≤ N) {h : HS L N} {κ : ℝ} (hκ : ∀ y : Lat L N, y ≠ 0 → κ ≤ q h y) : κ ≤ lam h := by
  have hne : Nonempty {y : Lat L N // y ≠ 0} := by
    refine ⟨⟨fun _ => 1, fun h0 => ?_⟩⟩
    have := congrFun h0 ⟨0, hN⟩
    exact one_ne_zero this
  unfold lam
  exact le_ciInf fun y => hκ y.1 y.2

end PositivityTheory.KB.MomentRationality.Ht
end
end

