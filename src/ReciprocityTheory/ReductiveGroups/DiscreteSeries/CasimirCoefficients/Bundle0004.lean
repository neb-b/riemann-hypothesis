module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Minors
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma sub_lower_mul {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (c * M).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      c.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have ha := a.2
  rw [hc _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]

private lemma sub_mul_upper {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c')
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (M * c').submatrix (Fin.castLE hi) (Fin.castLE hi) =
      M.submatrix (Fin.castLE hi) (Fin.castLE hi) * c'.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have hb := b.2
  unfold IsUpperTri at hc'
  rw [hc' _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

private lemma lowerTri_sub {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) :
    (c.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsLowerTriangular := by
  intro a b hab
  have hab' : a < b := hab
  apply hc
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

private lemma upperTri_sub {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c') :
    (c'.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
  intro a b hab
  have hab' : b < a := hab
  apply hc'
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

theorem lead_tri_mul {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c') (i : ℕ) (hi : i ≤ n) :
    lead i (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), c l l * c' l l) * lead i z := by
  have hp : ∀ f : Fin n → ℂ, ∏ a : Fin i, f (Fin.castLE hi a) =
      ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), f l := by
    intro f
    rw [Finset.prod_filter]
    refine Fintype.prod_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ ?_
    · intro k hk
      rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · intro a
      rw [if_pos (by rw [Fin.coe_castLE]; exact a.2)]
  unfold lead
  rw [dite_eq_left hi, dite_eq_left hi, sub_mul_upper hi hc', sub_lower_mul hi hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular _ (lowerTri_sub hi hc), Matrix.det_of_upperTriangular (upperTri_sub hi hc'),
    Finset.prod_mul_distrib, ← hp (fun l => c l l), ← hp (fun l => c' l l)]
  simp only [Matrix.submatrix_apply]
  ring

theorem lead_posDef {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (i : ℕ) (hi : i ≤ n) :
    0 < (lead i x).re ∧ (lead i x).im = 0 := by
  have hp := (hx.submatrix (Fin.castLE_injective hi)).det_pos
  unfold lead
  rw [dite_eq_left hi]
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hp
  exact ⟨h1, h2.symm⟩

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
section
noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
  exact (contDiff_apply ℂ (fun _ => ℂ) b).comp (contDiff_apply ℂ (fun _ => (Fin n → ℂ)) a)

theorem contDiff_lead (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dif_pos]
    simp only [Matrix.det_apply, Units.smul_def]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun k _ => ?_
    simp only [Matrix.submatrix_apply]
    exact contDiff_entry _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const

theorem contDiffAt_zpow_lead (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by
  have hl : ContDiffAt ℂ m (lead (n := n) i) z := (contDiff_lead i).contDiffAt
  rcases k with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hl.pow k
  · simp only [zpow_negSucc]
    exact (hl.pow (k + 1)).inv (pow_ne_zero _ hz)

theorem contDiffAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    {m : ℕ∞ω} : ContDiffAt ℂ m (PhiM μ) z := by
  unfold PhiM
  exact contDiffAt_prod fun i _ => contDiffAt_zpow_lead _ _ (hz i)

theorem differentiableAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  exact (contDiffAt_phiM μ hz (m := 1)).differentiableAt (by norm_num)

theorem hasDerivAt_line {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) hl

def mulLeftCLM (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)

theorem lhol_lhol_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) := by
  unfold Lhol
  have hc : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => Y * y) (mulLeftCLM Y) z :=
    (mulLeftCLM Y).hasFDerivAt
  have h := hc.hasFDerivAt.clm_apply hu
  erw [h.fderiv]
  rfl

theorem lhol_comm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = Lhol Y (Lhol X F) z + fderiv ℂ F z ((Y * X - X * Y) * z) := by
  rw [lhol_lhol_eq hF, lhol_lhol_eq hF]
  have hs := hF.isSymmSndFDerivAt (by simp)
  have h1 : fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) :=
    hs _ _
  have h2 : fderiv ℂ F z ((Y * X - X * Y) * z) =
      fderiv ℂ F z (Y * (X * z)) - fderiv ℂ F z (X * (Y * z)) := by
    rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  linear_combination -h1 - h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def PsiFormulaStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

section Gelfand

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

def opPow (A : Fin n → Fin n → F → F) : ℕ → Fin n → Fin n → F → F
  | 0, a, b, f => if a = b then f else 0
  | k + 1, a, b, f => ∑ c, A a c (opPow A k c b f)

def opGelfand (A : Fin n → Fin n → F → F) (k : ℕ) (f : F) : F := ∑ a, opPow A k a a f

end Gelfand

section Right

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rightE (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => EabV ε a b f

def rightEanti (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => -EabV ε (Fin.rev b) (Fin.rev a) f

end Right

def PsiAllStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

