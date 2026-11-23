module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
section
noncomputable section

open Finset

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs with h <;> simp [h]

private theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_right_inv (Jm_mul_Jm ε)

private theorem isUnit_Jm (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_Jm ε, Jm_mul_Jm ε⟩, rfl⟩

private theorem conjTranspose_eq_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm, mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, neg_mul]

theorem exp_smul_mem_UJset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  have hc : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, conjTranspose_eq_of_inG hX, Jm_inv]
    simp
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ (isUnit_Jm ε), Jm_inv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Jm ε * _) (Jm ε) (Jm ε), Jm_mul_Jm, mul_one, mul_assoc]
    _ = Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem exp_add_smul (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

theorem exp_mem_Kset {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    NormedSpace.exp Z ∈ Kset ε := by
  have hZh : Zᴴ = -Z := by
    rw [conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1
    rw [← Matrix.exp_conjTranspose, hZh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)

theorem inP_apply_eq_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    {a b : Fin n} (hab : ε a = ε b) : X a b = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero .. | (apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> first | assumption | infer_instance)

theorem inK_apply_eq_zero {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {a b : Fin n} (hab : ε a ≠ ε b) : Z a b = 0 := by
  have h := congrFun (congrFun hZ.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  all_goals first
    | exact absurd (ha.trans hb.symm) hab
    | (simp [ha, hb] at h; first | linear_combination h / 2 | linear_combination -h / 2)

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma kExp_Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

section L2
open scoped Matrix.Norms.L2Operator

lemma exists_inK_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k := by
  obtain ⟨hu, hc⟩ := hk
  have hfin := Matrix.finite_spectrum k
  have hN : IsStarNormal k := ⟨by
    rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hu, Unitary.mul_star_self_of_mem hu]⟩
  have hcl : ContinuousOn Complex.log (spectrum ℂ k) := hfin.continuousOn _

  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hz

  have hJ : Commute k (Jm ε) := hc
  have hJs : Commute (star k) (Jm ε) := by
    have h := congrArg star hc
    simp only [star_mul, Matrix.star_eq_conjTranspose, kExp_Jm_conjTranspose] at h
    exact h.symm
  have hZJ : Commute (cfc Complex.log k) (Jm ε) := Commute.cfc hJ hJs _
  have hstar : star (cfc Complex.log k) = -cfc Complex.log k := by
    rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, h1]
  refine ⟨cfc Complex.log k, ⟨?_, hZJ.eq⟩, ?_⟩
  · unfold inG
    rw [← Matrix.star_eq_conjTranspose, hstar, neg_mul, hZJ.eq]
    exact neg_add_cancel _
  · rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc Complex.log k) (cfc_predicate _ _),
      ← cfc_comp NormedSpace.exp Complex.log k hN ((hfin.image _).continuousOn _) hcl]
    conv_rhs => rw [← cfc_id ℂ k hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have h1 := hcirc z hz
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    simp only [Function.comp_apply, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log hz0]

end L2

theorem exists_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k :=
  exists_inK_exp_eq_of_mem_Kset hk

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
section
noncomputable section

open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

namespace PolarDecomposition

lemma polar_Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma polar_Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs <;> simp [*]

lemma polar_J_unit (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, polar_Jm_mul_self ε, polar_Jm_mul_self ε⟩, rfl⟩

lemma polar_Jinv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_left_inv (polar_Jm_mul_self ε)

lemma polar_exp_Jconj (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  have h := Matrix.exp_conj (Jm ε) A (polar_J_unit ε)
  rwa [polar_Jinv] at h

lemma polar_sa {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) : IsSelfAdjoint A := by
  exact hA

lemma polar_exp_inj {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  rw [← CFC.log_exp A (polar_sa hA), ← CFC.log_exp B (polar_sa hB), h]

lemma polar_exp_herm {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) :
    (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by
  exact Matrix.IsHermitian.exp hA

lemma polar_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left), neg_add_cancel, NormedSpace.exp_zero]

lemma polar_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_right), add_neg_cancel, NormedSpace.exp_zero]

lemma polar_exp_two (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (A + A) = NormedSpace.exp A * NormedSpace.exp A :=
  Matrix.exp_add_of_commute A A (Commute.refl A)

lemma polar_half {A B : Matrix (Fin n) (Fin n) ℂ} (h : A + A = B + B) : A = B := by
  rw [← two_smul ℂ A, ← two_smul ℂ B] at h
  exact smul_right_injective _ two_ne_zero h

lemma polar_spec_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hu : IsUnit P) :
    ∀ x ∈ spectrum ℝ P, 0 < x := by
  intro x hx
  rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have h0 := hP.eigenvalues_nonneg i
  have hne : hP.isHermitian.eigenvalues i ≠ 0 := by
    intro h
    have hmem := hP.isHermitian.eigenvalues_mem_spectrum_real i
    rw [h, spectrum.zero_mem_iff] at hmem
    exact hmem hu
  exact lt_of_le_of_ne h0 (Ne.symm hne)

lemma polar_exp_log {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsSelfAdjoint P)
    (hs : ∀ x ∈ spectrum ℝ P, 0 < x) : NormedSpace.exp (CFC.log P) = P := by
  have hlogsa : IsSelfAdjoint (CFC.log P) := cfc_predicate Real.log P
  rw [← CFC.real_exp_eq_normedSpace_exp hlogsa]
  show cfc Real.exp (cfc Real.log P) = P
  rw [← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn
    (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]
  conv_rhs => rw [← cfc_id' ℝ P hP]
  exact cfc_congr fun x hx => Real.exp_log (hs x hx)

lemma polar_gJgH {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * Jm ε * gᴴ = Jm ε ∧ IsUnit g := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hJJ := polar_Jm_mul_self ε
  have hleft : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  have hright : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.1 hleft
  refine ⟨?_, ⟨⟨g, _, hright, hleft⟩, rfl⟩⟩
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = Jm ε := by rw [hright, Matrix.one_mul]

def polar_L (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • CFC.log (gᴴ * g)

lemma polar_L_herm (g : Matrix (Fin n) (Fin n) ℂ) : (polar_L g)ᴴ = polar_L g := by
  have h : IsSelfAdjoint (CFC.log (gᴴ * g)) := cfc_predicate Real.log (gᴴ * g)
  exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul h

lemma polar_L_add (g : Matrix (Fin n) (Fin n) ℂ) :
    polar_L g + polar_L g = CFC.log (gᴴ * g) := by
  rw [polar_L, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]

lemma polar_isSelfAdjoint_isUnit_spectrum_pos {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g) ∧ ∀ x ∈ spectrum ℝ (gᴴ * g), 0 < x := by
  have hu : IsUnit g := (polar_gJgH hg).2
  have hu2 : IsUnit (gᴴ * g) := hu.star.mul hu
  exact ⟨Matrix.isHermitian_conjTranspose_mul_self g, hu2,
    polar_spec_pos (Matrix.posSemidef_conjTranspose_mul_self g) hu2⟩

lemma polar_exp_LL {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    NormedSpace.exp (polar_L g + polar_L g) = gᴴ * g := by
  have hf := polar_isSelfAdjoint_isUnit_spectrum_pos hg
  rw [polar_L_add]
  exact polar_exp_log hf.1 hf.2.2

lemma polar_JLJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * polar_L g * Jm ε = -polar_L g := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hLh := polar_L_herm g
  have hJh := polar_Jm_conjTranspose ε
  have hJJ := polar_Jm_mul_self ε
  have hgJ := (polar_gJgH hg).1
  have hA : (Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε)ᴴ =
      Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hLh, hJh, Matrix.mul_assoc]
  have hB : (-polar_L g + -polar_L g)ᴴ = -polar_L g + -polar_L g := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, hLh]
  have hsplit : Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε =
      Jm ε * (polar_L g + polar_L g) * Jm ε := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have h1 : NormedSpace.exp (Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε) =
      Jm ε * (gᴴ * g) * Jm ε := by
    rw [hsplit, polar_exp_Jconj, polar_exp_LL hg]
  have hM : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1 := by
    calc (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = Jm ε * gᴴ * (g * Jm ε * gᴴ) * g := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  have hN : NormedSpace.exp (-polar_L g + -polar_L g) * (gᴴ * g) = 1 := by
    rw [← polar_exp_LL hg, show -polar_L g + -polar_L g = -(polar_L g + polar_L g) by abel]
    exact polar_exp_neg_mul _
  have h2 : NormedSpace.exp (-polar_L g + -polar_L g) = Jm ε * (gᴴ * g) * Jm ε := by
    rw [← Matrix.inv_eq_left_inv hN, Matrix.inv_eq_left_inv hM]
  exact polar_half (polar_exp_inj hA hB (h1.trans h2.symm))

lemma polar_L_inP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inP ε (polar_L g) := by
  have h := polar_JLJ hg
  have hJJ := polar_Jm_mul_self ε
  have h2 : Jm ε * polar_L g = -(polar_L g * Jm ε) := by
    calc Jm ε * polar_L g = Jm ε * polar_L g * Jm ε * Jm ε := by
          rw [Matrix.mul_assoc (Jm ε * polar_L g) (Jm ε) (Jm ε), hJJ, Matrix.mul_one]
      _ = -polar_L g * Jm ε := by rw [h]
      _ = -(polar_L g * Jm ε) := Matrix.neg_mul _ _
  refine ⟨?_, by rw [h2, neg_neg]⟩
  show (polar_L g)ᴴ * Jm ε + Jm ε * polar_L g = 0
  rw [polar_L_herm, h2, add_neg_cancel]

lemma polar_k_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * NormedSpace.exp (-polar_L g) ∈ Kset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hJJ := polar_Jm_mul_self ε
  have hEiE := polar_exp_neg_mul (polar_L g)
  have hEEi := polar_exp_mul_neg (polar_L g)
  have hgg : gᴴ * g = NormedSpace.exp (polar_L g) * NormedSpace.exp (polar_L g) := by
    rw [← polar_exp_two, polar_exp_LL hg]
  have hEih : (NormedSpace.exp (-polar_L g))ᴴ = NormedSpace.exp (-polar_L g) :=
    polar_exp_herm (by rw [Matrix.conjTranspose_neg, polar_L_herm])
  have hEiJ : NormedSpace.exp (-polar_L g) * Jm ε = Jm ε * NormedSpace.exp (polar_L g) := by
    have h := polar_exp_Jconj ε (polar_L g)
    rw [polar_JLJ hg] at h
    rw [h, Matrix.mul_assoc (Jm ε * NormedSpace.exp (polar_L g)), hJJ, Matrix.mul_one]
  have hkk : (g * NormedSpace.exp (-polar_L g))ᴴ * (g * NormedSpace.exp (-polar_L g)) = 1 := by
    calc (g * NormedSpace.exp (-polar_L g))ᴴ * (g * NormedSpace.exp (-polar_L g))
        = NormedSpace.exp (-polar_L g) * (gᴴ * g) * NormedSpace.exp (-polar_L g) := by
          rw [Matrix.conjTranspose_mul, hEih]; simp only [Matrix.mul_assoc]
      _ = (NormedSpace.exp (-polar_L g) * NormedSpace.exp (polar_L g)) *
          (NormedSpace.exp (polar_L g) * NormedSpace.exp (-polar_L g)) := by
          rw [hgg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hEiE, hEEi, Matrix.mul_one]
  have hkJ : (g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g)) = Jm ε := by
    calc (g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g))
        = NormedSpace.exp (-polar_L g) * (gᴴ * Jm ε * g) * NormedSpace.exp (-polar_L g) := by
          rw [Matrix.conjTranspose_mul, hEih]; simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp (-polar_L g) * Jm ε * NormedSpace.exp (-polar_L g) := by rw [hg']
      _ = Jm ε * NormedSpace.exp (polar_L g) * NormedSpace.exp (-polar_L g) := by rw [hEiJ]
      _ = Jm ε := by rw [Matrix.mul_assoc, hEEi, Matrix.mul_one]
  have hkk' : (g * NormedSpace.exp (-polar_L g)) * (g * NormedSpace.exp (-polar_L g))ᴴ = 1 :=
    mul_eq_one_comm.1 hkk
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 hkk, ?_⟩
  calc (g * NormedSpace.exp (-polar_L g)) * Jm ε
      = (g * NormedSpace.exp (-polar_L g)) *
        ((g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g))) := by
        rw [hkJ]
    _ = ((g * NormedSpace.exp (-polar_L g)) * (g * NormedSpace.exp (-polar_L g))ᴴ) * Jm ε *
        (g * NormedSpace.exp (-polar_L g)) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (g * NormedSpace.exp (-polar_L g)) := by rw [hkk', Matrix.one_mul]

lemma eq_mul_exp_neg_polar_L_mul_exp_polar_L {g : Matrix (Fin n) (Fin n) ℂ} :
    g = g * NormedSpace.exp (-polar_L g) * NormedSpace.exp (polar_L g) := by
  rw [Matrix.mul_assoc, polar_exp_neg_mul, Matrix.mul_one]

end PolarDecomposition

open PolarDecomposition in
theorem polar_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ k ∈ Kset ε, ∃ Y, inP ε Y ∧ g = k * NormedSpace.exp Y :=
  ⟨_, polar_k_mem hg, polar_L g, polar_L_inP hg, eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

