module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainB
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma ccb_JJ (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * A) = A := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]

lemma ccb_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show (Z - Jm ε * Zᴴ * Jm ε) + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

lemma ccb_inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, smul_add, smul_sub, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg]
  abel

lemma ccb_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first
    | (simp [Complex.conj_I]; ring)
    | (rw [star_div', star_one, star_mul', Complex.star_def, Complex.conj_I]; field_simp; ring)
    | (apply Complex.ext <;> simp [Complex.div_re, Complex.div_im])
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, neg_smul, smul_add, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_add]
  abel

lemma ccb_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

lemma ccb_exp_inUJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left (show Xᴴ * Jm ε + Jm ε * X = 0 from hX)
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hs : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  have e2 : (t : ℂ) • -(Jm ε * X * Jm ε) = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hs, hXh, e2, Matrix.exp_conj _ _ hJu, hJinv]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [Matrix.mul_assoc (Jm ε * _) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc]
    _ = Jm ε := by rw [ccb_exp_neg_mul, Matrix.mul_one]

lemma ccb_inUJ_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hh : inUJ ε h) : inUJ ε (g * h) := by
  unfold inUJ at *
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

section Paths
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma ccb_path_right (X y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * y) (X * y) 0 :=
  (dga_exp X).mul_const y

lemma ccb_path_left (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  (dga_exp X).const_mul g

end Paths

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ccb_rdv (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X)))
      (-(fderiv ℂ F (g⁻¹ * m) (X * (g⁻¹ * m)))) 0 := by
  set y := g⁻¹ * m with hy
  have hyV : y ∈ V := (hWV g hg).2
  have hΦ : HasFDerivAt F (fderiv ℂ F y) y := (hF.differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
  have h0 : y = NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * y := by simp
  have h1 : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y))
      (fderiv ℂ F y (-X * y)) 0 :=
    (hΦ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (ccb_path_right (-X) y) h0
  have hcont : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (ccb_path_left g X).continuousAt
  have hW0 : W ∈ nhds ((fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) := by
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hW.mem_nhds hg
  have hev : ∀ᶠ t : ℝ in nhds 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ W :=
    hcont.preimage_mem_nhds hW0
  have hfin : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y) := by
    filter_upwards [hev] with t ht
    rw [hf _ ht (ccb_inUJ_mul ε hgu (ccb_exp_inUJ ε hX t)), Matrix.mul_inv_rev, smul_neg,
      Matrix.exp_neg, Matrix.mul_assoc]
  have h2 := h1.congr_of_eventuallyEq hfin
  rwa [Matrix.neg_mul, map_neg] at h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dmW (U : Matrix (Fin n) (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) (J : {J : Finset (Fin n) // J.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2

def dmChi (i : ℕ) (a : Fin n) : ℂ := if (a : ℕ) < i then 1 else 0

def dmK (U : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (k l : Fin n) : ℂ :=
  ∑ a, dmChi i a * (star (U a k) * U a l)

def dmInd (J : Finset (Fin n)) (k : Fin n) : ℂ := if k ∈ J then 1 else 0

lemma dm_sum_castLE {i : ℕ} (hi : i ≤ n) (f : Fin n → ℂ) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a : Fin n, dmChi i a * f a := by
  simp only [dmChi, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter, a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl

lemma dm_entry (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (a b : Fin n) :
    (U * Matrix.diagonal d * Uᴴ) a b = ∑ j, U a j * d j * star (U b j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma dm_UUh {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

lemma dm_UhU {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

lemma dm_unit {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    ∑ j, U a j * star (U b j) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h := congrFun (congrFun (dm_UUh hU) a) b
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.conjTranspose_apply] using h

lemma dm_one_sub {i : ℕ} (hi : i ≤ n) (a b : Fin i) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hi a) (Fin.castLE hi b) = (1 : Matrix (Fin i) (Fin i) ℂ) a b := by
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun e => h (Fin.castLE_injective hi e)

lemma dm_normsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma dm_mass {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) = 1 := by
  have h := lead_unitary_diag (U := U) (fun _ => (1 : ℂ)) i hi
  simp only [Finset.prod_const_one, mul_one] at h
  simp only [dmW]
  rw [← h, lead, dite_eq_left hi, Matrix.diagonal_one, Matrix.mul_one, dm_UUh hU]
  have h2 : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 := by
    ext a b; rw [Matrix.submatrix_apply, dm_one_sub]
  rw [h2, Matrix.det_one]

lemma sum_minorWeights_indicator {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * dmInd J.1 k = dmK U i k k := by
  have h := lead_unitary_diag (U := U) (fun j => if j = k then (2 : ℂ) else 1) i hi
  have hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, (if j = k then (2 : ℂ) else 1) = 1 + dmInd J k := by
    intro J; rw [Finset.prod_ite_eq']; unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  simp only [dmW] at hm ⊢
  rw [hm] at h
  let v : Fin i → ℂ := fun a => U (Fin.castLE hi a) k
  have hsub : (U * Matrix.diagonal (fun j => if j = k then (2 : ℂ) else 1) * Uᴴ).submatrix
      (Fin.castLE hi) (Fin.castLE hi) = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (star v) := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * (if j = k then (2 : ℂ) else 1) * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0 := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp; ring
      · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]
    simp [Matrix.mul_apply, v]
  rw [lead, dite_eq_left hi, hsub, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  have hdot : star v ⬝ᵥ v = dmK U i k k := by
    rw [dotProduct, dmK, ← dm_sum_castLE hi (fun a => star (U a k) * U a k)]
    rfl
  rw [hdot] at h
  linear_combination -h

lemma sum_minorWeights_indicator_pair {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) (hkl : k ≠ l) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k := by
  have h := lead_unitary_diag (U := U)
    (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) i hi
  have hprod : ∀ J : Finset (Fin n),
      ∏ j ∈ J, ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) =
        1 + dmInd J k + dmInd J l + dmInd J k * dmInd J l := by
    intro J
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  have h1 := sum_minorWeights_indicator hU hi k
  have h2 := sum_minorWeights_indicator hU hi l
  simp only [dmW] at hm h1 h2 ⊢
  rw [hm, h1, h2] at h
  let W : Matrix (Fin i) (Fin 2) ℂ :=
    Matrix.of fun a c => if c = 0 then U (Fin.castLE hi a) k else U (Fin.castLE hi a) l
  have hsub : (U * Matrix.diagonal (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
      * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + W * Wᴴ := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
        * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          ((if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0) +
          (if l = j then U (Fin.castLE hi a) l * star (U (Fin.castLE hi b) l) else 0)) := by
      intro j
      by_cases hjk : j = k
      · have hjl : j ≠ l := hjk ▸ hkl
        rw [if_pos hjk, if_neg hjl, if_pos hjk.symm, if_neg (Ne.symm hjl), hjk]; ring
      · by_cases hjl : j = l
        · rw [if_neg hjk, if_pos hjl, if_neg (Ne.symm hjk), if_pos hjl.symm, hjl]; ring
        · rw [if_neg hjk, if_neg hjl, if_neg (Ne.symm hjk), if_neg (Ne.symm hjl)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU,
      dm_one_sub]
    simp [Matrix.mul_apply, W, Fin.sum_univ_two]
  have hK : ∀ c c' : Fin 2, (Wᴴ * W) c c' = dmK U i (![k, l] c) (![k, l] c') := by
    intro c c'
    rw [Matrix.mul_apply, dmK, ← dm_sum_castLE hi (fun a => star (U a (![k, l] c)) * U a (![k, l] c'))]
    refine Finset.sum_congr rfl fun a _ => ?_
    fin_cases c <;> fin_cases c' <;> simp [W]
  rw [lead, dite_eq_left hi, hsub, Matrix.det_one_add_mul_comm, Matrix.det_fin_two] at h
  simp only [Matrix.add_apply, hK, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add] at h
  linear_combination -h

lemma dm_m {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k + if k = l then dmK U i k k else 0 := by
  by_cases hkl : k = l
  · subst hkl
    have hsq : ∀ (m : Fin n) (J : Finset (Fin n)), dmInd J m * dmInd J m = dmInd J m := by
      intro m J
      unfold dmInd
      split_ifs <;> simp
    rw [if_pos rfl]
    simp only [hsq, sum_minorWeights_indicator hU hi]
    ring
  · rw [sum_minorWeights_indicator_pair hU hi k l hkl, if_neg hkl, add_zero]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {ε : Fin n → Bool}

lemma exists_signVG (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIxV ε s) = q0 ε := by
  unfold q0
  rcases le_total (pOf ε) (qOf ε) with h | h
  · refine ⟨true, ?_⟩
    rw [min_eq_left h]
    first
    | (rw [pOf, Fintype.card_subtype])
    | simp [SgIxV, pOf, Fintype.card_subtype]
  · refine ⟨false, ?_⟩
    rw [min_eq_right h]
    first
    | (rw [qOf, Fintype.card_subtype])
    | simp [SgIxV, qOf, Fintype.card_subtype]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA
section
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcA_exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))

lemma exists_local_matrix_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h

lemma continuous_matrix_exp_alt :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous

end LogL

lemma lcA_exists_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)

lemma lcA_exists_klog (ε : Fin n → Bool) : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ ∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      k ∈ Kset ε → inK ε (ℓ k) ∧ NormedSpace.exp (ℓ k) = k := by
  obtain ⟨L, hL1, hL2, hL3⟩ := lcA_exists_log (n := n)
  refine ⟨L, hL1, ?_⟩
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hA : Tendsto (fun k => (L k)ᴴ) (𝓝 1) (𝓝 0) := by
    have h := hL1.star
    rw [star_zero] at h
    exact h
  have hB : Tendsto (fun k => -(L k)) (𝓝 1) (𝓝 0) := by
    have h := hL1.neg
    rw [neg_zero] at h
    exact h
  have hC : Tendsto (fun k => Jm ε * L k * Jm ε) (𝓝 1) (𝓝 0) := by
    have h := (hL1.const_mul (Jm ε)).mul_const (Jm ε)
    rw [mul_zero, zero_mul] at h
    exact h
  filter_upwards [hL2, hA.eventually hL3, hB.eventually hL3, hC.eventually hL3] with k h2 hA' hB' hC' hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkk : kᴴ * k = 1 := by
    have h := hk'.1
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  have e1 : NormedSpace.exp ((L k)ᴴ) = kᴴ := by rw [Matrix.exp_conjTranspose, h2]
  have e2 : NormedSpace.exp (-(L k)) = kᴴ := by
    rw [Matrix.exp_neg, h2]
    exact Matrix.inv_eq_left_inv hkk
  have hstar : (L k)ᴴ = -(L k) := by
    rw [← hA', e1, ← e2, hB']
  have e3 : NormedSpace.exp (Jm ε * L k * Jm ε) = NormedSpace.exp (L k) := by
    have h := Matrix.exp_conj (Jm ε) (L k) hJu
    rw [hJinv] at h
    rw [h, h2, mul_assoc, hk'.2, ← mul_assoc, hJJ, one_mul]
  have e4 : Jm ε * L k * Jm ε = L k := by
    rw [← hC', e3, h2]
  have hcomm : L k * Jm ε = Jm ε * L k := by
    calc L k * Jm ε = Jm ε * L k * Jm ε * Jm ε := by rw [e4]
      _ = Jm ε * L k := by rw [mul_assoc, hJJ, mul_one]
  refine ⟨⟨?_, hcomm⟩, h2⟩
  show (L k)ᴴ * Jm ε + Jm ε * L k = 0
  rw [hstar, neg_mul, ← hcomm]
  first
  | exact neg_add_cancel _
  | simp

open scoped Matrix.Norms.L2Operator in
lemma lcA_polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

