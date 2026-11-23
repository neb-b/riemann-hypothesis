module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF
variable {n : ℕ}

lemma map_star_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

lemma map_star_star (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j
  simp

lemma map_star_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma map_star_ct (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star)ᴴ = aᴴ.map star := by
  ext i j
  simp

lemma Jm_star (ε : Fin n → Bool) : (Jm ε).map star = Jm ε := by
  ext i j
  simp only [Matrix.map_apply, Formalism.REAL.Jm, Matrix.diagonal_apply]
  split_ifs <;> simp

lemma UJ_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) : g.map star ∈ UJset ε := by
  have h' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := h
  show (g.map star)ᴴ * Formalism.REAL.Jm ε * g.map star = Formalism.REAL.Jm ε
  have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) h'
  simp only [map_star_mul, Jm_star] at e
  rw [map_star_ct]
  exact e

lemma K_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g.map star ∈ Kset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hu
    simp only [map_star_mul, map_star_one, Matrix.star_eq_conjTranspose] at e
    rw [Matrix.star_eq_conjTranspose, map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hc
    simpa only [map_star_mul, Jm_star] using e

lemma P_star {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : inP ε (X.map star) := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  show ((X.map star)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X.map star = 0) ∧
    X.map star * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X.map star)
  refine ⟨?_, ?_⟩
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hg
    have ha : ∀ M N : Matrix (Fin n) (Fin n) ℂ, (M + N).map star = M.map star + N.map star :=
      fun M N => by
        ext i j
        simp
    have hz : (0 : Matrix (Fin n) (Fin n) ℂ).map star = 0 := by
      ext i j
      simp
    simp only [ha, hz, map_star_mul, Jm_star] at e
    rw [map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hp
    have hn : ∀ M : Matrix (Fin n) (Fin n) ℂ, (-M).map star = -(M.map star) := fun M => by
      ext i j
      simp
    simpa only [hn, map_star_mul, Jm_star] using e

lemma exp_star (X : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp X).map star = NormedSpace.exp (X.map star) := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map star = Mᴴᵀ := fun M => by
    ext i j
    simp
  rw [e (NormedSpace.exp X), e X, Matrix.exp_transpose, Matrix.exp_conjTranspose]

lemma Phi_star (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : Phi lam (z.map star) = star (Phi lam z) := by
  have e : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ), (M.map star).det = star M.det := by
    intro N M
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose Mᴴ]
    congr 1
  simp only [GlobalTheory.Dec.Phi, star_prod, star_zpow₀]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  simp only [Formalism.MainNotions.S.leadMinor]
  rw [← e]
  rfl

lemma K_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ UJset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]

lemma one_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε := by
  refine ⟨one_mem _, ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

lemma K_inv {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g⁻¹ = gᴴ := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp h'.1

lemma K_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ KC ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  exact ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp h'.1, Matrix.mem_unitaryGroup_iff'.mp h'.1⟩, rfl⟩, h'.2⟩

lemma exp_posDef {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : (NormedSpace.exp X).PosDef := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hp]
    exact eq_neg_of_add_eq_zero_left hg
  have hH : Xᴴ = X := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = X * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [h1]
      _ = X := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hYH : ((2⁻¹ : ℝ) • X)ᴴ = (2⁻¹ : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, hH, star_trivial]
  have hYY : (2⁻¹ : ℝ) • X + (2⁻¹ : ℝ) • X = X := by
    rw [← add_smul]
    norm_num
  rw [← hYY, Formalism.REAL.exp_add_self]
  have hE := Formalism.REAL.exp_conjTranspose_of_hermitian hYH
  have hsq : NormedSpace.exp ((2⁻¹ : ℝ) • X) * NormedSpace.exp ((2⁻¹ : ℝ) • X) =
      (NormedSpace.exp ((2⁻¹ : ℝ) • X))ᴴ * NormedSpace.exp ((2⁻¹ : ℝ) • X) := by
    rw [hE]
  rw [hsq]
  apply Matrix.PosDef.conjTranspose_mul_self
  intro u v huv
  have e := congrArg (NormedSpace.exp (-((2⁻¹ : ℝ) • X))).mulVec huv
  simpa only [Matrix.mulVec_mulVec, Formalism.REAL.matrix_exp_neg_mul_exp, Matrix.one_mulVec] using e

lemma URep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) σ) : IsURepOn (Kset ε) σ := by
  obtain ⟨⟨h1, hm⟩, hi, hc⟩ := h
  exact ⟨⟨h1, fun a ha b hb => hm a (K_UJ ha) b (K_UJ hb)⟩, fun g hg v => hi g (K_UJ hg) v,
    fun v => (hc v).mono (fun g hg => K_UJ hg)⟩


end GlobalTheory.Dec.FormF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShellSumMajorant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

private lemma exp_mul_exp_neg_eq_shell (a : ℝ) (r : ℕ) :
    Real.exp (2 * a * (r + 1)) * Real.exp (-(4 * a * r)) =
      Real.exp (2 * a) * Real.exp (-(2 * a)) ^ r := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem shell_sum_majorant : ∀ (n q : ℕ) (h : ℝ), 1 ≤ n → 1 ≤ q → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h → AntitoneOn (decE q h) (Set.Ici 0) ∧ (∀ r : ℕ, decE q h r ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ Summable (fun r : ℕ => Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ ∑' r : ℕ, Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r)) ≤ 2 * Real.exp (2 * (n : ℝ) ^ 2) := by
  intro n q h hn hq hh
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr hq1
  have hsqpos : 0 < Real.sqrt (q : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 32 * (n : ℝ) ^ 2 * Real.sqrt q := by positivity
    linarith
  have hgeo := fun r : ℕ => exp_mul_exp_neg_eq_shell ((n : ℝ) ^ 2) r
  have h3 : 3 ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp (2 * (n : ℝ) ^ 2)]
  have he0 : 0 ≤ Real.exp (-(2 * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
  have he : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    have hm : min (2 * x ^ 2) (x / Real.sqrt q) ≤ min (2 * y ^ 2) (y / Real.sqrt q) := by
      apply min_le_min
      · nlinarith
      · exact div_le_div_of_nonneg_right hxy hsqpos.le
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  ·
    intro r
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hmin : min (2 * (r : ℝ) ^ 2) (r / Real.sqrt q) = r / Real.sqrt q := by
        apply min_eq_right
        have : (r : ℝ) / Real.sqrt q ≤ r := div_le_self (by linarith) hsq
        nlinarith
      rw [hmin, neg_mul]
      apply neg_le_neg
      have hd : 32 * (n : ℝ) ^ 2 ≤ h / Real.sqrt q := by
        rw [le_div_iff₀ hsqpos]
        exact hh
      have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ r)
      have hdiv : h / 8 * (r / Real.sqrt q) = h / Real.sqrt q * r / 8 := by ring
      rw [hdiv]
      linarith
  · rw [funext hgeo]
    exact (summable_geometric_of_lt_one he0 (by linarith)).mul_left _
  ·
    rw [funext hgeo, tsum_mul_left, tsum_geometric_of_lt_one he0 (by linarith)]
    have hinv : (1 - Real.exp (-(2 * (n : ℝ) ^ 2)))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (2 * (n : ℝ) ^ 2)).le
    linarith

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpacePropsOfDiff
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

theorem stepSpace_props_of_diff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → (∀ P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) → ∀ P : ℕ, IsKStableOn ε σ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X w) (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w) 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ (P + 1)) ∧ ∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ w' ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (w + c • w') = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w + c • GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w' := by
  intro n ε H _ _ _ σ lam hU hd P
  have hσ : IsCRepOn (UJset ε) σ := hU.1
  refine ⟨?_, fun X hX w hw => ⟨(hd P w hw X hX).hasDerivAt, ?_⟩,
    fun X hX w hw w' hw' c => dAct_add_smul (hd P w hw X hX) (hd P w' hw' X hX) c⟩
  · intro g hg v hv
    have : stepSpace ε lam σ P ≤ (stepSpace ε lam σ P).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, u, hl, hX, hu, rfl⟩
      change σ g (dWord σ l u) ∈ stepSpace ε lam σ P
      rw [dWord_conj hσ hd hg hu l hX]
      refine dWord_mem (by simpa using hl) ?_ (lowKSub_stable ε lam σ g hg u hu)
      intro Y hY
      obtain ⟨X, hXl, rfl⟩ := List.mem_map.mp hY
      exact inG_conj hg (hX X hXl)
    exact this hv
  · induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, u, hl, hl', hu, rfl⟩ := hv
      refine dWord_mem (l := X :: l) (by simpa using hl) ?_ hu
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | h
      · exact hX
      · exact hl' Y h
    | zero => rw [dAct_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have := dAct_add_smul (hd P x hx X hX) (hd P y hy X hX) 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have := dAct_add_smul (hd P 0 (Submodule.zero_mem _) X hX) (hd P x hx X hX) c
      rw [zero_add, dAct_zero, zero_add] at this
      rw [this]
      exact Submodule.smul_mem _ c ihx

end GlobalTheory.StepLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumTwoPowPredMulExpNegLeExpNegThird
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem sum_two_pow_pred_mul_pow_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) (q : ℕ) :
    ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * r ^ J ≤ 2 * r * (1 - (1 / 2) ^ q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n := by rw [mul_pow]; ring
    have h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h2 h0
    have h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1))
        = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n := by ring
    rw [h3, h5]
    linarith

theorem sum_two_pow_pred_mul_exp_neg_le :
    ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  intro q x hx
  have hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J := by
    intro J
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hr]
  have h0 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(x / 2)) ≤ 1 / 4 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp (x / 2)
    linarith
  refine (sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_
  have h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (2 : ℝ) ≤ Real.exp (x / 6) := by
    have := Real.add_one_le_exp (x / 6)
    linarith
  have h4 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [h2]
  nlinarith [mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrFirstPattern
section
noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dite_eq_left ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dite_eq_left ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dite_eq_left ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dite_eq_right (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
end
end

