module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ENNReal

namespace GlobalTheory.TwBoundFour

def wt (N : ℕ) (c : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ((c : ℝ) / N) ^ 2))

lemma real_bound (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 0 < y) :
    1 / (1 + (y / N) ^ 2) ≤ (N:ℝ)^2 * (1 / y^2) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [sq_nonneg y, sq_nonneg (N:ℝ)]

lemma half_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
  have hz : HasSum (fun m : ℕ => (1:ℝ) / ((m:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using h
  have hz2 : HasSum (fun m : ℕ => (N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  calc ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2))
      ≤ ∑' m : ℕ, ENNReal.ofReal ((N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (real_bound N hN _ (by positivity))
    _ = ENNReal.ofReal ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hz2.summable, hz2.tsum_eq]
    _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
        apply ENNReal.ofReal_le_ofReal
        have hp := Real.pi_lt_d2
        have hp0 := Real.pi_pos
        have : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        nlinarith [sq_nonneg (N:ℝ)]

lemma int_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' c : ℤ, wt N c ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := by
  rw [tsum_of_add_one_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' m : ℕ, wt N ((m:ℤ) + 1) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; simp [wt]
  have h2 : ∑' m : ℕ, wt N (-((m:ℤ) + 1)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; unfold wt; congr 1; push_cast; ring
  have h0 : wt N 0 = 1 := by simp [wt]
  have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) + 1 + ENNReal.ofReal (2 * (N:ℝ)^2) := by
        rw [h0]; gcongr
    _ = ENNReal.ofReal (2 * (N:ℝ)^2 + 1 + 2 * (N:ℝ)^2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := ENNReal.ofReal_le_ofReal (by linarith)

lemma pi_sum_le (n : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑' c : Fin n → ℤ, ∏ j, f (c j) ≤ (∑' z, f z) ^ n := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  let t : Fin n → Finset ℤ := fun j => s.image (fun x => x j)
  have hs : s ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hx
  calc ∑ c ∈ s, ∏ j, f (c j) ≤ ∑ c ∈ Fintype.piFinset t, ∏ j, f (c j) :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ j, ∑ z ∈ t j, f z := (Finset.prod_univ_sum t (fun _ z => f z)).symm
    _ ≤ ∏ _j : Fin n, ∑' z, f z := Finset.prod_le_prod' fun j _ => ENNReal.sum_le_tsum _
    _ = (∑' z, f z) ^ n := by simp

theorem tsum_le {Y : Type} (n N : ℕ) (hN : 0 < N) (a : Y → ENNReal) (T : Fin n → Y → ℝ)
    (hinj : ∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y')
    (hint : ∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) (S : ENNReal)
    (hS : ∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) :
    ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  classical
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let cf : Function.support a → Fin n → ℤ := fun y j => Classical.choose (hint y.1 y.2 j)
  have hcf : ∀ (y : Function.support a) j, (N : ℝ) * T j y.1 = cf y j :=
    fun y j => Classical.choose_spec (hint y.1 y.2 j)
  have hT : ∀ (y : Function.support a) j, T j y.1 = (cf y j : ℝ) / N := fun y j => by
    rw [eq_div_iff hN', mul_comm]; exact hcf y j
  have hcinj : Function.Injective cf := by
    intro y y' h
    apply Subtype.ext
    apply hinj y.1 y'.1 y.2 y'.2
    intro j
    rw [hT y j, hT y' j, h]
  have hbound : ∀ y : Function.support a, a y.1 ≤ S * ∏ j, wt N (cf y j) := by
    intro y
    have hP : (∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      have hpos : (0:ℝ) < 1 + T j y.1 ^ 2 := by positivity
      rw [wt, ← hT y j, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
    calc a y.1 = a y.1 * ((∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j)) := by
          rw [hP, mul_one]
      _ = (a y.1 * ∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) := by
          rw [mul_assoc]
      _ ≤ S * ∏ j, wt N (cf y j) := by gcongr; exact hS y.1
  rw [← tsum_subtype_support]
  calc ∑' y : Function.support a, a y.1 ≤ ∑' y : Function.support a, S * ∏ j, wt N (cf y j) :=
        ENNReal.tsum_le_tsum hbound
    _ = S * ∑' y : Function.support a, ∏ j, wt N (cf y j) := ENNReal.tsum_mul_left
    _ ≤ S * ∑' c : Fin n → ℤ, ∏ j, wt N (c j) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hcinj (fun c => ∏ j, wt N (c j))
    _ ≤ S * (∑' z, wt N z) ^ n := by gcongr; exact pi_sum_le n (wt N)
    _ ≤ S * ENNReal.ofReal (5 * (N:ℝ)^2) ^ n := by gcongr; exact int_sum_le N hN
    _ = S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
        rw [ENNReal.ofReal_pow (by positivity)]

end GlobalTheory.TwBoundFour
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem covolOne_map {a b c d : ℕ} (f : Mx D a b ≃+ Mx D c d) (hf : Continuous f) (hfs : Continuous f.symm)
    (hΓ : ∀ x, f x ∈ ratMx D c d ↔ x ∈ ratMx D a b) {μ : Measure (Mx D a b)} {𝓖 : Set (Mx D a b)}
    (h : IsCovolOne (ratMx D a b) μ 𝓖) :
    IsCovolOne (ratMx D c d) (μ.map f) (f.symm ⁻¹' 𝓖) ∧
      ∀ g : Mx D c d → ℂ, ∫ x in f.symm ⁻¹' 𝓖, g x ∂(μ.map f) = ∫ y in 𝓖, g (f y) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D c d
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D c d) := ⟨rfl⟩
  let m : Mx D a b ≃ᵐ Mx D c d :=
    { toEquiv := f.toEquiv
      measurable_toFun := hf.measurable
      measurable_invFun := hfs.measurable }
  have hm : (m : Mx D a b → Mx D c d) = f := rfl
  have hmp : MeasurePreserving m μ (μ.map f) := ⟨m.measurable, rfl⟩
  have hmp' : MeasurePreserving f.symm (μ.map f) μ := hmp.symm
  have hpre : f ⁻¹' (f.symm ⁻¹' 𝓖) = 𝓖 := by
    ext y; simp
  obtain ⟨hμ, hF, h1⟩ := h
  refine ⟨⟨f.isAddHaarMeasure_map μ hf hfs, ?_, ?_⟩, fun g => ?_⟩
  · let e : ratMx D a b → ratMx D c d := fun y => ⟨f y, (hΓ _).2 y.2⟩
    have he : Function.Bijective e := by
      constructor
      · intro x y hxy
        exact Subtype.ext (f.injective (congrArg Subtype.val hxy))
      · intro x
        refine ⟨⟨f.symm x, (hΓ _).1 (by simpa using x.2)⟩, Subtype.ext ?_⟩
        simp [e]
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving he ?_
    intro y x
    simp [e, AddSubgroup.vadd_def]
  · rw [← hm, MeasurableEquiv.map_apply, hm, hpre, h1]
  · rw [← hm, m.measurableEmbedding.setIntegral_map, hm, hpre]

def swapE (S : HSp D) (t : ℕ) : Mx D S.rank t ≃+ Mx D t S.rank where
  toFun y := adj y ⬝ gA S
  invFun x := giA S ⬝ adj x
  left_inv y := by
    simp only [adj_mul, adj_gA, adj_adj, giA_gA_cancel]
  right_inv x := by
    simp only [adj_mul, adj_giA, adj_adj, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  map_add' x y := by
    simp only [adj_add, Matrix.add_mul]

theorem swapE_apply (S : HSp D) (t : ℕ) (y : Mx D S.rank t) : swapE S t y = adj y ⬝ gA S := rfl

theorem swapE_symm_apply (S : HSp D) (t : ℕ) (x : Mx D t S.rank) : (swapE S t).symm x = giA S ⬝ adj x := rfl

theorem continuous_swapE (S : HSp D) (t : ℕ) : Continuous (swapE S t) :=
  continuous_adj.matrix_mul continuous_const

theorem continuous_swapE_symm (S : HSp D) (t : ℕ) : Continuous (swapE S t).symm :=
  continuous_const.matrix_mul continuous_adj

theorem swapE_mem_iff (S : HSp D) (t : ℕ) (y : Mx D S.rank t) :
    swapE S t y ∈ ratMx D t S.rank ↔ y ∈ ratMx D S.rank t := by
  constructor
  · intro hy
    have e : y = (swapE S t).symm (swapE S t y) := ((swapE S t).symm_apply_apply y).symm
    rw [e, swapE_symm_apply]
    exact ratMx_mul (rat_mem _) (ratMx_adj hy)
  · intro hy
    exact ratMx_mul (ratMx_adj hy) (rat_mem _)

theorem swapE_symm_mem_iff (S : HSp D) (t : ℕ) (x : Mx D t S.rank) :
    (swapE S t).symm x ∈ ratMx D S.rank t ↔ x ∈ ratMx D t S.rank := by
  rw [← swapE_mem_iff, AddEquiv.apply_symm_apply]

end GlobalTheory.TwistSwap

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem adjO_split (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E)
    (y : Mx D S.rank t) (w' : WO T' S) :
    GlobalTheory.PairLift.adjO S T ((y : Matrix (Fin S.rank) (Fin t) (AE D)) *
                 GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct C * T.gram) +
      (w' : Matrix (Fin S.rank) (Fin T'.rank) (AE D)) *
        GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (T'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct (frameMat T T' ι) * T.gram)) =
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (swapE S t y : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w' := by
  have e1 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel x = rat x := fun _ => rfl
  have e2 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct x = xᴴ := fun _ => rfl
  have e3 : ∀ (A B : HSp D) (z : WO B A), GlobalTheory.PairLift.adjO A B z = giA B ⬝ adj z ⬝ gA A := fun _ _ _ => rfl
  have g1 : ∀ A : HSp D, rat A.gram = gA A := fun _ => rfl
  have g2 : ∀ A : HSp D, rat A.gram⁻¹ = giA A := fun _ => rfl
  rw [e3, e3, e1, e1, e1, e2, e2, swapE_apply]
  simp only [e1, rat_mul, rat_conjTranspose, g1, g2, adj_add, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, giA_gA_cancel]

theorem res_dag_swap : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  intro D S T T' t ι C
  have key : ∀ (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (μ' : Measure (Mx D S.rank t))
      (𝓖' : Set (Mx D S.rank t)),
      (∀ G : Mx D t S.rank → ℂ, ∫ y in 𝓖', G (swapE S t y) ∂μ' = ∫ x in 𝓖, G x ∂μ) →
      ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) =
        GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
    intro μ 𝓖 μ' 𝓖' hI φ
    funext w'
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT, GlobalTheory.PairLift.dag, adjO_split]
    rw [integral_conj, hI (fun x => φ (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (x : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w'))]
  refine ⟨fun μ 𝓖 h => ?_, fun μ' 𝓖' h => ?_⟩
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t).symm (continuous_swapE_symm S t) (continuous_swapE S t)
      (swapE_symm_mem_iff S t) h
    refine ⟨_, _, h1, key μ 𝓖 _ _ fun G => ?_⟩
    exact (h2 fun y => G (swapE S t y)).trans (by simp)
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t) (continuous_swapE S t) (continuous_swapE_symm S t) (swapE_mem_iff S t) h
    exact ⟨_, _, h1, key _ _ μ' 𝓖' fun G => (h2 G).symm⟩

end GlobalTheory.TwistSwap
end
end

