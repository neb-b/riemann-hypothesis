module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotExistsExponentConditionCard
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRationalFramePeriodMatrixLogCove
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

private theorem differentiableOn_finsetProd' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Idx : Type}
    (u : Finset Idx) (f : Idx → E → ℂ) {S : Set E} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ u, f i s) S := by
  classical
  revert h
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  · intro a u ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S) :
    DifferentiableOn ℂ (fun s => (M s).det) S := by
  have hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)

theorem differentiableOn_inv_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S)
    (hu : ∀ s ∈ S, IsUnit (M s).det) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => (M s)⁻¹ i j) S := by
  have hdet : DifferentiableOn ℂ (fun s => (M s).det) S := differentiableOn_det_of_entries h
  have hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S := by
    have hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hk]
        exact h k l
    have := differentiableOn_det_of_entries hupd
    simpa only [Matrix.adjugate_apply] using this
  have hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S :=
    hdet.fun_inv fun s hs => (hu s hs).ne_zero
  have heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.fun_mul hadj

theorem differentiableOn_combMat_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g r : ℕ}
    {l : E → Fin r → Fin g → ℂ} {S : Set E} (ε : Matrix (Fin g) (Fin r) ℚ)
    (h : ∀ m k, DifferentiableOn ℂ (fun s => l s m k) S) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => combMat (l s) ε i j) S := by
  simp only [combMat, Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro m _
  exact (h m i).const_mul _

theorem differentiableOn_combMat_perTau : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  intro n a g r₀ r ζ lam α φ D hζ hlam hunit
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζ.differentiableOn
  have hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1) := by
    intro m k
    have h1 := differentiableOn_pi.1 hζd m
    exact differentiableOn_pi.1 h1 k
  have hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1) :=
    fun i j => differentiableOn_combMat_of_entries α hζe i j
  refine ⟨hA, ?_⟩
  intro i j
  set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT
  have hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s) := by
    refine differentiable_pi.2 fun k => ?_
    simp only [logExp]
    split_ifs
    · exact (differentiable_apply k).cexp
    · exact differentiable_apply k
  have hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T := by
    intro i j
    exact (hA i j).comp hexp.differentiableOn (fun s hs => hs.2)
  have hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T :=
    differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)
  have hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T := by
    intro i j
    exact (differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)
  simp only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_sum
  intro k _
  exact (hinvT i k).fun_mul (hBT k j)

end GlobalTheory.PeriodFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iotaR_injective_of (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (hU : R.toRealDat.LUnif) (i : Fin D.R.m) :
    Function.Injective (iotaR R i) := by
  have hj : Function.Injective ((R.FW i).j (sg0 D A3.A)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    exact ((hU i _).1 1 (fun _ => v) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hv
  exact (hM.HW i _).1.comp hj

end Gen

end GlobalTheory.EigSpanDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_on_ball_of_eq_on_logExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  intro n a ρ₁ X _ _ f h hρ hf hh hagree
  set U := Metric.ball (0 : Fin n → ℂ) ρ₁ with hUdef
  set D : Set (Fin n → ℂ) := {z | z ∈ U ∧ ∀ k : Fin n, (k:ℕ) < a → z k ≠ 0} with hDdef
  have hD : Set.EqOn f h D := by
    rintro z ⟨hzU, hz0⟩
    set s : Fin n → ℂ := fun k => if (k:ℕ) < a then Complex.log (z k) else z k with hsdef
    have hexp : logExp a s = z := by
      funext k
      simp only [logExp, s]
      split_ifs with hk
      · exact Complex.exp_log (hz0 k hk)
      · rfl
    have hz1 : ‖z‖ < ρ₁ := by simpa [U] using hzU
    have hnorm : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k) (lt_of_lt_of_le hz1 hρ)
    have hs : s ∈ logDom n a := by
      intro k
      simp only [s]
      split_ifs with hk
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.mpr (hz0 k hk)) (hnorm k)
      · exact hnorm k
    have := hagree s hs (by rw [hexp]; exact hzU)
    rwa [hexp] at this
  have hsub : U ⊆ closure D := by
    intro z hz
    let g : ℂ → (Fin n → ℂ) := fun t k => if (k:ℕ) < a then z k + t else z k
    have hg : Continuous g := by
      refine continuous_pi fun k => ?_
      by_cases hk : (k:ℕ) < a
      · simp only [g, hk, if_true]; fun_prop
      · simp only [g, hk, if_false]; fun_prop
    let T : Set ℂ := Set.range (fun k : Fin n => - z k)
    have hT : T.Finite := Set.finite_range _
    have hS : Dense (Set.univ \ T) := dense_univ.diff_finite hT
    have h0 : g 0 = z := by funext k; simp [g]
    have h1 : z ∈ closure (g '' (Set.univ \ T)) := by
      rw [← h0]
      exact image_closure_subset_closure_image hg
        (Set.mem_image_of_mem g (by rw [hS.closure_eq]; exact Set.mem_univ _))
    have h2 : U ∩ g '' (Set.univ \ T) ⊆ D := by
      rintro _ ⟨hU, t, ⟨-, htT⟩, rfl⟩
      refine ⟨hU, fun k hk => ?_⟩
      simp only [g, hk, if_true]
      intro heq
      exact htT ⟨k, by linear_combination -heq⟩
    exact closure_mono h2 (Metric.isOpen_ball.inter_closure ⟨hz, h1⟩)
  exact fun z hz => hD.of_subset_closure hf hh (fun x hx => hx.1) hsub hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.FaceSub

variable {X : Type} [AddCommGroup X]

theorem eq_of_toReal_sum_eq {p : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} (hu : LinearIndependent ℤ u)
    {r r' : Fin p → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ j, r' j • toReal (u j)) : r = r' := by
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin p → ℤ), ∑ j, c j • u j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c hc => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    exact funext (Fintype.linearIndependent_iff.1 hu c hc)
  have h0 : ∑ j, (r - r') j • toReal (u j) = ∑ k, (Fin.elim0 k : ℝ) • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self, Finset.univ_eq_empty, Finset.sum_empty]
  exact sub_eq_zero.1 (eq_zero_of_toReal_rel hind h0)

theorem eq_zero_of_toReal_eq_zero {β : LinearMap.BilinForm ℤ X} (h : toReal β = 0) : β = 0 :=
  LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.zero_apply] at this
    simpa using this

theorem exists_ray {p q : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} {v : Fin q → LinearMap.BilinForm ℤ X}
    (hu : LinearIndependent ℤ u) (hv : ∀ l, v l ≠ 0) (A : Fin q → ℝ) (B : Fin q → Fin p → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hB : ∀ l k', 0 ≤ B l k') (k : Fin p) (hk : toReal (u k) = ∑ l, A l • toReal (v l))
    (hBe : ∀ l, 0 < A l → toReal (v l) = ∑ k', B l k' • toReal (u k')) :
    ∃ l, 0 < A l ∧ ∃ c : ℝ, 0 < c ∧ toReal (v l) = c • toReal (u k) := by
  classical
  set B' : Fin q → Fin p → ℝ := fun l k' => if 0 < A l then B l k' else 0 with hB'
  have hB'0 : ∀ l k', 0 ≤ B' l k' := fun l k' => by
    simp only [hB']; split_ifs <;> [exact hB l k'; exact le_rfl]
  have hterm : ∀ l, A l • toReal (v l) = A l • ∑ k', B' l k' • toReal (u k') := fun l => by
    rcases (hA l).lt_or_eq with hl | hl
    · simp only [hB', if_pos hl]; rw [hBe l hl]
    · simp [← hl]
  have hsum : ∑ k', (if k' = k then (1 : ℝ) else 0) • toReal (u k') =
      ∑ k', (∑ l, A l * B' l k') • toReal (u k') := by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    rw [if_pos rfl, one_smul, hk]
    simp only [hterm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc := eq_of_toReal_sum_eq hu hsum
  have hk1 : ∑ l, A l * B' l k = 1 := by simpa using (congrFun hc k).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, A l * B' l k ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero hne] at hk1
    exact zero_ne_one hk1
  have hAl : 0 < A l := (hA l).lt_of_ne fun h0 => hl (by rw [← h0, zero_mul])
  have hoff : ∀ k', k' ≠ k → B l k' = 0 := fun k' hk' => by
    have h0 : ∑ l, A l * B' l k' = 0 := by simpa [hk'] using (congrFun hc k').symm
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hA l) (hB'0 l k'))).1 h0 l (Finset.mem_univ _)
    simpa [hB', if_pos hAl, hAl.ne'] using this
  have hvl : toReal (v l) = B l k • toReal (u k) := by
    rw [hBe l hAl, Finset.sum_eq_single k (fun b _ hb => by rw [hoff b hb, zero_smul]) (by simp)]
  refine ⟨l, hAl, B l k, (hB l k).lt_of_ne fun h0 => hv l (eq_zero_of_toReal_eq_zero ?_), hvl⟩
  rw [hvl, ← h0, zero_smul]

end GlobalTheory.PolFan.FaceSub


open GlobalTheory.PolFan.FaceSub in
theorem GlobalTheory.PolFan.eq_subfamily_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  intro O _ bar X _ _ m n δ γ hδ hγ h hδi hγi hδp hγp hγc hδn hγz hZ
  classical
  choose b hb hbe using hγc
  choose a ha hae using hZ
  have hsupp : ∀ j i, 0 < b j i → h (δ i) = 0 := fun j i hji => by
    have e := apply_eq_of_toReal_eq (hbe j) h
    rw [hγz j, Int.cast_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hb j i) (by exact_mod_cast hδn i))).1 e.symm i
      (Finset.mem_univ _)
    have h2 : ((h (δ i) : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hji.ne'
    exact_mod_cast h2
  have hex1 : ∀ i, h (δ i) = 0 → ∃ j, γ j = δ i := fun i hi => by
    obtain ⟨j, -, c, hc, e⟩ := exists_ray hδi hγi.ne_zero (a i hi) b (ha i hi) hb i (hae i hi) (fun l _ => hbe l)
    exact ⟨j, _root_.GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul bar (γ j) (δ i) (hγ j) (hδ i) (hγp j) (hδp i) c hc e⟩
  have hex2 : ∀ j, ∃ i, h (δ i) = 0 ∧ γ j = δ i := fun j => by
    obtain ⟨i, hbi, c, hc, e⟩ := exists_ray hγi hδi.ne_zero (b j)
      (fun i => if hi : h (δ i) = 0 then a i hi else 0) (hb j)
      (fun i j' => by split_ifs with hi <;> [exact ha i hi j'; exact le_rfl]) j (hbe j)
      (fun l hl => by rw [dite_eq_left (hsupp j l hl)]; exact hae l _)
    exact ⟨i, hsupp j i hbi, (_root_.GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul bar (δ i) (γ j) (hδ i) (hγ j) (hδp i) (hγp j) c hc e).symm⟩
  choose s hsZ hsγ using hex2
  have hsinj : Function.Injective s := fun j j' hjj => hγi.injective (by rw [hsγ j, hsγ j', hjj])
  refine ⟨⟨s, hsinj⟩, hsγ, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := hex1 i hi
    exact ⟨j, hδi.injective (show δ (s j) = δ i by rw [← hsγ j, hj])⟩
  · rintro ⟨j, rfl⟩
    exact hsZ j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmMapMulConst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrobSplit

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (s.map (fun x => x * c)).esymm k = c ^ k * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hk : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const',
    Multiset.prod_replicate, hk]
  ring

theorem galPol_lifts_ae : ∀ (D : D7) (cf : CharFrame D) (Rw : GlobalTheory.HeightCounting.RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), ValLL0 D cf → GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∀ π : D.naut.CG D.R.r, D.naut.csd π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) → ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf Rw Sb eig hV hE j hj1 hj2 σ hiso hgood π hcsd hloc
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  let j' : Fin D.R.m := ⟨j - 1, by omega⟩
  have hjj : (j' : ℕ) + 1 = j := by simp only [j']; omega
  have hfin : (bar ⁻¹' ((Sb : Set (PlE D.host)) ∪ {v | ¬ (cf.mu0 j').UnrAt v})).Finite :=
    (Sb.finite_toSet.union (GlobalTheory.Mem.UnrAe.finite_ramified _)).preimage hinj.injOn
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  by_contra hw'
  apply hw
  intro hsplit
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hw'
  obtain ⟨hSb, hunrμ⟩ := hw'
  obtain ⟨hc, -, hsp⟩ := hbar w
  have hPs : IsSplitPl D.host (bar w) := hsp hsplit
  have hE' := hE j' σ (by rw [hjj]; exact hiso) hgood (bar w) hPs hSb
  rw [hjj] at hE'
  obtain ⟨hunrP, heig⟩ := hE'
  rw [← hloc (bar w) hPs] at hunrP heig
  obtain ⟨hunrw, hfw⟩ := D.naut.csd_unr π (bar w) w hcsd (GlobalTheory.ToricDenomCheck.isConj_symm hc) hunrP
  have hfP : D.naut.frobEig (D.naut.locG π (bar w)) =
      (D.naut.frobEig (D.naut.locG π w)).map (fun x => x⁻¹) := by
    rw [hfw, Multiset.map_map]; simp
  have hcard : (D.naut.frobEig (D.naut.locG π w)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hunrw, D.naut.locG_dim]
  have hmemS : ∀ x, x ∈ (embLL0 D).fieldRange → x ∈ Set.range (embLL0 D) :=
    fun x h => (RingHom.mem_fieldRange).1 h
  have hNS : ∀ n : ℕ, (n : ℂ) ∈ (embLL0 D).fieldRange := fun n => natCast_mem _ n
  have hN0 : (Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.ConjPoly.normV_ne_zero (bar w)
  have hμ0 : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  obtain ⟨yμ, hyμ⟩ := hV.mu0 j' (bar w) hunrμ
  have hμS : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange :=
    ⟨yμ, by rw [hyμ]; simp [Formalism.L2.Host.HChar.valTw]⟩
  have hAk : ∀ k, 1 ≤ k → k ≤ D.R.r →
      (D.naut.frobEig (D.naut.locG π w)).esymm k ∈ (embLL0 D).fieldRange := by
    intro k hk1 hk2
    have h := heig k hk1 hk2
    rw [hfP, Multiset.map_map] at h
    have hfun : (fun a : ℂ => a⁻¹ * (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ (fun x : ℂ => x⁻¹) =
        fun x => x * ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
      funext x; simp [mul_assoc]
    rw [hfun, esymm_map_mul_const] at h
    have hd : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ≠ 0 := by
      simp [hμ0, hN0]
    have hdS : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∈ (embLL0 D).fieldRange :=
      Subfield.mul_mem _ (Subfield.inv_mem _ hμS) (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))
    have hpow : ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2)) ≠ 0 := pow_ne_zero _ hN0
    have heq : (D.naut.frobEig (D.naut.locG π w)).esymm k =
        D.what₂.embLL ↑(eig j σ k (bar w)) * ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2))⁻¹ *
          (((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
            ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ^ k)⁻¹ := by
      rw [h]; field_simp
    rw [heq]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ⟨eig j σ k (bar w), rfl⟩
      (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))) (Subfield.inv_mem _ (Subfield.pow_mem _ hdS _))
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Formalism.BasicNotions.Ranks.r]; omega⟩
  obtain ⟨q, hq⟩ := hr
  have hs : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) =
      ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹ := by
    have : ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) = -(q : ℂ) := by
      rw [hq]; push_cast; ring
    rw [this, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  unfold Formalism.MainNotions.N.galPol
  rw [D.naut.frobEig_tw _ _ hunrw, hs]
  have hBk : ∀ k, k ≤ D.R.r →
      ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).esymm k ∈
        (embLL0 D).fieldRange := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : Multiset.esymm ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)) 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [this]; exact Subfield.one_mem _
    rw [esymm_map_mul_const]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _)) _)
      (hAk k hk1 hk)
  have hBc : ((D.naut.frobEig (D.naut.locG π w)).map
      (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).card = D.R.r := by
    rw [Multiset.card_map, hcard]
  rcases le_or_gt n D.R.r with hn | hn
  · rw [Multiset.prod_X_sub_C_coeff _ (hBc.symm ▸ hn), hBc]
    exact hmemS _ (Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _)
      (hBk _ (by omega)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hBc]; exact hn)]
    exact ⟨0, map_zero _⟩

end GlobalTheory.CuspFrobSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_polFanCones_cover_realCone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  first | exact @GlobalTheory.PolCell.exists_finite_cover_rcone | exact GlobalTheory.PolCell.exists_finite_cover_rcone | (intros; apply GlobalTheory.PolCell.exists_finite_cover_rcone <;> assumption)
end

