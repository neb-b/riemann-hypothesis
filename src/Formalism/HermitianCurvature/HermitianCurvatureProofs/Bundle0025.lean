module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

namespace B2

theorem AB_nonneg (k r : ℕ) : (0 : ℝ) ≤ AB k r := by
  unfold AB
  positivity

theorem aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, inv_pow, inv_mul_cancel₀ (hp _), Complex.ofReal_one]
  · exact mul_one 1
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, mul_inv_cancel₀ (hp _), Complex.ofReal_one]

end B2

theorem bessel_lemma_from_reductions : Formalism.FourierDecayAlt.B.LemmaBFromSteps := by
  intro hFC hAe hFat hCC hDil hJ hRB hRA hU hJC hDB hPA hRP hEq hAdj
  unfold StepRegBound StepRegAverage StepUnfold StepJCont StepDilBeta at *
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA hInt hConj hDJ hCCI hCoef hXi
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  have h12 := hEq hFC hAe hFat hCC hDil hJ k r Wp Wq D A h0A
    (by apply hRB <;> assumption) (by apply hRA <;> assumption) (by apply hU <;> assumption)
    (by apply hJC <;> assumption) (by apply hDB <;> assumption)
  exact ⟨h12.1, h12.2, hAdj hPA hRP k r Wp Wq D A h12.2⟩

theorem adjointness_of_bessel_transform : Formalism.FourierDecayAlt.B.AssembleAdj := by
  intro hPA hRP k r Wp Wq _ _ _ _ _ _ D A hB2 UU Θ hStab hSm hCom F F' hCk hCk' hS hS' h1 h2 h3 h4 hIC
  have hT : ∀ τ, betaInfTau D τ (opApply Θ F) F' = betaInfTau D τ F (opAdj Θ F') := fun τ =>
    hRP k r Wp Wq D τ _ _ _ _ (hPA k r Wp Wq D UU Θ hStab hSm hCom F F' hCk hCk' hS hS' hIC)
  rw [hB2 _ _ h3 h2, hB2 _ _ h1 h4]
  first
  | (unfold betaInf; simp only [hT])
  | (simp only [betaInf, hT])
  | (unfold betaInf; rw [hT])

theorem adjointness_polynomially_bounded : Formalism.FourierDecayAlt.B.AssemblePoly := by
  intro hSC k r Wp Wq _ _ _ _ _ _ D A hA hCC hB3 Θ ε d hε hd hSm hCom hPoly F F' hF hF' hsF hsF'
  obtain ⟨hStab, hcl⟩ := hSC k r Wp Wq D A hA hCC
  obtain ⟨hs1, hs2, h1, h2, h3, h4, hIC⟩ := hcl Θ ε d hε hd hSm hPoly F F' hF hF' hsF hsF'
  have hCk : ∀ G : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) G →
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) G := by
    intro G hG
    obtain ⟨c, hc⟩ := hG
    unfold CCle at hc
    first
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2.1
    | exact hc.1.1
    | exact hc
  exact hB3 (GPos D) Θ hStab hSm hCom F F' (hCk F hF) (hCk F' hF') hs1 hs2 h1 h2 h3 h4 hIC

theorem bessel_function_trivial_index : Formalism.FourierDecayAlt.B.JtauOne := by
  unfold Formalism.FourierDecayAlt.B.JtauOne
  intro k r Wp Wq _ _ _ _ D F g
  unfold Jtau JF xiTau besselJ RealPlaceData.μSS
  unfold rho sgs
  congr 1
  funext p
  congr 1
  unfold psi cStd
  have hs : ∀ z : ℂ, star (Complex.exp z) = Complex.exp ((starRingEnd ℂ) z) :=
    fun z => (Complex.exp_conj z).symm
  rw [hs, ← Complex.exp_add]
  congr 1
  try unfold lam
  dsimp only
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  try unfold cStd
  ring_nf
  push_cast
  ring

private lemma star_ofReal_eq (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

theorem dilation_big_cell_formula : Formalism.FourierDecayAlt.B.DilBigCell := by
  unfold Formalism.FourierDecayAlt.B.DilBigCell
  intro k r c μ t₁ t₂ h1 h2
  rw [B2.aDil_inv k r t₁ h1]
  unfold aDil
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold bigCell esI
  beta_reduce
  split_ifs
  all_goals try first
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | rfl
    | (rw [one_mul, mul_one])
    | exact (congrArg (· * (1 : ℂ)) (one_mul _)).trans (mul_one _)
    | (simp; done)
    | (have e : (i : ℕ) - (r + k) = r - (j : ℕ) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       rw [e]
       try simp only [Fin.val_mk]
       push_cast
       simp only [inv_pow, inv_inv]
       ring)
    | (have e1 : r - (i : ℕ) = (j : ℕ) - (r + k) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       have e2 : r - (2 * r + k - (j : ℕ)) = (j : ℕ) - (r + k) := by omega
       simp only [Fin.val_mk, e1, e2, star_mul', star_ofReal_eq]
       push_cast
       ring)

private lemma star_ofReal_eq_self (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

theorem dilation_mem_group : Formalism.FourierDecayAlt.B.DilMem := by
  unfold Formalism.FourierDecayAlt.B.DilMem
  intro k r t ht
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  unfold GV UH aDil
  rw [Set.mem_setOf_eq, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Hpk
  beta_reduce
  split_ifs
  all_goals (try simp only [star_ofReal_eq_self, star_one, mul_one, one_mul, mul_zero, zero_mul, mul_neg])
  all_goals try first
    | rfl
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | (rw [show (j : ℕ) - (r + k) = r - (i : ℕ) by omega, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (hp _), Complex.ofReal_one])
    | (rw [show (i : ℕ) - (r + k) = r - (j : ℕ) by omega, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (hp _), Complex.ofReal_one])

theorem bessel_lemma_closed_form : Formalism.FourierDecayAlt.B.LemmaBClosedFromParts := by
  intro hXi hLB hSC hAP k r Wp Wq _ _ _ _ _ _ D A hA hInt hConj hDJ hCCI
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  obtain ⟨h1, h2, h3⟩ := hLB k r Wp Wq D Ξ A hA hInt hConj hDJ hCCI hCB hXI
  exact ⟨h1, h2, h3, hAP hSC k r Wp Wq D A h0A hCCI h3⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin
section
namespace Formalism.FourierDecayAlt.P.CutBP

noncomputable section

def KFinDSCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : B.Mat k r → (H →L[ℂ] H)) (Pm : H →L[ℂ] Wp) (Qm : Wq →L[ℂ] H),
    PI.UpqRep.IsHCParam lam ∧ PI.UpqRep.IsDSHpk k r ε lam σ ∧
    (∀ w, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (Qm w)) ∧
    (∀ x, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint Pm x)) ∧
    ∀ g ∈ B.GV k r, F g = Pm.comp ((σ g).comp Qm)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsSmoothExt
section
open Matrix Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem isClosed_GVt (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by
  have h0 : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) :=
    ((h0.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h0
  exact isClosed_eq hc continuous_const

theorem exists_smoothExt {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k r → E) (hF : B.CkOn (⊤ : ℕ∞) (B.GV k r) F) :
    ∃ Ft : Mt k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft ∧
      ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x) := by
  set s : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ B.GV k r} with hs
  have hloc : ∀ i : s, ∃ (U : Set (Mt k r)) (f' : Mt k r → E), IsOpen U ∧ (i : Mt k r) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' U ∧ ∀ x ∈ U, Matrix.of x ∈ B.GV k r → F (Matrix.of x) = f' x := by
    intro i
    obtain ⟨U, f', hU, hiU, hf', hfe⟩ := hF (Matrix.of (i : Mt k r)) i.2
    exact ⟨U, f', hU, hiU, hf', fun x hx hxG => hfe (Matrix.of x) hx hxG⟩
  choose U f' hU hiU hf' hfe using hloc
  have hcov : s ⊆ ⋃ i : s, U i := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hiU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Mt k r) (isClosed_GVt k r) U hU hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i x, ?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := f') fun i x hx => by
      have hxU : x ∈ U i := hρ i hx
      exact ((hf' i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
    exact contMDiff_iff_contDiff.1 h
  · intro x hx
    have hsum : ∑ᶠ i, ρ i x = 1 := ρ.sum_eq_one hx
    have heq : ∀ i, ρ i x • f' i x = ρ i x • F (Matrix.of x) := by
      intro i
      by_cases h0 : ρ i x = 0
      · simp [h0]
      · have hxU : x ∈ U i := hρ i (subset_tsupport _ h0)
        rw [hfe i x hxU hx]
    simp only [heq]
    rw [← finsum_smul, hsum, one_smul]

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
end
end

