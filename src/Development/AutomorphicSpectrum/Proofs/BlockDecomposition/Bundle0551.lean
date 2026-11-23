module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientWeylIntegral
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.RCellInv

variable {D : D7} {t ρ : ℕ}

theorem block_matrix_mul {n : ℕ} (a b c d a' b' c' d' : Mx D n n) :
    (blk4 a b c d * blk4 a' b' c' d' : Mx D (n + n) (n + n)) =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem mat_mul_mat {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem trace_adj_eq {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  rw [adj, Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm

theorem adj_gram (b₀ : HermE D ρ) : adj (b₀.1.map (incA D)) = b₀.1.map (incA D) := by
  ext i j
  have h := congrFun (congrFun b₀.2 i) j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply] at h ⊢
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg (incA D) h

theorem adj_pr (b₀ : HermE D ρ) (x y : Mx D ρ t) : adj (pr b₀ x y) = pr b₀ y x := by
  have adj_mul_local {l m n : ℕ} (a : Mx D l m) (b : Mx D m n) :
      adj (a * b) = adj b * adj a := by
    unfold adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [pr, adj_mul_local, adj_adj, adj_gram, Matrix.mul_assoc]

theorem pr_neg_left (b₀ : HermE D ρ) (x y : Mx D ρ t) : pr b₀ (-x) y = -pr b₀ x y := by
  simp only [pr, adj_neg, Matrix.neg_mul]

theorem trA_trace_pr_swap (b₀ : HermE D ρ) (x y : Mx D ρ t) :
    trA (Matrix.trace (pr b₀ y x)) = trA (Matrix.trace (pr b₀ x y)) := by
  rw [← adj_pr b₀ x y, trace_adj_eq]
  exact GlobalTheory.DualPairCheck.trace_cA _

theorem conj_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem det_neg_one (t : ℕ) :
    Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D)) =
      Units.map (incA D).toMonoidHom ((-1 : (D.host.E)ˣ) ^ t) := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]

theorem absA_det_neg_one (t : ℕ) : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) = 1 := by
  have h : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, neg_one_sq, map_one, map_one]
  exact (pow_eq_one_iff.1 h).resolve_right two_ne_zero

theorem weyl_sq {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D}
    {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω)
    {w : G D t} (hw : IsW w) (h : G D t) (y : Mx D ρ t) : Ω (w * (w * h)) y = Ω h (-y) := by
  have hm : mat (w * w) = blk4 (-1 : GL (Fin t) (AE D)).1 0 0 (adj ((-1 : GL (Fin t) (AE D))⁻¹).1) := by
    have hi : ((-1 : GL (Fin t) (AE D))⁻¹) = -1 := by
      rw [inv_eq_iff_mul_eq_one]
      simp
    have ha : adj (-1 : Mx D t t) = -1 := by
      rw [adj_neg, adj_one]
    rw [hi, mat_mul_mat, show mat w = _ from hw, block_matrix_mul]
    simp [ha]
  have hl := hΩ.levi (w * w) (-1) hm h y
  have hc : (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) : ℂ) = 1 := by
    rw [det_neg_one]
    have := hχ.2 ((-1 : (D.host.E)ˣ) ^ t)
    rw [this]
    simp
  rw [← mul_assoc, hl, hc, absA_det_neg_one]
  simp [npow]

end GlobalTheory.CompanionTheory.RCellInv


open GlobalTheory.CompanionTheory.RCellInv in
theorem GlobalTheory.CompanionTheory.RCellInv.fourier_inv : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  intro D t ρ ψ hψ χ hχ θ b₀ μ Ω hΩ nb hnb w hw b y₀
  have hint : ∀ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) =
      conj (Ω (w * nb b) y * ψ (trA (Matrix.trace (pr b₀ (-y₀) y)))) := by
    intro y
    have hneg : -trA (Matrix.trace (pr b₀ (-y₀) y)) = trA (Matrix.trace (pr b₀ y y₀)) := by
      rw [pr_neg_left, Matrix.trace_neg, trA_trace_pr_swap b₀ y₀ y]
      simp only [trA, map_neg, neg_neg]
    rw [map_mul, conj_char hψ, hneg, mul_comm]
  have hu := hΩ.unip (nb b) b.1 (hnb b) 1 y₀
  rw [mul_one] at hu
  simp only [hint]
  rw [integral_conj, ← hΩ.weyl w hw (w * nb b) (-y₀), weyl_sq hχ hΩ hw, neg_neg, hu]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceConjTransposeMulSelf
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.Orb
variable {D : D7}

def fro {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem fro_nonneg {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : 0 ≤ fro A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem fro_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) :
    fro (A * B) ≤ fro A * fro B := by
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  unfold fro
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem norm_entry_sq_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    ‖A i j‖ ^ 2 ≤ fro A := by
  unfold fro
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem continuous_fro {a b : ℕ} : Continuous (fro : Matrix (Fin a) (Fin b) ℂ → ℝ) := by
  unfold fro
  fun_prop

theorem trace_conjTranspose_mul_self {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    Matrix.trace (Aᴴ * A) = ((fro A : ℝ) : ℂ) := by
  unfold fro
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul']
  rfl

def nrm {m : ℕ} {n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ τ, |l τ| * fro (z τ)

theorem nrm_nonneg {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : 0 ≤ nrm l z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)

theorem entry_le_nrm {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (τ) (i j) :
    |l τ| * ‖z τ i j‖ ^ 2 ≤ nrm l z := by
  refine le_trans (mul_le_mul_of_nonneg_left (norm_entry_sq_le _ i j) (abs_nonneg _)) ?_
  exact Finset.single_le_sum (f := fun τ => |l τ| * fro (z τ)) (fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)) (Finset.mem_univ τ)

theorem norm_le_exp {w : ℂ} {d : ℝ} (hd : 0 < d) : ‖w‖ ≤ (1 / Real.sqrt d) * Real.exp (d * ‖w‖ ^ 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have h1 : Real.sqrt d * ‖w‖ ≤ Real.exp (d * ‖w‖ ^ 2) := by
    have h2 : d * ‖w‖ ^ 2 + 1 ≤ Real.exp (d * ‖w‖ ^ 2) := Real.add_one_le_exp _
    have h3 : (Real.sqrt d * ‖w‖) ^ 2 = d * ‖w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd.le]
    nlinarith [sq_nonneg (Real.sqrt d * ‖w‖ - 1)]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
  linarith [mul_comm (Real.sqrt d) ‖w‖]

theorem evalPoly_bound {m n : ℕ} (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ,
      ‖evalPoly q z‖ ≤ C * Real.exp (e * nrm l z) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro e he
    refine ⟨‖a‖, norm_nonneg _, fun z => ?_⟩
    simp only [evalPoly, MvPolynomial.eval_C]
    have : 1 ≤ Real.exp (e * nrm l z) := Real.one_le_exp (mul_nonneg he.le (nrm_nonneg _ _))
    nlinarith [norm_nonneg a]
  | add p q hp hq =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp e he
    obtain ⟨C₂, h₂, b₂⟩ := hq e he
    refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun z => ?_⟩
    have : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by simp [evalPoly]
    rw [this, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (b₁ z) (b₂ z))
  | mul_X p k hp =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp (e / 2) (by positivity)
    obtain ⟨τ, i, j, b⟩ := k
    have hlt : 0 < |l τ| := abs_pos.2 (hl τ)
    set d : ℝ := e / 2 * |l τ| with hd
    have hd0 : 0 < d := by positivity
    refine ⟨C₁ * (1 / Real.sqrt d), by positivity, fun z => ?_⟩
    have hm : evalPoly (p * MvPolynomial.X (τ, i, j, b)) z = evalPoly p z *
        (if b then conj (z τ i j) else z τ i j) := by simp [evalPoly]
    have hx : ‖(if b then conj (z τ i j) else z τ i j)‖ = ‖z τ i j‖ := by
      split_ifs <;> simp
    rw [hm, norm_mul, hx]
    have h1 := norm_le_exp (w := z τ i j) hd0
    have h2 : Real.exp (d * ‖z τ i j‖ ^ 2) ≤ Real.exp (e / 2 * nrm l z) := by
      apply Real.exp_le_exp.2
      have := entry_le_nrm l z τ i j
      rw [hd, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : ‖z τ i j‖ ≤ (1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc ‖evalPoly p z‖ * ‖z τ i j‖
        ≤ (C₁ * Real.exp (e / 2 * nrm l z)) * ((1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z)) :=
          mul_le_mul (b₁ z) h3 (norm_nonneg _) (by positivity)
      _ = C₁ * (1 / Real.sqrt d) * Real.exp (e * nrm l z) := by
          have : Real.exp (e * nrm l z) = Real.exp (e / 2 * nrm l z) * Real.exp (e / 2 * nrm l z) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring

end GlobalTheory.CompanionTheory.ThTot.Orb

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerCompactPart
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CentOk

theorem centraliser_hyps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  intro G _ _ _ _ θ hθ K I C δ hK hI hC hcpt x
  have hTc : IsClosed (twCent θ δ : Set G) := by
    have : (twCent θ δ : Set G) = {g | g * δ = δ * θ g} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hconj : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  constructor
  · have hKx : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.image hconj
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨hg.1, ?_⟩
    have hzp : (Subgroup.zpowers g : Set G) ⊆ (K.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
      (Subgroup.zpowers_le (G := G) (H := K.map (MulAut.conj x).toMonoidHom)).2 hg.2
    exact hKx.of_isClosed_subset isClosed_closure (closure_minimal hzp hKx.isClosed)
  · set A : Subgroup G := I.map (MulAut.conj x).toMonoidHom with hA
    have hAo : IsOpen (A : Set G) := by
      rw [hA, Subgroup.coe_map]
      exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hI
    have hHc : IsCompact (cptPart (twCent θ δ) : Set G) := by
      rw [hcpt, Subgroup.coe_inf]
      exact hC.inter_left hTc
    have hHT : cptPart (twCent θ δ) ≤ twCent θ δ := by
      rw [hcpt]; exact inf_le_left
    have e : (twCent θ δ ⊓ A) ⊓ cptPart (twCent θ δ) = A ⊓ cptPart (twCent θ δ) := by
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hHT h.2, h.1⟩, h.2⟩⟩
    rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
    haveI : CompactSpace (cptPart (twCent θ δ)) := isCompact_iff_compactSpace.mp hHc
    have ho : IsOpen ((A.subgroupOf (cptPart (twCent θ δ)) : Subgroup _) : Set (cptPart (twCent θ δ))) :=
      hAo.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.CentOk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitTransport

theorem unitConds_of_homeo : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  unfold GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, (hK d).2 h2, ?_, ?_⟩
  · funext x
    rw [hf x, h1]
    simp only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]
  · unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    rw [SetLike.mem_coe, hK t]
    have hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d) := by
      have htd : t * d = d * θ t := ht
      show e t * e d = e d * θ' (e t)
      rw [← hθ, ← map_mul e, ← map_mul e, htd]
    have hcl : closure (Subgroup.zpowers (e t) : Set G') =
        e '' closure (Subgroup.zpowers t : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        refine map_mem_closure e.symm.continuous hy ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩
      · rintro y ⟨x, hx, rfl⟩
        refine map_mem_closure e.continuous hx ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩
    have hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
      rw [hcl]
      exact hc.image e.continuous
    unfold GlobalTheory.BCT.cptPart at h3
    exact h3 (Subgroup.subset_closure (And.intro hte hce))
  · intro y hy
    have hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K' := by
      rw [← hθ, ← map_inv e, ← map_mul e, ← map_mul e]
      exact (hK _).1 hy
    obtain ⟨t', ht', k', hk', hyt⟩ := h4 (e y) hy'
    refine ⟨e.symm t', ?_, e.symm k', ?_, ?_⟩
    · show e.symm t' * d = d * θ (e.symm t')
      apply e.injective
      rw [map_mul, map_mul, hθ, e.apply_symm_apply]
      exact ht'
    · rw [hK, e.apply_symm_apply]
      exact hk'
    · apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hyt

end GlobalTheory.CompanionTheory.UnitTransport
end

