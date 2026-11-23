module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem triv_mul {θ : InfFam D} {τ : D.what₂.Tau} {a b : G D n} (ha : IsTrivAt θ τ a) (hb : IsTrivAt θ τ b) :
    IsTrivAt θ τ (a * b) := by
  unfold IsTrivAt at *
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', ha, hb, Matrix.mul_one]

theorem triv_inv {θ : InfFam D} {τ : D.what₂.Tau} {a : G D n} (ha : IsTrivAt θ τ a) : IsTrivAt θ τ a⁻¹ := by
  unfold IsTrivAt at *
  have h : compAt θ τ (mat a⁻¹) * compAt θ τ (mat a) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rwa [ha, Matrix.mul_one] at h

theorem triv_one {θ : InfFam D} {τ : D.what₂.Tau} : IsTrivAt θ τ (1 : G D n) := by
  unfold IsTrivAt; rw [GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']

theorem eq_one_of_triv_ι {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {y : GR n}
    (hy : IsTrivAt θ τ (ι y)) : y = 1 := by
  unfold IsTrivAt at hy
  rw [(hι.2 y).1] at hy
  have h1 : mR y = 1 := by
    have h2 : (mR y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        (1 : M2 n).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      rw [Matrix.submatrix_one_equiv]; exact hy
    have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h2
    simpa using this
  exact Subtype.ext (Units.ext h1)

theorem uniq_dec {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {a a' : G D n} {y y' : GR n}
    (ha : IsTrivAt θ τ a) (ha' : IsTrivAt θ τ a') (h : a * ι y = a' * ι y') : y = y' := by
  have h2 : ι (y * y'⁻¹) = a⁻¹ * a' := by
    rw [map_mul, map_inv]
    calc ι y * (ι y')⁻¹ = a⁻¹ * (a * ι y) * (ι y')⁻¹ := by group
      _ = a⁻¹ * (a' * ι y') * (ι y')⁻¹ := by rw [h]
      _ = a⁻¹ * a' := by group
  have : y * y'⁻¹ = 1 := eq_one_of_triv_ι hι (by rw [h2]; exact triv_mul (triv_inv ha) ha')
  exact mul_inv_eq_one.mp this

theorem blocks_of_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {M : Mx D (n + n) (n + n)}
    (hM : ∀ τ', τ' ≠ τ → compAt θ τ' M = 1) (hMf : M.map (finPart D) = 1) {α β γ δ : Matrix (Fin n) (Fin n) ℂ}
    (hτ : compAt θ τ M = blk4 α β γ δ) :
    ∃ A B C E' : Mx D n n, M = blk4 A B C E' ∧ compAt θ τ A = α ∧ compAt θ τ B = β ∧ compAt θ τ C = γ ∧
      compAt θ τ E' = δ ∧ (∀ τ', τ' ≠ τ → compAt θ τ' A = 1 ∧ compAt θ τ' B = 0 ∧ compAt θ τ' C = 0 ∧ compAt θ τ' E' = 1) ∧
      A.map (finPart D) = 1 ∧ B.map (finPart D) = 0 ∧ C.map (finPart D) = 0 ∧ E'.map (finPart D) = 1 := by
  obtain ⟨B, E', hBE⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.exists_blocks M
  set A := blkA M
  set C := GlobalTheory.CompanionTheory.SwUnf.lowerC M
  refine ⟨A, B, C, E', hBE, ?_⟩
  have h0 := hτ
  rw [hBE, component_block_matrix] at h0
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h0
  refine ⟨e1, e2, e3, e4, fun τ' hτ' => ?_, ?_⟩
  · have h1 := hM τ' hτ'
    rw [hBE, component_block_matrix, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩
  · have h1 := hMf
    rw [hBE, GlobalTheory.StdUnn.Frame.block_matrix_map, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩

theorem eq_of_comps {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {X Y : Mx D n n} (hτ : compAt θ τ X = compAt θ τ Y)
    (hτ' : ∀ τ', τ' ≠ τ → compAt θ τ' X = compAt θ τ' Y) (hf : X.map (finPart D) = Y.map (finPart D)) : X = Y := by
  refine mx_ext hθ (fun τ'' => ?_) hf
  by_cases h : τ'' = τ
  · subst h; exact hτ
  · exact hτ' τ'' h

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRightOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem convRight_of (hE : EisStrong) : ConvRight := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR
  have hn : 0 < n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hsec : IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) :=
    GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 h𝓕 ω hS.hω l hS.hl s hS.hs Φ
      hS.hΦ
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ :=
    hE D n hn χ V.rank hS.hχ hS.hη H hS.hH (s0 V n) _ hsec (s0 V n)
  refine ⟨σ, fun z hz g => ?_⟩
  obtain ⟨u, hu, hb⟩ := (hconv z hz).1 {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hb g rfl q) hu

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FtLocEqKer
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ))

theorem ftLoc_eq_ker (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (v : Fin m → Fin n → ℂ) :
    ftLoc ε t f v = ∫ u, f u * ker ε t v u := rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem integrand_eq {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    tens θ τ fr f Ψ y * ψ (trA (Matrix.trace (inner V x y))) =
      (f (piF θ τ fr y) * ker ε (tLoc l τ) (piF θ τ fr x) (piF θ τ fr y)) * Bw ψ V θ τ fr Ψ x y := by
  have hsplit : inner V x y = inner V x (y - sIns τ fr (piF θ τ fr y)) + inner V x (sIns τ fr (piF θ τ fr y)) := by
    rw [← GlobalTheory.CompanionTheory.EisCovar.Weyl.inner_add_right, sub_add_cancel]
  have hψ2 : ψ (trA (Matrix.trace (inner V x y))) =
      ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y))))) *
        ψ (trA (Matrix.trace (inner V x (sIns τ fr (piF θ τ fr y))))) := by
    rw [hsplit, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Weyl.trA_add, AddChar.map_add_eq_mul]
  rw [hψ2, psi_inner_sIns hθ hl hfr]
  have hp : (fr⁻¹ * compAt θ τ y : Matrix (Fin V.rank) (Fin n) ℂ) = piF θ τ fr y := rfl
  unfold Bw tens ker
  rw [hp]
  ring

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def ptX {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) : Fin m × Fin n × Bool → ℂ := fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

theorem evX_eq_eval {m : ℕ} (Q : PX m n) (u : Matrix (Fin m) (Fin n) ℂ) : evX Q u = eval (ptX u) Q := rfl

theorem ptX_add_smul {m : ℕ} (u w : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptX (u + (t : ℂ) • w) = ptX u + (t : ℂ) • ptX w := by
  funext k
  simp only [ptX, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem gAway_add_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    gAway V l s τ (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) = gAway V l s τ z := by
  have hz : ∀ τ', τ' ≠ τ → (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) τ' = z τ' := by
    intro τ' h
    rw [Pi.add_apply, Pi.smul_apply, dirAt_ne h, smul_zero, add_zero]
  delta gAway
  beta_reduce
  congr 2
  refine Finset.sum_congr rfl fun τ' hτ' => ?_
  rw [hz τ' (by simpa using hτ')]

theorem gaussian_vacuum_add_line {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (x : Mx D V.rank n)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    psi0 θ V n l s τ (x + lineAt θ τ X t) = psi0 θ V n l s τ x := by
  obtain ⟨-, hfinL, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  have h1 : (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) =
      (fun τ' => compAt θ τ' x) + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X := by
    funext τ'
    have hadd : compAt θ τ' (x + lineAt θ τ X t) = compAt θ τ' x + compAt θ τ' (lineAt θ τ X t) := by
      ext i j
      show (θ τ') (infPart D ((x + lineAt θ τ X t) i j)) =
        (θ τ') (infPart D (x i j)) + (θ τ') (infPart D (lineAt θ τ X t i j))
      rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add (f := _), map_add (f := _)]
    rw [hadd, hcomp t τ', Pi.add_apply, Pi.smul_apply]
    by_cases h : τ' = τ
    · rw [if_pos h, h, dirAt_self]
    · rw [if_neg h, dirAt_ne h, smul_zero]
  have h2 : (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = (fun i j => finPart D (x i j)) := by
    funext i j
    have h0 : finPart D (lineAt θ τ X t i j) = 0 := congrFun (congrFun (hfinL t) i) j
    rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add (f := _), h0, add_zero]
  show gAway V l s τ (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) *
      g0 D V.rank n (fun i j => finPart D ((x + lineAt θ τ X t) i j)) =
    gAway V l s τ (fun τ' => compAt θ τ' x) * g0 D V.rank n (fun i j => finPart D (x i j))
  rw [h1, h2, gAway_add_dirAt]

private theorem hasDerivAt_mvPolynomial_eval_line_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (a v : σ → ℂ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (a + (t : ℂ) • v) p)
      (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) 0 := by
  induction p using MvPolynomial.induction_on
  next r =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : HasDerivAt (fun t : ℝ => (a + (t : ℂ) • v) i) (v i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have h2 := (h1.mul_const (v i)).const_add (a i)
      simpa using h2
    have h := hp.mul hX
    simp only [map_mul, MvPolynomial.eval_X]
    refine h.congr_deriv ?_
    have hk : ∀ k, MvPolynomial.eval a (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i +
          (if i = k then MvPolynomial.eval a p else 0) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      split_ifs with h
      · simp only [map_one, mul_one]
        ring
      · simp only [map_zero, mul_zero, zero_add, add_zero]
        ring
    have hs1 : ∑ k, v k * (MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i) =
        (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) * a i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, v k * (if i = k then MvPolynomial.eval a p else 0) = MvPolynomial.eval a p * v i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        ring
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hk, mul_add, Finset.sum_add_distrib, hs1, hs2, Complex.ofReal_zero, zero_smul, add_zero]

private theorem hasDerivAt_norm_sq_add_smul_zero (u w : ℂ) :
    HasDerivAt (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) (2 * (star u * w).re) 0 := by
  have h : (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) =
      fun t : ℝ => (u.re + t * w.re) * (u.re + t * w.re) + (u.im + t * w.im) * (u.im + t * w.im) := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => u.re + t * w.re) w.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.re).const_add u.re
  have h2 : HasDerivAt (fun t : ℝ => u.im + t * w.im) w.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).const_add u.im
  refine ((h1.mul h1).add (h2.mul h2)).congr_deriv ?_
  show _ = 2 * ((starRingEnd ℂ) u * w).re
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem hasDerivAt_gs_line_zero {m : ℕ} (c : ℝ) (U W : Matrix (Fin m) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gs c (U + (t : ℂ) • W))
      (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) 0 := by
  have hr : HasDerivAt (fun t : ℝ => c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2)
      (c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re) 0 := by
    refine HasDerivAt.const_mul c ?_
    first
      | exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
      | exact HasDerivAt.sum fun a _ => HasDerivAt.sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
  have hn : HasDerivAt (fun t : ℝ => -((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ))
      (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ)) 0 := hr.ofReal_comp.neg
  have hc := hn.cexp
  have e0 : (fun t : ℝ => gs c (U + (t : ℂ) • W)) =
      fun t : ℝ => Complex.exp (-((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ)) := by
    funext t
    rfl
  rw [e0]
  refine hc.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rfl

theorem annS_tens {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (X : Matrix (Fin V.rank) (Fin n) ℂ) (x : Mx D V.rank n) :
    annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) x =
      (∑ k, ptX (fr⁻¹ * X) k * eval (ptX (fr⁻¹ * compAt θ τ x)) (pderiv k Q)) *
        gs (cLoc l τ) (fr⁻¹ * compAt θ τ x) * psi0 θ V n l s τ x := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  set c := cLoc l τ with hc
  set z := compAt θ τ x with hz
  set U : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * z with hU
  set W : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * X with hW
  set Ψx := psi0 θ V n l s τ x with hΨ
  have hadd : ∀ y : Mx D V.rank n, compAt θ τ (x + y) = z + compAt θ τ y := by
    intro y
    ext i j
    show (θ τ) (infPart D ((x + y) i j)) = (θ τ) (infPart D (x i j)) + (θ τ) (infPart D (y i j))
    rw [show (x + y) i j = x i j + y i j from rfl, map_add (f := _), map_add (f := _)]
  have hcz : ∀ t : ℝ, compAt θ τ (x + lineAt θ τ X t) = z + (t : ℂ) • X := by
    intro t
    rw [hadd, hcomp t τ, if_pos rfl]
  have hφ : ∀ t : ℝ, tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t) =
      eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx := by
    intro t
    have e1 : fr⁻¹ * compAt θ τ (x + lineAt θ τ X t) = U + (t : ℂ) • W := by
      rw [hcz t, Matrix.mul_add, Matrix.mul_smul]
    show fP c Q (fr⁻¹ * compAt θ τ (x + lineAt θ τ X t)) * psi0 θ V n l s τ (x + lineAt θ τ X t) = _
    rw [e1, gaussian_vacuum_add_line hθ V l s τ x X t]
    show evX Q (U + (t : ℂ) • W) * gs c (U + (t : ℂ) • W) * Ψx = _
    rw [evX_eq_eval, ptX_add_smul]
  have hderiv : HasDerivAt (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t))
      ((∑ k, ptX W k * eval (ptX U) (pderiv k Q)) * gs c U * Ψx +
        eval (ptX U) Q * (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) * Ψx) 0 := by
    have hP := hasDerivAt_mvPolynomial_eval_line_zero Q (ptX U) (ptX W)
    have hG := hasDerivAt_gs_line_zero c U W
    rw [show (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) =
        fun t : ℝ => eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx from funext hφ]
    refine ((hP.mul hG).mul_const Ψx).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    ring
  have hφx : tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = eval (ptX U) Q * gs c U * Ψx := by
    have h0 := hφ 0
    simp only [map_zero, add_zero, Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have hdet : IsUnit fr.det := hfr.1
  have hdetH : IsUnit frᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  have hGs : gramAt D V τ * s τ = (fr⁻¹)ᴴ * fr⁻¹ := by
    have h := hfr.2.2
    calc gramAt D V τ * s τ = (frᴴ)⁻¹ * (frᴴ * (gramAt D V τ * s τ) * fr) * fr⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
            ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
      _ = (fr⁻¹)ᴴ * fr⁻¹ := by
          rw [h, Matrix.mul_one, Matrix.conjTranspose_nonsing_inv]
  have e1' : ∑ a, ∑ i, 2 * (star (U a i) * W a i).re = 2 * (Uᴴ * W).trace.re := by
    show _ = 2 * (∑ i, (Uᴴ * W) i i).re
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have e2' : Uᴴ * W = zᴴ * (gramAt D V τ * s τ) * X := by
    rw [hGs]
    simp only [hU, hW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e3' : (zᴴ * (gramAt D V τ * s τ) * X).trace.re = (Xᴴ * (gramAt D V τ * s τ) * z).trace.re := by
    have h : Xᴴ * (gramAt D V τ * s τ) * z = (zᴴ * (gramAt D V τ * s τ) * X)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hM τ).eq, Matrix.mul_assoc]
    rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  have hc' : c = 2 * Real.pi * |l τ| := rfl
  have hlin : GlobalTheory.StdUnn.linF V l s τ X z = ((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ) := by
    show ((4 * Real.pi * |l τ| * (Xᴴ * (gramAt D V τ * s τ) * z).trace.re : ℝ) : ℂ) = _
    congr 1
    rw [e1', e2', e3', hc']
    ring
  show deriv (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) 0 +
      GlobalTheory.StdUnn.linF V l s τ X z * tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = _
  rw [hderiv.deriv, hφx, hlin]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

theorem alg_id (Z R : ℂ) (hZ : Z ≠ 0) (hR : R ≠ 0) (k j : ℤ) (p q m : ℕ) (hm : p + q = m) (hj : k - m = j + j) :
    (Z / R) ^ k * R ^ (m : ℤ) = (Z * (Z / R ^ 2)) ^ (k - j) * ((Z / R ^ 2) ^ (-(p : ℤ)) * (Z / R ^ 2) ^ (-(q : ℤ))) := by
  have hk : k = (m : ℤ) + j + j := by omega
  have hkj : k - j = (m : ℤ) + j := by omega
  have hpq : -(p : ℤ) + -(q : ℤ) = -(m : ℤ) := by omega
  rw [← zpow_add₀ (div_ne_zero hZ (pow_ne_zero 2 hR)), hpq, hkj, hk]
  have hR2 : (R ^ 2 : ℂ) = R * R := by ring
  rw [hR2]
  simp only [div_eq_mul_inv, mul_zpow, _root_.inv_zpow, zpow_add₀ hZ, zpow_add₀ hR, _root_.zpow_neg, zpow_natCast, inv_inv, mul_inv]
  have h1 : Z ^ m ≠ 0 := pow_ne_zero _ hZ
  have h2 : R ^ m ≠ 0 := pow_ne_zero _ hR
  have h3 : Z ^ j ≠ 0 := zpow_ne_zero _ hZ
  have h4 : R ^ j ≠ 0 := zpow_ne_zero _ hR
  field_simp
  ring_nf
  rw [inv_pow]
  field_simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

