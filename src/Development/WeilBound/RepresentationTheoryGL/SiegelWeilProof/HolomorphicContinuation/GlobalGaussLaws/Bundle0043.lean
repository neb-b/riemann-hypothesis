module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0042
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
section
namespace PositivityTheory.Rg.Sw.Glob

theorem awayFact_of (hA : AwayAct) (hD : DecompAway) : AwayFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  have hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι := by
    obtain ⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩ := hC
    exact ⟨hθ, hι⟩
  obtain ⟨x, y, hx, hg, -⟩ := hD D n θ τ ι hθι.1 hθι.2 g
  obtain ⟨A, hA'⟩ := hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx
  exact ⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtMulOfOne
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

def AG (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop :=
  IsTrivAt θ τ x ∧ ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))

def AgreeAway {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x x' : Mx D m k) : Prop :=
  (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') ∧ x.map (finPart D) = x'.map (finPart D)

theorem mem_closure_AG (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | AG θ τ x} :=
  closure_triv hG hDA hθ hι x hx

theorem exists_w (D : D7) (n : ℕ) : ∃ w : G D n, mat w = blk4 0 1 (-1) 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.SiegelCells.exists_wPart (D := D) (n := n) n
  refine ⟨g, hg.trans ?_⟩
  have hL : GlobalTheory.SiegelCells.lastDiag (AE D) n n = 1 := by
    unfold GlobalTheory.SiegelCells.lastDiag
    rw [← Matrix.diagonal_one]
    congr 1; funext i; simp
  rw [GlobalTheory.SiegelCells.wMat, hL, sub_self]

theorem compAt_b_zero {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {b : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 1 b 0 1) : compAt θ τ b = 0 := by
  have h1 : compAt θ τ (mat x) = blk4 1 (compAt θ τ b) 0 1 := by rw [h, component_block_matrix, compAt_one', compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 1 (compAt θ τ b) 0 1 := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).2.1.symm

theorem compAt_a_one {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {a d : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 a 0 0 d) : compAt θ τ a = 1 := by
  have h1 : compAt θ τ (mat x) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by rw [h, component_block_matrix, compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).1.symm

theorem compAt_mul_of_one {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x : Mx D m k) (a : Mx D k k)
    (ha : compAt θ τ a = 1) : compAt θ τ (x ⬝ a : Mx D m k) = compAt θ τ x := by
  rw [compAt_mul', ha, Matrix.mul_one]

theorem agree_mul_right {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} {x x' : Mx D m k} (a : Mx D k k)
    (h : AgreeAway θ τ x x') : AgreeAway θ τ (x ⬝ a : Mx D m k) (x' ⬝ a : Mx D m k) := by
  refine ⟨fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_mul', compAt_mul', h.1 τ' hτ']
  · rw [Matrix.map_mul, Matrix.map_mul, h.2]

theorem unipArg_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) (V : HSp D) {b : Mx D n n}
    (hb : compAt θ τ b = 0) {x x' : Mx D V.rank n} (h : AgreeAway θ τ x x') :
    halfTr (Matrix.trace (b ⬝ inner V x x : Mx D n n)) = halfTr (Matrix.trace (b ⬝ inner V x' x' : Mx D n n)) := by
  have htr : ∀ (R : Type) [CommRing R] (f : AE D →+* R) (M : Mx D n n), f (Matrix.trace M) = Matrix.trace (M.map f) := by
    intro R _ f M
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum f _ _
  have hinner : ∀ τ'', τ'' ≠ τ → compAt θ τ'' (inner V x x) = compAt θ τ'' (inner V x' x') := by
    intro τ'' hτ''
    have hx := h.1 τ'' hτ''
    have hadj : compAt θ τ'' (adj x) = compAt θ τ'' (adj x') := by
      ext i j
      have := congrFun (congrFun hx j) i
      simp only [compAt_eq, Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [cθ_cA hθ, cθ_cA hθ, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [compAt_mul', compAt_mul', compAt_mul', compAt_mul', hadj, hx]
  have hfin : (inner V x x).map (finPart D) = (inner V x' x').map (finPart D) := by
    have hadj : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      have := congrFun (congrFun h.2 j) i
      simp only [Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [finPart_cA, finPart_cA, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hadj, h.2]
  congr 1
  apply ae_ext hθ
  · intro τ''
    rw [htr, htr, ← compAt_eq, ← compAt_eq, compAt_mul', compAt_mul']
    by_cases hτ : τ'' = τ
    · subst hτ; rw [hb, Matrix.zero_mul, Matrix.zero_mul]
    · rw [hinner τ'' hτ]
  · rw [htr, htr, Matrix.map_mul, Matrix.map_mul, hfin]

theorem exists_change_tau {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (xs x0 : Mx D m k) :
    ∃ x1 : Mx D m k, compAt θ τ x1 = compAt θ τ x0 ∧ AgreeAway θ τ x1 xs := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ (compAt θ τ x0 - compAt θ τ xs)
  refine ⟨xs + lineAt θ τ (compAt θ τ x0 - compAt θ τ xs) 1, ?_, fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_add', hcomp 1 τ, if_pos rfl]; simp
  · rw [compAt_add', hcomp 1 τ', if_neg hτ', add_zero]
  · rw [Matrix.map_add _ (map_add (finPart D)), hfin 1, add_zero]

theorem levi_blocks (g : G D n) {a d : Mx D n n} (h : mat g = blk4 a 0 0 d) :
    ∃ a' : GL (Fin n) (AE D), a'.1 = a ∧ d = adj (a'⁻¹).1 := by
  obtain ⟨-, h2, -, -⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.unitary_rel g h
  simp only [adj_zero, Matrix.zero_mul, neg_zero, zero_add] at h2
  have h3 : adj d * a = 1 := by
    have := congrArg adj h2
    rwa [adj_mul, adj_adj, adj_one] at this
  have h4 : a * adj d = 1 := mul_eq_one_comm.mp h3
  refine ⟨⟨a, adj d, h4, h3⟩, rfl, ?_⟩
  show d = adj (adj d)
  rw [adj_adj]

theorem mat_w_conj {w x : G D n} (hw : mat w = blk4 0 1 (-1) 0) {c : Mx D n n} (hx : mat x = blk4 1 0 c 1) :
    mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := by
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv w hw, hx, hw]
  simp [adj_zero, adj_one, adj_neg, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]

theorem trivAt_conj {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (w : G D n) (hx : IsTrivAt θ τ x) :
    IsTrivAt θ τ (w⁻¹ * x * w) := by
  unfold IsTrivAt at *
  have hw : compAt θ τ (mat w⁻¹) * compAt θ τ (mat w) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', compAt_mul', hx, Matrix.mul_one, hw]

theorem exists_compAt {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    ∃ x : Mx D m k, compAt θ τ x = M := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ M
  exact ⟨lineAt θ τ M 1, by rw [hcomp 1 τ, if_pos rfl]; simp⟩

theorem exists_sch_ne {m k : ℕ} (u0 : Fin m → Fin k → ℂ) : ∃ f : (Fin m → Fin k → ℂ) → ℂ, IsSch f ∧ f u0 ≠ 0 := by
  let b : ContDiffBump u0 := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => ((b u : ℝ) : ℂ), ?_, ?_⟩
  · have hc : HasCompactSupport (fun u => ((b u : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun u => ((b u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
    exact ⟨hc.toSchwartzMap hs, rfl⟩
  · have : b u0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [this]

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LieCPf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LieCPfH

variable {D : D7} {n : ℕ}

theorem sgn_sq {m : ℕ} (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> simp

theorem diag_sgn_sq {m : ℕ} (ε : Fin m → Bool) :
    Matrix.diagonal (sgn ε) * Matrix.diagonal (sgn ε) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact sgn_sq ε a

theorem exp_preserves {m : ℕ} (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) (hX : IsUe ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ * Matrix.diagonal (sgn ε) * NormedSpace.exp ((t : ℂ) • X) =
      Matrix.diagonal (sgn ε) := by
  set J := Matrix.diagonal (sgn ε) with hJdef
  have hJJ : J * J = 1 := diag_sgn_sq ε
  have hJu : IsUnit J := by
    refine (Matrix.isUnit_iff_isUnit_det J).2 ?_
    have h := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h)
  have hJinv : J⁻¹ = J := Matrix.inv_eq_left_inv hJJ
  set Y : Matrix (Fin m) (Fin m) ℂ := (t : ℂ) • X with hY
  have hXs : Xᴴ = J * (-X) * J := by
    have h1 : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(J * X) * J := by rw [h1]
      _ = J * (-X) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
  have hYs : Yᴴ = J * (-Y) * J⁻¹ := by
    rw [hJinv, hY, Matrix.conjTranspose_smul, hXs]
    have : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [this]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hE : (NormedSpace.exp Y)ᴴ = J * NormedSpace.exp (-Y) * J := by
    rw [← Matrix.exp_conjTranspose, hYs, Matrix.exp_conj J (-Y) hJu, hJinv]
  have hneg : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl Y).neg_left), neg_add_cancel, NormedSpace.exp_zero]
  rw [hE]
  calc J * NormedSpace.exp (-Y) * J * J * NormedSpace.exp Y
        = J * (NormedSpace.exp (-Y) * NormedSpace.exp Y) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    _ = J := by rw [hneg, Matrix.mul_one]

theorem uh_frame {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : IsUe ε X) (t : ℝ) :
    (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  set E := NormedSpace.exp ((t : ℂ) • X)
  set G := gramAt D V τ
  set J := Matrix.diagonal (sgn ε)
  have hfu : IsUnit fr.det := hfr.1
  have hG : frᴴ * G * fr = J := hfr.2.1
  have hEJ : Eᴴ * J * E = J := exp_preserves ε X hX t
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hfu
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hGJ : G = (fr⁻¹)ᴴ * J * fr⁻¹ := by
    rw [← hG]
    calc G = ((fr⁻¹)ᴴ * frᴴ) * G * (fr * fr⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (fr⁻¹)ᴴ * (frᴴ * G * fr) * fr⁻¹ := by simp only [Matrix.mul_assoc]
  show (fr * E * fr⁻¹)ᴴ * G * (fr * E * fr⁻¹) = G
  calc (fr * E * fr⁻¹)ᴴ * G * (fr * E * fr⁻¹)
        = (fr⁻¹)ᴴ * Eᴴ * (frᴴ * G * fr) * E * fr⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (Eᴴ * J * E) * fr⁻¹ := by rw [hG]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hEJ, hGJ]

theorem isAtTau_atTau {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {M : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : M ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsAtTau θ V τ M (atTau θ V τ M) := by
  have hex : ∃ x, IsAtTau θ V τ M x := Formalism.IndefR.PublishedAut.atTauExists_of hθ V τ M hM
  unfold atTau
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem compAt_mul_gen (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B := by
  unfold compAt
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem tens_comp {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfu : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (E : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) (hh : IsAtTau θ V τ (fr * E * fr⁻¹) h)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (x : Mx D V.rank n) :
    tens θ τ fr f Ψ (HMul.hMul (mt V h) x : Mx D V.rank n) = f (E * (fr⁻¹ * compAt θ τ x)) * Ψ x := by
  have hc : ∀ ρ, compAt θ ρ (HMul.hMul (mt V h) x : Mx D V.rank n) = compAt θ ρ (mt V h) * compAt θ ρ x := fun ρ =>
    compAt_mul_gen θ ρ (mt V h) x
  have hτ : compAt θ τ (mt V h) = fr * E * fr⁻¹ := hh.2.1
  have hρ : ∀ ρ, ρ ≠ τ → compAt θ ρ (mt V h) = 1 := fun ρ hρ => hh.2.2 ρ hρ
  have hfin : (HMul.hMul (mt V h) x : Mx D V.rank n).map (finPart D) = x.map (finPart D) := by
    rw [Matrix.map_mul, Formalism.IndefR.Fock.Der.finPart_mt hh.1, Matrix.one_mul]
  have hΨx : Ψ (HMul.hMul (mt V h) x : Mx D V.rank n) = Ψ x := hΨ.1 _ _ (fun ρ hρ' => by rw [hc, hρ ρ hρ', Matrix.one_mul]) hfin
  unfold tens
  rw [hΨx, hc, hτ]
  congr 1
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hfu, Matrix.one_mul,
    Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.LieCPfH

namespace PositivityTheory.Rg.Sw.Glob

open LieCPfH


set_option maxHeartbeats 1000000 in
theorem lieComm_of (hAway : AwayIn) (hLNe : LNe) (hSch : SchFP) (hOp : OpCLM) (hAF : AwayFact) (hSD : SchDeriv) :
    LieComm := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨA X hX P g x
  have hl : ∀ τ', l τ' ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.2 (hl τ)
    positivity
  have hΨ : AwayCls θ τ fr Ψ := hAway D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨA
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hfu : IsUnit fr.det := hC.hfr.1
  obtain ⟨S, S', hS, hS', hder⟩ := hSD V.rank n (cLoc l τ) hc X P
  obtain ⟨SP, hSP⟩ := hSch V.rank n (cLoc l τ) hc P
  have memQ : ∀ T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ, tens θ τ fr T Ψ ∈ schwartzA θ V.rank n :=
    fun T => hΨ.2 T ⟨T, rfl⟩
  have hphi : ∀ (Q : PX V.rank n) (T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ), (⇑T = fP (cLoc l τ) Q) →
      phiS θ τ fr (cLoc l τ) Ψ Q = ⟨tens θ τ fr T Ψ, memQ T⟩ := by
    intro Q T hT
    have hm : tens θ τ fr (fP (cLoc l τ) Q) Ψ ∈ schwartzA θ V.rank n := hT ▸ memQ T
    unfold phiS
    rw [dite_eq_left hm]
    apply Subtype.ext
    show tens θ τ fr (fP (cLoc l τ) Q) Ψ = tens θ τ fr T Ψ
    rw [hT]
  obtain ⟨x0, y, hg, hx0⟩ := hAF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  obtain ⟨Ψ', hΨ', hact⟩ := hx0 Ψ hΨ
  obtain ⟨L, hL⟩ := hOp D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y
  have key : ∀ T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      (ω g ⟨tens θ τ fr T Ψ, memQ T⟩).1 = tens θ τ fr (L T) Ψ' := by
    intro T
    rw [hg, map_mul, Module.End.mul_apply]
    have h1 : ω (ι y) ⟨tens θ τ fr T Ψ, memQ T⟩ = ⟨tens θ τ fr (L T) Ψ, memQ (L T)⟩ := Subtype.ext (hL Ψ hΨ T)
    rw [h1]
    exact hact (L T) (memQ (L T))

  have hLHS : (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P))).1 x =
      (L S') (fr⁻¹ * compAt θ τ x) * Ψ' x := by
    rw [hphi _ S' (funext hS'), key]
    rfl

  have hgc : ∀ t : ℝ, (ω g (phiS θ τ fr (cLoc l τ) Ψ P)).1
      (HMul.hMul (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹))) x : Mx D V.rank n) =
        (L (S t)) (fr⁻¹ * compAt θ τ x) * Ψ' x := by
    intro t
    have hM := uh_frame hC.hfr hX t
    have hh := isAtTau_atTau hC.hθ V τ hM
    have hΦt : ∀ x', (⟨tens θ τ fr (S t) Ψ, memQ (S t)⟩ : schwartzA θ V.rank n).1 x' =
        (phiS θ τ fr (cLoc l τ) Ψ P).1 (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹)) ⬝ x') := by
      intro x'
      rw [hphi P SP hSP]
      show tens θ τ fr (S t) Ψ x' = tens θ τ fr SP Ψ (HMul.hMul (mt V _) x' : Mx D V.rank n)
      rw [tens_comp hfu hΨ _ _ hh, hSP]
      unfold tens
      exact congrArg (· * Ψ x') (hS t _)
    have e := GCommH.gComm hC.hψ hC.hχ hC.hη hC.hθ hμ hC.hω (phiS θ τ fr (cLoc l τ) Ψ P) ⟨tens θ τ fr (S t) Ψ, memQ (S t)⟩
      _ hΦt g x
    rw [← e, key]
    rfl

  let ev : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℝ (fr⁻¹ * compAt θ τ x)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ (Fin V.rank → Fin n → ℂ) ℂ)
  have hev : ∀ T, ev T = T (fr⁻¹ * compAt θ τ x) := fun T => rfl
  have hT : Filter.Tendsto (fun t : ℝ => (ev.comp L) (t⁻¹ • (S t - S 0))) (nhdsWithin 0 {0}ᶜ)
      (nhds ((ev.comp L) S')) := ((ev.comp L).continuous.tendsto S').comp hder
  have hd : HasDerivAt (fun t : ℝ => ev (L (S t))) (ev (L S')) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hT.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [slope_def_module, sub_zero, map_smul, map_sub, ContinuousLinearMap.comp_apply]
  have hd' : HasDerivAt (fun t : ℝ => (L (S t)) (fr⁻¹ * compAt θ τ x) * Ψ' x)
      ((L S') (fr⁻¹ * compAt θ τ x) * Ψ' x) 0 := by
    simpa only [hev] using hd.mul_const (Ψ' x)
  unfold DX
  rw [hLHS, ← hd'.deriv]
  congr 1
  funext t
  exact (hgc t).symm

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIkvac : LIkvac := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac k hk
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hC.hs τ).2.2.1

  have hann1 : ∀ X, annS V l s θ τ X (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 = 0 := by
    intro X
    rw [phiS_val (hmem 1).1]
    funext x
    rw [annS_tens hC.hθ hC.hfr hM l]
    simp
  have hann2 := annS_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs τ _ hann1 (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hann2

  have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 ∈ fockA θ V n l s := by
    rw [phiS_val (hmem 1).1]
    exact (hmem 1).2
  have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hst
  obtain ⟨Q, hQ⟩ := tens_slice hC.hθ hC.hfr l _ hst
  rw [hQ] at hann2
  have hQc := const_of_annS hC.hθ hC.hfr hM l Q hann2
  set a := evX Q 0 with ha
  have hL1 : L k (fP (cLoc l τ) 1) = a • fP (cLoc l τ) 1 := by
    rw [hQ, hQc]
    funext u
    simp [fP, evX]

  have hv := hvac k
  unfold sLd at hv
  rw [hL1] at hv
  have hg0 : gs (cLoc l τ) (0 : Fin V.rank → Fin n → ℂ) = 1 := by
    simp [gs]
  have hf0 : fP (cLoc l τ) (1 : PX V.rank n) 0 = 1 := by
    simp [fP, evX, hg0]
  simp only [Pi.smul_apply, smul_eq_mul, hf0, mul_one] at hv
  rw [hL1, hv]

end PositivityTheory.Rg.Sw.Glob
end
end

