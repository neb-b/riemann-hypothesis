module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.EmbP

open Formalism.IndefR.Eqv (glueA splitInv psiT psiT_glueA finPart_glueA mat_ext psiT_sigR finPart_sigR psiT_inclR
  finPart_inclR continuous_glueA continuous_splitInv thetaC eq_thetaC)

variable (D : D7) {N : ℕ}

open Classical

def atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then g i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j)
    ((1 : Matrix (Fin N) (Fin N) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_atMN (τ τ' : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) :
    (atMN D τ g).map (psiT D τ') = if τ' = τ then g else 1 := by
  classical
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, psiT_glueA]
  split_ifs <;> rfl

theorem fin_atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : (atMN D τ g).map (finPart D) = 1 := by
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, finPart_glueA]

theorem atMN_mul (τ : D.what₂.Tau) (g g' : Matrix (Fin N) (Fin N) ℂ) :
    atMN D τ (g * g') = atMN D τ g * atMN D τ g' := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, psi_atMN, psi_atMN, psi_atMN]
    split_ifs <;> simp
  · rw [Matrix.map_mul, fin_atMN, fin_atMN, fin_atMN, Matrix.one_mul]

theorem atMN_one (τ : D.what₂.Tau) : atMN D τ (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  apply mat_ext D
  · intro τ'
    rw [psi_atMN, Matrix.map_one _ (map_zero _) (map_one _)]
    split_ifs <;> rfl
  · rw [fin_atMN, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_map_psiT (τ : D.what₂.Tau) (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (psiT D τ) = (M.map (psiT D τ))ᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, psiT_sigR]

theorem cT_map_fin (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (finPart D) =
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (M.map (finPart D)) := by
  ext i j; simp [Formalism.UG.cT, finPart_sigR]

theorem JR_map_psiT (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (psiT D τ) = J.map (tauE D τ) := by
  ext i j; simp [JR, psiT_inclR]

theorem JR_map_fin (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (finPart D) = JR (Af D.host.F) J := by
  ext i j; simp [JR, finPart_inclR]

theorem atMN_unitary (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : gᴴ * J.map (tauE D τ) * g = J.map (tauE D τ)) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (atMN D τ g) * JR (AF D.host.F) J * atMN D τ g = JR (AF D.host.F) J := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_atMN]
    split_ifs with h
    · subst h; exact hg
    · simp
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_atMN, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem continuous_atMN (τ : D.what₂.Tau) : Continuous (atMN D (N := N) τ) := by
  classical
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact (continuous_apply j).comp (continuous_apply i)
  · simp only [h, if_false]; exact continuous_const

end PositivityTheory.Rg.Sw.Glob.EmbP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def ConvRight : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n →
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∀ g, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g

def ThLin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ Φ', PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ →
    PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ' → PositivityTheory.PfSWUS.InRange V n →
    ∀ g, thetaInt ω ν (Φ + Φ') g = thetaInt ω ν Φ g + thetaInt ω ν Φ' g

def GLamBd : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ L ∈ lamSet (n := n) ψ,
    (∀ (a : ℂ) (F F' : G D n → ℂ), Continuous F → Continuous F' → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ GF D n, ∀ g, F' (γ * g) = F' g) → L (a • F + F') = a * L F + L F') ∧
    ∃ C : Set (G D n), IsCompact C ∧ ∀ (F : G D n → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ x ∈ C, ‖F x‖ ≤ M) → ‖L F‖ ≤ M

def GLsing : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsCharAF D.host.F ψ →
    IsInfFam θ → IsPlaceEmb θ τ ι → ∀ F : G D n → ℂ, Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
    (∀ L ∈ lamSet (n := n) ψ, L F = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G D n) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ₀ x = 0

def LNZ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def MainSt : Prop :=
  AbsThm → SFrame → SEmb → SigOK → SplitFock → TensMem → LocOpEx → LocInst → LinSec → GSplit → GIauto → GIk → GIinv →
    GIdil → EisStrong → GLamBd → GLsing → PositivityTheory.PfSWUS.CoefND → ConvRight → ThLin → LNZ →
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (s0 V n) (thetaInt ω ν Φ g)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have hJ : JJ n * JJ n = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [JJ, Matrix.fromBlocks_multiply]
  have h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n)) := by
    rw [← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]
  have hJd : (JJ n).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
  rw [h0, mul_zero] at e
  exact e.symm

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsUnitaryDiag
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix Formalism.IndefR.Datum

namespace PositivityTheory.Rg.Sw.Glob

theorem exists_unitary_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsHermitian) :
    ∃ (W : Matrix (Fin k) (Fin k) ℂ) (lam : Fin k → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      Wᴴ * T * W = diagonal (fun i => (lam i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

theorem exists_normal {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.PosDef) : ∃ C : Matrix (Fin k) (Fin k) ℂ,
    Cᴴ * M * C = 1 := by
  have hpos := hM.eigenvalues_pos
  have hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) =
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this
  generalize (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd
  generalize hM.1.eigenvalues = μ at hpos hd
  refine ⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩
  have hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, hCd]
  calc diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ * M * (U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))
      = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hp := hpos i
        have hs : (Real.sqrt (μ i)) ^ 2 = μ i := Real.sq_sqrt hp.le
        have hs0 : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
        have hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
        field_simp
        rw [← Complex.ofReal_pow, hs]

theorem frame_of_cartan {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℂ) (h : IsCartanInv G S) :
    ∃ (ε : Fin k → Bool) (fr : Matrix (Fin k) (Fin k) ℂ), IsUnit fr.det ∧ frᴴ * G * fr = diagonal (sgn ε) ∧
      frᴴ * (G * S) * fr = 1 := by
  obtain ⟨hSS, hSG, hM⟩ := h
  have hMh : (G * S)ᴴ = G * S := hM.1
  have hGh : Gᴴ = G := by
    have h1 : Sᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
    have h2 : Sᴴ * Gᴴ = G * S := by rw [← conjTranspose_mul]; exact hMh
    calc Gᴴ = Sᴴ * Sᴴ * Gᴴ := by rw [h1, Matrix.one_mul]
      _ = Sᴴ * (Sᴴ * Gᴴ) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * (G * S) := by rw [h2]
      _ = Sᴴ * G * S := by rw [Matrix.mul_assoc]
      _ = G := hSG
  obtain ⟨C, hCMC⟩ := exists_normal hM
  have hCCM : C * (Cᴴ * (G * S)) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC
  have hTh : (Cᴴ * G * C).IsHermitian := by
    show (Cᴴ * G * C)ᴴ = Cᴴ * G * C
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1 := by
    have e1 : C * Cᴴ * G = S := by
      have : G = G * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc C * Cᴴ * G = C * (Cᴴ * (G * S)) * S := by
            conv_lhs => rw [this]
            simp only [Matrix.mul_assoc]
        _ = S := by rw [hCCM, Matrix.one_mul]
    calc (Cᴴ * G * C) * (Cᴴ * G * C) = Cᴴ * G * (C * Cᴴ * G) * C := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (G * S) * C := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = 1 := hCMC
  obtain ⟨W, lam, hWW, hWW', hTd⟩ := exists_unitary_diag hTh
  have hsq : ∀ i, lam i = 1 ∨ lam i = -1 := by
    have hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hTd]
      calc Wᴴ * (Cᴴ * G * C) * W * (Wᴴ * (Cᴴ * G * C) * W)
          = Wᴴ * (Cᴴ * G * C) * (W * Wᴴ) * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]
    intro i
    have := congrFun (congrFun hD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : (lam i) * (lam i) = 1 := by exact_mod_cast this
    have h3 : (lam i - 1) * (lam i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  refine ⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩
  · have hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1 := by
      rw [conjTranspose_mul]
      calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]
    exact isUnit_det_of_left_inverse hinv
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * G * (C * W) = Wᴴ * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := hTd
      _ = diagonal (sgn fun i => decide (lam i = 1)) := by
          congr 1; funext i
          simp only [sgn]
          rcases hsq i with h | h
          · simp [h]
          · simp [h] <;> norm_num
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]

theorem sFrame : SFrame := by
  intro D V τ s h
  exact frame_of_cartan _ _ h

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIk
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dite_eq_left hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def CompInj : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (x y : Mx D m n), (∀ τ, compAt θ τ x = compAt θ τ y) →
    x.map (finPart D) = y.map (finPart D) → x = y

def WEx : Prop := ∀ (D : D7) (n : ℕ), ∃ W : G D n, mat W = blk4 0 1 (-1) 0

def UnipTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n),
      (ω (ι y) Φ).1 x = Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace) * Φ.1 x

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def sLd {m : ℕ} (L : GR n → ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (c : ℝ) (P : PX m n) (y : GR n) : ℂ :=
  L y (fP c P) 0

def pqOf {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℕ × ℕ :=
  if 0 < l τ then (cnt ε true, cnt ε false) else (cnt ε false, cnt ε true)

def LIl : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → l τ ≠ 0

def LIlin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    (∀ (y : GR n) (a : ℂ) (P Q : PX V.rank n), L y (fP (cLoc l τ) (a • P + Q)) = a • L y (fP (cLoc l τ) P) + L y (fP (cLoc l τ) Q)) ∧
    ∀ P : PX V.rank n, L 1 (fP (cLoc l τ) P) = fP (cLoc l τ) P

def LIlaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ e : ℤ, ∀ (P : PX V.rank n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLd L (cLoc l τ) P (y * g) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y * sLd L (cLoc l τ) P g

def LIcell : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = C * secN ε (cLoc l τ) (tLoc l τ) P b

def LIcont : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ P : PX V.rank n, Continuous (sLd L (cLoc l τ) P)

def LIrho : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) ∧
      ∀ P, ∃ W : Submodule ℂ (PX V.rank n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
        ∀ Q ∈ W, ∀ l' : PX V.rank n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l' (ρ k Q)) {k | InK (mR k)}

def LIkact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
      ∀ P (g k : GR n), InK (mR k) → sLd L (cLoc l τ) P (g * k) = sLd L (cLoc l τ) (ρ k P) g

def LIvac : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ), 0 < c →
    ((t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)) →
    ∀ (S : GR n → ℂ) (C : ℂ), Continuous S → S 1 = 1 →
      (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 p q e y * S g) →
      (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b → S g = C * secN ε c t (1 : PX m n) b) →
      ∀ g, S g = F0 p q e g

def LIkvac : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ e : ℤ, (∀ g : GR n, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g) →
    ∀ k : GR n, InK (mR k) → L k (fP (cLoc l τ) 1) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k • fP (cLoc l τ) 1

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast
section
noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def SigAtLeast (D : D7) (V : HSp D) (k : ℕ) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit fr.det ∧ frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε) ∧ k ≤ cnt ε true ∧ k ≤ cnt ε false

def WittLBlt : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k < V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

def WittLBeq : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k = V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def GIwasawa : Prop := ∀ (D : D7) (n : ℕ) (g : G D n), ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k

end PositivityTheory.Rg.Sw.Glob
end
end

