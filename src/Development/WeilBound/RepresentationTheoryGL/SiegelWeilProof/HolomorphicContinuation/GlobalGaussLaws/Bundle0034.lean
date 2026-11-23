module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0033
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AdelicConjTransposeBlockMatrixTwoByTwoFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LeviH

variable {D : D7}

def bA {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

def bD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    M = blk4 (bA M) (bB M) (bC M) (bD M) := by
  unfold blk4 bA bB bC bD
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem upper_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bA (blk4 a b c d) = a := by
  unfold bA blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem upper_right_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bB (blk4 a b c d) = b := by
  unfold bB blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bA_reidx {n : ℕ} (y : M2 n) : bA (reidx y) = y.toBlocks₁₁ := by
  unfold bA reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_reidx {n : ℕ} (y : M2 n) : bB (reidx y) = y.toBlocks₁₂ := by
  unfold bB reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_reidx {n : ℕ} (y : M2 n) : bC (reidx y) = y.toBlocks₂₁ := by
  unfold bC reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_one {R : Type} [CommRing R] {n : ℕ} : bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_right_of_block_matrix]

theorem bA_one {R : Type} [CommRing R] {n : ℕ} : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_left_of_block_matrix]

theorem lower_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bC (blk4 a b c d) = c := by
  unfold bC blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_one {R : Type} [CommRing R] {n : ℕ} : bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, lower_left_of_block_matrix]

theorem bA_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bA M).map f = bA (M.map f) := rfl

theorem bB_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bB M).map f = bB (M.map f) := rfl

theorem bC_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bC M).map f = bC (M.map f) := rfl

theorem compAt_bA (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bA M) = bA (compAt θ τ M) := rfl

theorem compAt_bB (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bB M) = bB (compAt θ τ M) := rfl

theorem compAt_bC (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bC M) = bC (compAt θ τ M) := rfl

theorem adj_mul {m n k : ℕ} (x : Mx D m n) (z : Mx D n k) :
    adj (HMul.hMul x z : Mx D m k) = HMul.hMul (adj z) (adj x) := by
  unfold adj
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {n : ℕ} (a d : Mx D n n) : adj (blk4 a 0 0 d) = blk4 (adj a) 0 0 (adj d) := by
  unfold adj
  rw [GlobalTheory.StdUnn.Frame.block_matrix_map, GlobalTheory.StdUnn.Frame.blockMatrixTwoByTwoFin_transpose, Matrix.map_zero _ (map_zero (cA D)),
    Matrix.transpose_zero]

theorem unitary_mat {n : ℕ} (g : G D n) :
    adj (mat g) * (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * rat (Jst D n) * mat g = rat (Jst D n) := g.2
  rwa [GlobalTheory.StdUnn.Frame.rat_Jst] at h

end PositivityTheory.Rg.Sw.Glob.LeviH

namespace PositivityTheory.Rg.Sw.Glob

open LeviH in
set_option maxHeartbeats 800000 in
theorem leviTau : LeviTau := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  have hθ := hC.hθ
  obtain ⟨hτ, hτ', hfin⟩ := hC.hι.2 y
  have h1 : mat (ι y) * mat (ι y)⁻¹ = 1 := by
    show mat (ι y * (ι y)⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have h2 : mat (ι y)⁻¹ * mat (ι y) = 1 := by
    show mat ((ι y)⁻¹ * ι y) = 1
    rw [inv_mul_cancel]
    rfl
  have hU := unitary_mat (ι y)
  have hlevi := hC.hω.levi (ι y)
  generalize mat (ι y) = M at hτ hτ' hfin h1 h2 hU hlevi
  generalize mat (ι y)⁻¹ = M' at h1 h2
  have hB : bB M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bB_map, hfin, bB_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bB]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bB_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₁₂]
      · rw [hτ' τ' h, bB_one]
  have hC0 : bC M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bC_map, hfin, bC_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bC]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bC_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₂₁]
      · rw [hτ' τ' h, bC_one]
  have hM : M = blk4 (bA M) 0 0 (bD M) := by
    conv_lhs => rw [block_matrix_of_blocks M]
    rw [hB, hC0]
  have hAA' : bA M * bA M' = 1 := by
    have e := congrArg bA h1
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, zero_mul, add_zero] at e
    exact e
  have hA'A : bA M' * bA M = 1 := by
    have e := congrArg bA h2
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, mul_zero, add_zero] at e
    exact e
  have hAD : adj (bA M) * bD M = 1 := by
    rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul] at hU
    have e := congrArg bB hU
    rw [upper_right_of_block_matrix, upper_right_of_block_matrix] at e
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at e
    exact e
  have hD : bD M = adj (bA M') := by
    have e : adj (bA M') * adj (bA M) = 1 := by rw [← LeviH.adj_mul, hAA', LeviH.adj_one]
    calc bD M = 1 * bD M := (one_mul _).symm
      _ = adj (bA M') * (adj (bA M) * bD M) := by rw [← mul_assoc, e]
      _ = adj (bA M') := by rw [hAD, mul_one]
  have hmat : M = blk4 (bA M) 0 0 (adj (bA M')) := by
    calc M = blk4 (bA M) 0 0 (bD M) := hM
      _ = blk4 (bA M) 0 0 (adj (bA M')) := by rw [hD]
  refine ⟨_, bA M, ?_, ?_, ?_, fun Φ x => hlevi ⟨bA M, bA M', hAA', hA'A⟩ hmat Φ x⟩
  · rw [compAt_bA, hτ, bA_reidx, hya]
    simp only [mM, Matrix.toBlocks_fromBlocks₁₁]
  · intro τ' h
    rw [compAt_bA, hτ' τ' h, bA_one]
  · rw [bA_map, hfin, bA_one]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOne
section
namespace PositivityTheory.Rg.Sw.Glob

theorem derivOne (h : GlobalTheory.Published.WeilThetaConvergence) : DerivOne := derivOne_of h curveSt

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenOps
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenOpsH

theorem gen_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) :
    ∃ κ γ : ℂ, κ ≠ 0 ∧ ((∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0) → γ ≠ 0) ∧
      (∀ f : (Fin V.rank → Fin n → ℂ) → ℂ, IsSch f → IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u)) ∧
      ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => γ⁻¹ * (κ * ftLoc ε (tLoc l τ)
          (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) u)) Ψ := by
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨w, hw⟩ := hW D n
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) (by rw [Matrix.conjTranspose_neg, hc])
  have hιn : ι yn = w⁻¹ * ι y * w := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [hιn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
  have h0 := hFT 0 (OG.awayCls_zero τ fr)
  let e : (Fin V.rank → Fin n → ℂ) → ℂ := fun u =>
    Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace)
  let F' : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u =>
    κ⁻¹ * ftLoc ε (-tLoc l τ) f u
  let Fw : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u => κ * ftLoc ε (tLoc l τ) f u
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  have hE : ∀ f, IsSch f → IsSch (fun u => e u * F' f u) := fun f hf =>
    (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) (F' f) hc' ((h0.2.2 f hf).2.1)
  set γ : ℂ := Fw (F' f0) (0 : Matrix (Fin V.rank) (Fin n) ℂ) with hγdef

  have hrelAll : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), ∀ x, Ψ x = γ * A (A' Ψ) x := by
    intro Ψ hΨ
    obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
    have kA := hFT (A' Ψ) hA'Ψ
    have hcons : ∀ g (hg : IsSch g), tens θ τ fr g Ψ = tens θ τ fr (Fw (F' g)) (A (A' Ψ)) := by
      intro g hg
      have k1g := (hFΨ g hg).2.2.2
      have kcg := (kA.2.2 (F' g) ((hFΨ g hg).2.1)).2.2.1
      have hΦ1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ = ⟨tens θ τ fr (F' g) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
        Subtype.ext k1g
      have hid : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hΦ1] at hid
      rw [← kcg, hid]
    intro x
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := OG.exists_slice hC.hθ τ x (fr * (0 : Matrix (Fin V.rank) (Fin n) ℂ))
    have h1 := congrFun (hcons f0 hf0) x'
    have hf00' : f0 (0 : Matrix (Fin V.rank) (Fin n) ℂ) = 1 := hf00
    rw [OG.tens_at τ hfr _ _ x' 0 hx'1, OG.tens_at τ hfr _ _ x' 0 hx'1, hf00', one_mul, hΨ.1 x' x hx'2 hx'3,
      kA.1.1 x' x hx'2 hx'3] at h1
    exact h1
  refine ⟨κ, γ, hκ, ?_, fun f hf => ⟨(h0.2.2 f hf).2.1, (h0.2.2 f hf).1⟩, ?_⟩
  · rintro ⟨Ψ, x₀, hΨ, hx₀⟩ hγ
    exact hx₀ (by rw [hrelAll Ψ hΨ x₀, hγ, zero_mul])
  intro Ψ hΨ f hf
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have k1 := (hFΨ f hf).2.2.2
  have kA := hFT (A' Ψ) hA'Ψ
  have kr := (kA.2.2 (fun u => e u * F' f u) (hE f hf)).2.2.1
  have hrel := hrelAll Ψ hΨ
  by_cases hγ : γ = 0
  · have hΨ0 : Ψ = 0 := funext fun x => by rw [hrel x, hγ, zero_mul]; rfl
    subst hΨ0
    have hz : (⟨tens θ τ fr f 0, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := Subtype.ext (by funext x; simp [tens])
    rw [hz, map_zero]
    funext x
    simp [tens]
  · have hstep : ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
        ω w ⟨tens θ τ fr (fun u => e u * F' f u) (A' Ψ), hA'Ψ.2 _ (hE f hf)⟩ := by
      rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      congr 1
      apply Subtype.ext
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn, k1]
      simp only [tens, e, F', mul_assoc]
    funext x
    rw [hstep, kr]
    simp only [tens]
    rw [hrel x]
    simp only [e, F']
    field_simp

end PositivityTheory.Rg.Sw.Glob.GenOpsH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenUnit
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.GenUnitH

variable {D : D7}

theorem compAt_eq (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v z = GlobalTheory.AdelicU.compFin D.host.F D.host.E v z :=
  GlobalTheory.EmbChart.map_evalV_map_sndA v z

theorem compFin_tensAt_ne {v w : GlobalTheory.FinPl.Pl D} (h : w ≠ v) (y : Ev D v) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E w (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne h a,
      TensorProduct.zero_tmul]

theorem infPart_tensAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) : infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) = 0 from rfl, TensorProduct.zero_tmul]

theorem tensAt_mem_idAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  unfold GlobalTheory.FinPl.idAt
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_tensAt v y), ?_⟩
  refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
  rw [compAt_eq]
  exact compFin_tensAt_ne w.2 y

theorem tensAt_mem_intAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) (hy : y ∈ intLoc D.host.F D.host.E v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨tensAt_mem_idAt v y, (GlobalTheory.EmbChart.finPart_tensAt_mem_iff y).2 hy⟩

theorem glueEntry (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v) (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ s : AE D, infPart D s = 0 ∧ ∀ v, GlobalTheory.FinPl.compAt D v s = z v := by
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.FinPlLoc.glue D (fun v => GlobalTheory.EmbChart.tensAt D.host.E v (z v))
    (fun v => tensAt_mem_idAt v (z v)) ⟨∅, fun v _ => tensAt_mem_intAt v (z v) (hz v)⟩
  refine ⟨s, hs0, fun v => ?_⟩
  have h := hs v
  unfold GlobalTheory.FinPl.idOff at h
  have h2 : GlobalTheory.FinPl.compAt D v (s - GlobalTheory.EmbChart.tensAt D.host.E v (z v)) = 0 :=
    RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨v, rfl⟩)
  rw [map_sub, sub_eq_zero, compAt_eq v (GlobalTheory.EmbChart.tensAt _ v _), GlobalTheory.EmbChart.compFin_tensAt] at h2
  exact h2

theorem finExt {x y : Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y) : x = y := by
  have key : ∀ (x : Af D.host.F ⊗[D.host.F] D.host.E) (v : GlobalTheory.FinPl.Pl D) (k : Fin 2),
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x) k =
        evalV D.host.F v ((Formalism.IndefR.Eqv.basAf D).repr x k) := by
    intro x v k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]
    | tmul a e =>
      show (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr
        (evalV D.host.F v a ⊗ₜ[D.host.F] e) k = _
      rw [Formalism.IndefR.Eqv.basAf, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  apply (Formalism.IndefR.Eqv.basAf D).ext_elem
  intro k
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [← key, ← key, h]

end PositivityTheory.Rg.Sw.Glob.GenUnitH

namespace PositivityTheory.Rg.Sw.Glob

theorem unitAE : UnitAE := by
  intro D d hτ hv
  choose z' hz'mem hz'inv using fun v => (hv v).2
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z' hz'mem
  let x := Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D fun τ => (Formalism.IndefR.Eqv.psiT D τ d)⁻¹) (finPart D s)
  have hx : ∀ v, GlobalTheory.FinPl.compAt D v x = z' v := fun v => by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = _
    rw [Formalism.IndefR.Eqv.finPart_glueA]
    exact hs v
  have hdx : d * x = 1 := by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [map_mul, Formalism.IndefR.Eqv.psiT_glueA, mul_inv_cancel₀ (hτ τ), map_one]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (d * x) = GlobalTheory.FinPl.compAt D v 1
      rw [map_mul, map_one, hx v, hz'inv v]
  exact ⟨⟨d, x, hdx, by rw [mul_comm]; exact hdx⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def PlanchLoc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t : ℝ), t ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f →
    ∫ u, ‖ftLoc ε t f u‖ ^ 2 = c * ∫ u, ‖f u‖ ^ 2

def AwayNZ : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0

end PositivityTheory.Rg.Sw.Glob
end
end

