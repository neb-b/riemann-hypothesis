module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP.Cartan

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

section Complex

variable {n : ℕ} {G s b c : Matrix (Fin n) (Fin n) ℂ}

theorem herm_of_isCartanInv (hs : IsCartanInv G s) : Gᴴ = G := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h4 : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul]; exact h3.1
  have h5 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← mul_assoc, h5, one_mul]
    _ = G := by rw [h4, ← mul_assoc, h2]

theorem frame_gram_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : bᴴ * G * b = c * s * b := by
  calc bᴴ * G * b = bᴴ * (G * (s * (b * c) * s)) * b := by rw [hbc, mul_one, hs, mul_one]
    _ = (bᴴ * (G * s) * b) * (c * s * b) := by simp only [mul_assoc]
    _ = _ := by rw [h, one_mul]

theorem frame_gram_sq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) :
    (bᴴ * G * b) * (bᴴ * G * b) = 1 := by
  rw [frame_gram_eq hbc hs h]
  calc c * s * b * (c * s * b) = c * (s * (b * c) * s) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hbc, mul_one, hs, mul_one, mul_eq_one_comm.1 hbc]

theorem frame_inv_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : b * bᴴ * G = s := by
  rw [mul_conjTranspose_mul_eq hbc (frame_gram_eq hbc hs h)]
  calc b * (c * s * b) * c = (b * c) * s * (b * c) := by simp only [mul_assoc]
    _ = s := by rw [hbc, one_mul, mul_one]

theorem blkMat_conjTranspose (x y : Matrix (Fin n) (Fin n) ℂ) :
    (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := by
  simp [blkMat, Matrix.fromBlocks_conjTranspose]

end Complex

variable {D : D7} {θ : InfFam D}

theorem compAt_blkGL (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    compAt θ τ (blkGL finSumFinEquiv (a, a)).1 = blkMat finSumFinEquiv (compAt θ τ a.1) (compAt θ τ a.1) :=
  blkMat_map finSumFinEquiv ((θ τ).comp (infPart D)) (map_zero _) _ _

theorem commute_of_mem_Kmax (hθ : IsInfFam θ) {V : HSp D} {a : GL (Fin V.rank) (AE D)} (τ : D.what₂.Tau)
    (hd : ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) = 1)
    {g : GA D V} (hg : g ∈ Kmax V a) :
    Commute (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  refine (unitary_iff_commute (compAt_mul_inv τ a) rfl hd (infMat_isometry hθ τ g)).1 ?_
  rw [compAt_eq_map hθ, compAt_eq_map hθ, eq_infProj hθ (embOverOf D τ) rfl]
  exact (mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) V.gram a g).1
    (((mem_levelAll (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (a := a) (g := g)).1 hg).2 _)

theorem cartan_dbl : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D θ A sA a hθ hs ha
  have hbc := fun τ => compAt_mul_inv (θ := θ) τ a
  have e : ∀ τ, frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ = blkMat finSumFinEquiv (sA τ) (-sA τ) := fun τ => by
    rw [frameInv_dblSp, show frameInv θ A a τ = sA τ from frame_inv_eq (hbc τ) (hs τ).1 (ha τ)]
  have hd : ∀ τ, (compAt θ τ (blkGL finSumFinEquiv (a, a)).1)ᴴ * blkMat finSumFinEquiv (gramAt D A τ) (-gramAt D A τ) *
      compAt θ τ (blkGL finSumFinEquiv (a, a)).1 =
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) := fun τ => by
    rw [compAt_blkGL, blkMat_conjTranspose, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  have hd2 : ∀ τ, blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) *
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) = 1 := fun τ => by
    rw [blkMat_mul, neg_mul_neg, frame_gram_sq (hbc τ) (hs τ).1 (ha τ), blkMat_one]
  refine ⟨fun τ => ?_, fun k hk τ => ?_⟩
  · have h := isCartanInv_of_frame (compAt_mul_inv (θ := θ) τ (blkGL finSumFinEquiv (a, a))) (hd τ) (hd2 τ) (by
      rw [blkMat_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, herm_of_isCartanInv (hs τ), ← mul_assoc])
    rw [← gramAt_dblSp] at h
    have h' : IsCartanInv (gramAt D (dblSp A) τ) (frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ) := h
    rw [e] at h'
    exact h'
  · rw [Khat_eq] at hk
    have h := commute_of_mem_Kmax hθ (V := dblSp A) (a := blkGL finSumFinEquiv (a, a)) τ (by
      rw [gramAt_dblSp]
      exact (congrArg₂ (· * ·) (hd τ) (hd τ)).trans (hd2 τ)) hk
    rw [e] at h
    exact h

end GlobalTheory.Core.Rk.IP.Cartan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped ComplexOrder TensorProduct

namespace GlobalTheory.Core.Rk.HgtArch

open Matrix

section Block

variable {A : Type} [CommRing A] (ρ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]

theorem cT_fromBlocks (P Q R S : Matrix m m A) :
    Formalism.UG.cT ρ (fromBlocks P Q R S) = fromBlocks (Formalism.UG.cT ρ P) (Formalism.UG.cT ρ R) (Formalism.UG.cT ρ Q) (Formalism.UG.cT ρ S) := by
  simp [Formalism.UG.cT, fromBlocks_map, fromBlocks_transpose]

theorem cT_zero : Formalism.UG.cT ρ (0 : Matrix m m A) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem diag_identity (Z b binv : Matrix m m A) (P : Matrix (m ⊕ m) (m ⊕ m) A) (hbb : b * binv = 1)
    (hKD : P.toBlocks₂₁ + P.toBlocks₂₂ = P.toBlocks₁₁ + P.toBlocks₁₂)
    (hU : Formalism.UG.cT ρ (fromBlocks binv 0 0 binv * (fromBlocks Z 0 0 1 * P) * fromBlocks b 0 0 b) *
      (fromBlocks binv 0 0 binv * (fromBlocks Z 0 0 1 * P) * fromBlocks b 0 0 b) = 1) :
    Formalism.UG.cT ρ (Z * (P.toBlocks₁₁ + P.toBlocks₁₂)) * (Formalism.UG.cT ρ binv * binv) * (Z * (P.toBlocks₁₁ + P.toBlocks₁₂)) +
      Formalism.UG.cT ρ (P.toBlocks₁₁ + P.toBlocks₁₂) * (Formalism.UG.cT ρ binv * binv) * (P.toBlocks₁₁ + P.toBlocks₁₂) =
      Formalism.UG.cT ρ binv * binv + Formalism.UG.cT ρ binv * binv := by
  set V := fromBlocks Z 0 0 1 * P with hV
  set Bb : Matrix (m ⊕ m) (m ⊕ m) A := fromBlocks b 0 0 b
  set Bi : Matrix (m ⊕ m) (m ⊕ m) A := fromBlocks binv 0 0 binv
  set α := P.toBlocks₁₁ + P.toBlocks₁₂
  set M := Formalism.UG.cT ρ binv * binv
  have hBB : Bb * Bi = 1 := by simp [Bb, Bi, fromBlocks_multiply, hbb]
  have hBB' : Formalism.UG.cT ρ Bi * Formalism.UG.cT ρ Bb = 1 := by rw [← Formalism.UG.cT_mul, hBB, Formalism.UG.cT_one]
  have hN : Formalism.UG.cT ρ V * (Formalism.UG.cT ρ Bi * Bi) * V = Formalism.UG.cT ρ Bi * Bi := by
    calc Formalism.UG.cT ρ V * (Formalism.UG.cT ρ Bi * Bi) * V
        = (Formalism.UG.cT ρ Bi * Formalism.UG.cT ρ Bb) * (Formalism.UG.cT ρ V * (Formalism.UG.cT ρ Bi * Bi) * V) * (Bb * Bi) := by
          rw [hBB, hBB', Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT ρ Bi * (Formalism.UG.cT ρ (Bi * V * Bb) * (Bi * V * Bb)) * Bi := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT ρ Bi * Bi := by rw [hU, Matrix.mul_one]
  have hP : P * fromBlocks 1 0 1 0 = fromBlocks α 0 α 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks P]
    rw [fromBlocks_multiply]
    simp [α, hKD]
  have hVD : V * fromBlocks 1 0 1 0 = fromBlocks (Z * α) 0 α 0 := by
    rw [hV, Matrix.mul_assoc, hP, fromBlocks_multiply]; simp
  have hNb : Formalism.UG.cT ρ Bi * Bi = fromBlocks M 0 0 M := by
    simp [Bi, M, cT_fromBlocks, cT_zero, fromBlocks_multiply]
  have key := congrArg (fun X => Formalism.UG.cT ρ (fromBlocks (1 : Matrix m m A) 0 1 0) * X * fromBlocks 1 0 1 0) hN
  have e1 : Formalism.UG.cT ρ (fromBlocks (1 : Matrix m m A) 0 1 0) * (Formalism.UG.cT ρ V * (Formalism.UG.cT ρ Bi * Bi) * V) *
      fromBlocks 1 0 1 0 = Formalism.UG.cT ρ (V * fromBlocks 1 0 1 0) * (Formalism.UG.cT ρ Bi * Bi) * (V * fromBlocks 1 0 1 0) := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  rw [e1, hVD, hNb] at key
  simp only [cT_fromBlocks, cT_zero, Formalism.UG.cT_one, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one] at key
  exact (fromBlocks_inj.1 key).1

theorem map_identity (φ : A →+* ℂ) (hφ : ∀ x, φ (ρ x) = star (φ x)) (Z α binv : Matrix m m A)
    (h : Formalism.UG.cT ρ (Z * α) * (Formalism.UG.cT ρ binv * binv) * (Z * α) + Formalism.UG.cT ρ α * (Formalism.UG.cT ρ binv * binv) * α =
      Formalism.UG.cT ρ binv * binv + Formalism.UG.cT ρ binv * binv) :
    (Z.map φ * α.map φ)ᴴ * ((binv.map φ)ᴴ * binv.map φ) * (Z.map φ * α.map φ) +
      (α.map φ)ᴴ * ((binv.map φ)ᴴ * binv.map φ) * α.map φ =
      (binv.map φ)ᴴ * binv.map φ + (binv.map φ)ᴴ * binv.map φ := by
  have hcT : ∀ X : Matrix m m A, (Formalism.UG.cT ρ X).map φ = (X.map φ)ᴴ := by
    intro X; ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hφ]
  have := congrArg φ.mapMatrix h
  simpa only [map_add (f := _), map_mul, RingHom.mapMatrix_apply, hcT, Matrix.map_mul] using this

end Block

section Complex

variable {n : ℕ}

theorem det_one_add_ge (W : Matrix (Fin n) (Fin n) ℂ) (hW : ‖W.det‖ = 1) :
    ∃ r : ℝ, 2 ^ n ≤ r ∧ (1 + Wᴴ * W).det = r := by
  have hH : (Wᴴ * W).PosSemidef := posSemidef_conjTranspose_mul_self W
  have hh : (Wᴴ * W).IsHermitian := hH.isHermitian
  set U : Matrix (Fin n) (Fin n) ℂ := (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU1 : star U * U = 1 := hh.eigenvectorUnitary.2.1
  have hU2 : U * star U = 1 := hh.eigenvectorUnitary.2.2
  have hspec := hh.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  have hnn : ∀ i, 0 ≤ hh.eigenvalues i := hH.eigenvalues_nonneg
  have hprod : (∏ i, hh.eigenvalues i) = 1 := by
    have hd := hh.det_eq_prod_eigenvalues
    rw [det_mul, det_conjTranspose] at hd
    have h1 := Complex.normSq_eq_conj_mul_self (z := W.det)
    rw [Complex.normSq_eq_norm_sq, hW] at h1
    have h3 : star W.det * W.det = 1 := by simpa using h1.symm
    rw [h3] at hd
    have h4 : ((∏ i, hh.eigenvalues i : ℝ) : ℂ) = 1 := by
      first
        | exact_mod_cast hd.symm
        | (rw [Complex.ofReal_prod]; exact hd.symm)
        | simpa using hd.symm
    exact_mod_cast h4
  refine ⟨∏ i, (1 + hh.eigenvalues i), ?_, ?_⟩
  · have hs : (∏ i, Real.sqrt (hh.eigenvalues i)) = 1 := by
      have h0 : 0 ≤ ∏ i, Real.sqrt (hh.eigenvalues i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
      have h2 : (∏ i, Real.sqrt (hh.eigenvalues i)) ^ 2 = 1 := by
        rw [← Finset.prod_pow]
        simp only [Real.sq_sqrt (hnn _)]
        exact hprod
      exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).1 h2
    calc (2 : ℝ) ^ n = ∏ i, (2 * Real.sqrt (hh.eigenvalues i)) := by
          rw [Finset.prod_mul_distrib, hs, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, (1 + hh.eigenvalues i) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          have := Real.sq_sqrt (hnn i)
          nlinarith [sq_nonneg (Real.sqrt (hh.eigenvalues i) - 1)]
  · have e : 1 + Wᴴ * W = U * (1 + diagonal (RCLike.ofReal ∘ hh.eigenvalues)) * star U := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2]
    rw [e, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hU1, det_one, one_mul, ← diagonal_one,
      diagonal_add, det_diagonal]
    push_cast
    simp

theorem norm_det_le_one (a Z c : Matrix (Fin n) (Fin n) ℂ) (hc : c.det ≠ 0) (hZ : ‖Z.det‖ = 1)
    (h : (Z * a)ᴴ * (cᴴ * c) * (Z * a) + aᴴ * (cᴴ * c) * a = cᴴ * c + cᴴ * c) : ‖a.det‖ ≤ 1 := by
  have hcu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  set W := c * Z * c⁻¹ with hWdef
  have hWdet : W.det = Z.det := by
    rw [hWdef, det_mul, det_mul, det_nonsing_inv, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hcu, one_mul]
  obtain ⟨r, hr, hdet⟩ := det_one_add_ge W (by rw [hWdet, hZ])
  have hWc : W * c = c * Z := by
    rw [hWdef, Matrix.mul_assoc, nonsing_inv_mul _ hcu, Matrix.mul_one]
  have e : aᴴ * cᴴ * (1 + Wᴴ * W) * c * a = cᴴ * c + cᴴ * c := by
    rw [← h]
    calc aᴴ * cᴴ * (1 + Wᴴ * W) * c * a = aᴴ * (cᴴ * c) * a + (W * c * a)ᴴ * (W * c * a) := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = (Z * a)ᴴ * (cᴴ * c) * (Z * a) + aᴴ * (cᴴ * c) * a := by
          rw [hWc, add_comm]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hd := congrArg det e
  rw [← two_smul ℂ (cᴴ * c), det_smul, det_mul, det_mul, det_mul, det_mul, det_mul, det_conjTranspose,
    det_conjTranspose, hdet] at hd
  simp only [Fintype.card_fin] at hd
  have hn := congrArg norm hd
  simp only [norm_mul, norm_star, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_ofNat] at hn
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
  rw [abs_of_pos hr0] at hn
  have hq : 0 < ‖c.det‖ := norm_pos_iff.2 hc
  have h1 : ‖a.det‖ ^ 2 * r = 2 ^ n := by
    have : ‖a.det‖ ^ 2 * r * (‖c.det‖ * ‖c.det‖) = 2 ^ n * (‖c.det‖ * ‖c.det‖) := by rw [← hn]; ring
    exact mul_right_cancel₀ (by positivity) this
  have h2 : ‖a.det‖ ^ 2 ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

end Complex

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem submatrix_mul_self_equiv {ι κ : Type} [Fintype ι] [Fintype κ] {A : Type} [CommRing A] (e : κ ≃ ι)
    (X Y : Matrix ι ι A) : (X * Y).submatrix e e = X.submatrix e e * Y.submatrix e e :=
  (submatrix_mul_equiv X Y e e e).symm

theorem cT_submatrix {ι κ : Type} {A : Type} [CommRing A] (ρ : A →+* A) (e : κ ≃ ι) (X : Matrix ι ι A) :
    (Formalism.UG.cT ρ X).submatrix e e = Formalism.UG.cT ρ (X.submatrix e e) := rfl

theorem absEw_aH_le_one (hc : IsCMExt F E σ) (hJ : J.det ≠ 0) (h : Q = dblGram finSumFinEquiv J)
    {w : InfinitePlace F} (b : GL (Fin n) (w.Completion ⊗[F] E)) (y : GArch σ J w)
    (p : siegelH w.Completion σ Q) (k : GArch σ Q w) (hk : k ∈ KArch σ Q w b)
    (e : ioH _ σ h (y, 1) = p * k) : absEw F E w (aH _ σ Q p) ≤ 1 := by
  classical
  obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
  have e' : k⁻¹ = ioH _ σ h (y⁻¹, 1) * p := by
    have : k = (p : GArch σ Q w)⁻¹ * ioH _ σ h (y, 1) := by rw [e, inv_mul_cancel_left]
    rw [this, _root_.mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have hk' : k⁻¹ ∈ KArch σ Q w b := inv_mem hk
  rw [KArch, mem_stabArch] at hk'
  set ρ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ
  set P := (AdelicU.matHom w.Completion σ Q p).1
  set Z := (AdelicU.matHom w.Completion σ J y⁻¹).1
  set e2 := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
  have hU : Formalism.UG.cT ρ (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) *
      (blkMat e2 (b⁻¹).1 (b⁻¹).1 * (blkMat e2 Z 1 * P) * blkMat e2 b.1 b.1) = 1 := by
    have h1 : Formalism.UG.cT ρ ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 * 1 *
        ((blkGL e2 (b, b))⁻¹ * AdelicU.matHom w.Completion σ Q k⁻¹ * blkGL e2 (b, b)).1 = 1 := hk'
    rw [Matrix.mul_one, e', map_mul, matHom_ioH, ← map_inv, Prod.inv_mk] at h1
    simpa only [Units.val_mul, val_blkGL, map_one, Units.val_one, Subgroup.coe_mul] using h1
  have hU2 := congrArg (fun X => X.submatrix e2 e2) hU
  simp only [submatrix_mul_self_equiv, cT_submatrix, submatrix_blkMat, submatrix_one_equiv] at hU2
  have hKD : KeepsDiag e2 P := mem_siegelOf.1 p.2
  have key := diag_identity ρ Z b.1 (b⁻¹).1 (P.submatrix e2 e2) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    hKD (by simpa [submatrix_mul_self_equiv, Matrix.mul_assoc] using hU2)
  obtain ⟨φ, hφ⟩ : ∃ φ' : w.Completion ⊗[F] E →+* ℂ, φ' = infEmb τ := ⟨_, rfl⟩
  have hmd : ∀ X : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E), (X.map φ).det = φ X.det :=
    fun X => (RingHom.map_det φ X).symm
  have key2 := map_identity ρ φ (fun x => by rw [hφ]; exact (infEmb_sigR hc τ x).symm) _ _ _ key
  set α := (P.submatrix e2 e2).toBlocks₁₁ + (P.submatrix e2 e2).toBlocks₁₂ with hα
  have hZ : ‖(Z.map φ).det‖ = 1 := by
    have h1 := abs_detH (ν := absEw F E w) (absEw_conjUnit σ w) hJ y⁻¹
    rw [absEw_eq_sq hc τ, val_detH, ← hφ] at h1
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
    simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one] at h2
    rw [hmd]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hcdet : ((b⁻¹).1.map φ).det ≠ 0 := by
    rw [hmd]
    exact (((Matrix.isUnit_iff_isUnit_det _).1 (b⁻¹).isUnit).map φ).ne_zero
  have hdet : ‖(α.map φ).det‖ ≤ 1 := norm_det_le_one (α.map φ) (Z.map φ) ((b⁻¹).1.map φ) hcdet hZ key2
  rw [absEw_eq_sq hc τ, val_aOf, ← hφ]
  change ‖φ α.det‖₊ ^ 2 ≤ 1
  rw [← hmd]
  have h3 : ‖(α.map φ).det‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]; exact hdet
  exact pow_le_one₀ (by positivity) h3

theorem hgtArch_ioH_le_one (hc : IsCMExt F E σ) (hJ : J.det ≠ 0) (h : Q = dblGram finSumFinEquiv J)
    {w : InfinitePlace F} (b : GL (Fin n) (w.Completion ⊗[F] E)) (y : GArch σ J w) :
    hgtArch σ Q w b (ioH _ σ h (y, 1)) ≤ 1 := by
  unfold hgtArch hgtH hgtOf iwAbs
  split_ifs with hx
  · obtain ⟨k, hk, e⟩ := hx.choose_spec
    exact absEw_aH_le_one hc hJ h b y _ k hk e
  · exact le_rfl

end Place

theorem hgtW_le_one : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a →
    ∀ (w : InfinitePlace D.host.F) (y : Gw A w), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w y ≤ 1 := by
  intro D A a _ w y
  have := hgtArch_ioH_le_one (isCMExt_host D) (isHermND_gram A).2 (gram_hdbl A) (Formalism.UG.bc (compInf _ _ w) a) y
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW
  exact_mod_cast this

end GlobalTheory.Core.Rk.HgtArch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem exists_cutoff_srat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  intro D X u Fs hFs
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  haveI : DiscreteTopology (Srat X u) := Formalism.L2.SG.Pf.srat_discrete X u
  haveI : Countable (Srat X u) := Formalism.L2.SG.Pf.countable_of_discrete _
  obtain ⟨_, hleft, _⟩ := Formalism.L2.SG.EvalTOntoExt.instances X
  obtain ⟨F', hF'm, h1, h2⟩ := Formalism.L2.SG.Pf.exists_strictFund (Srat X u)
  have hF' := Formalism.L2.SG.Pf.isFund_of_strict (Srat X u) hF'm h1 h2 (X.B.I.muA X.B.μf)
  refine ⟨F'.indicator 1, measurable_one.indicator hF'm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := h1 x
    rw [tsum_eq_single (⟨s, hs⟩ : Srat X u)]
    · simp [Set.indicator_of_mem hsx]
    · intro t ht
      have hne : ((t : X.B.I.GA) * x) ∉ F' := by
        intro htx
        apply ht
        have := h2 _ hsx ((t : X.B.I.GA) * s⁻¹) ((Srat X u).mul_mem t.2 ((Srat X u).inv_mem hs))
          (by simpa [mul_assoc] using htx)
        exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
      simp [Set.indicator_of_notMem hne]
  · intro F hFm hFinv
    rw [hFs.setLIntegral_eq hF' F (fun g x => by simpa [Subgroup.smul_def, smul_eq_mul] using hFinv g g.2 x)]
    rw [← lintegral_indicator hF'm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ F' <;> simp [Set.indicator, hx]

end GlobalTheory.Core.Mi.Fold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Level

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt' {D : D7} (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_mul_mt {D : D7} (S T : HSp D) (k : GA D S) (u : WO S T) :
    actO S T k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) = u := by
  unfold actO
  rw [mt_one', Matrix.one_mul, Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]

theorem exists_common_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  intro D ψ S T χS χT om hW K hK f hf
  obtain ⟨U₀, hU₀, hUf⟩ := hf.level
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ k ∈ K,
        (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀}
      add_mem' := fun {a b} ha hb k hk => by
        have := U₀.add_mem (ha k hk) (hb k hk)
        rwa [← Matrix.add_mul] at this
      zero_mem' := fun k _ => by
        rw [Matrix.zero_mul]; exact U₀.zero_mem
      neg_mem' := fun {a} ha k hk => by
        have := U₀.neg_mem (ha k hk)
        rwa [← Matrix.neg_mul] at this }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 0) ?_, fun k hk u hu h0 => ?_⟩
  · refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u k =>
      (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀) fun k _ => ?_
    have hc : Continuous fun p : WO S T × GA D S =>
        (HMul.hMul (p.1 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S p.2) : WO S T) :=
      continuous_fst.matrix_mul ((continuous_mt' S).comp continuous_snd)
    refine (hU₀.preimage hc).mem_nhds ?_
    show (HMul.hMul (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀
    rw [Matrix.zero_mul]; exact U₀.zero_mem
  · have h1 := hUf _ (hu k hk) (by rw [Matrix.map_mul, h0]; simp)
    have h2 := hW.om_heis k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) f hf
    rw [h1, actO_mul_mt] at h2
    exact h2.symm

end GlobalTheory.Core.Rk.Level
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  intro hD hH
  obtain ⟨X, hX, d1, q5, a1, a2, a3, a5⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta hD hH
  exact ⟨X, hX, a1, a2, a3,
    _root_.GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner X (GlobalTheory.FockDeg.degrees_and_adjoints X) (GlobalTheory.FockAlg.fock_structure X) d1 q5, a5⟩

end GlobalTheory.RealPlaceTheta
end

