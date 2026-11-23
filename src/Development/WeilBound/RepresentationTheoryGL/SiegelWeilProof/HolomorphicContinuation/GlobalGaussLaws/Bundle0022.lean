module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0019
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

abbrev Ev (D : D7) (v : GlobalTheory.FinPl.Pl D) := Fv D.host.F v ⊗[D.host.F] D.host.E

def IsIntUnit {D : D7} {v : GlobalTheory.FinPl.Pl D} (z : Ev D v) : Prop :=
  z ∈ intLoc D.host.F D.host.E v ∧ ∃ z' ∈ intLoc D.host.F D.host.E v, z * z' = 1

def cTv {D : D7} {v : GlobalTheory.FinPl.Pl D} (a : Matrix (Fin n) (Fin n) (Ev D v)) : Matrix (Fin n) (Fin n) (Ev D v) :=
  (a.map (sigR (Fv D.host.F v) D.sp.cm.sig)).transpose

def LocGood {D : D7} {v : GlobalTheory.FinPl.Pl D} (kv : Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v))
    (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)) : Prop :=
  (∀ i j, a i j ∈ intLoc D.host.F D.host.E v) ∧ IsIntUnit a.det ∧
    IsIntUnit (blkDm (kv * blk4 a 0 0 (cTv a)⁻¹ * wIm I)).det

def LocFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, ∀ v : GlobalTheory.FinPl.Pl D,
    ∃ (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)), LocGood ((mat k).map (GlobalTheory.FinPl.compAt D v)) a I

def GlueLevi : Prop :=
  ∀ (D : D7) (n : ℕ) (a : ∀ v : GlobalTheory.FinPl.Pl D, Matrix (Fin n) (Fin n) (Ev D v)),
    (∀ v i j, a v i j ∈ intLoc D.host.F D.host.E v) → (∀ v, IsIntUnit (a v).det) →
    ∃ m : G D n, m ∈ genSet D n ∧ (∀ v, (mat m).map (GlobalTheory.FinPl.compAt D v) = blk4 (a v) 0 0 (cTv (a v))⁻¹) ∧
      ∀ τ, (mat m).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def GlueW : Prop :=
  ∀ (D : D7) (n : ℕ) (I : GlobalTheory.FinPl.Pl D → Finset (Fin n)),
    ∃ w ∈ Subgroup.closure (genSet D n), (∀ v, (mat w).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)) ∧
      ∀ τ, (mat w).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def UnitAE : Prop :=
  ∀ (D : D7) (d : AE D), (∀ τ, Formalism.IndefR.Eqv.psiT D τ d ≠ 0) → (∀ v, IsIntUnit (GlobalTheory.FinPl.compAt D v d)) → IsUnit d

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenInfH

open PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

variable {D : D7} {n : ℕ}

theorem isUnit_of_comps (x : AE D) (h1 : ∀ τ, psiT D τ x ≠ 0) (h2 : IsUnit (finPart D x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h2
  set y : AE D := glueA D (splitInv D fun τ => (psiT D τ x)⁻¹) ((u⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)
  have hxy : x * y = 1 := by
    apply ae_ext' D
    · intro τ
      rw [map_mul, psiT_glueA, map_one, mul_inv_cancel₀ (h1 τ)]
    · rw [map_mul, finPart_glueA, map_one, ← hu, Units.mul_inv]
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem cT_blk4 {R : Type} [CommRing R] (σ : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (blk4 a b c d) = blk4 (Formalism.UG.cT σ a) (Formalism.UG.cT σ c) (Formalism.UG.cT σ b) (Formalism.UG.cT σ d) := by
  ext i j
  simp only [Formalism.UG.cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem cT_zero' {R : Type} [CommRing R] (σ : R →+* R) : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_neg' {R : Type} [CommRing R] (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (-M) = -Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem blk4_neg {R : Type} [CommRing R] (a b c d : Matrix (Fin n) (Fin n) R) :
    blk4 (-a) (-b) (-c) (-d) = -blk4 a b c d := by
  ext i j
  simp only [blk4, Matrix.neg_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    blkDm (M.map f) = (blkDm M).map f := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkDm, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem eI_mul_self {R : Type} [CommRing R] (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  simp only [eI, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem eI_conjTranspose (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) ℂ)ᴴ = eI I := by
  simp only [eI, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem weyl_idem {R : Type} [CommRing R] (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) :
    blk4 1 e 0 1 * blk4 1 0 (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.add_mul, he]
  congr 1 <;> abel

theorem unip_unitary {R : Type} [CommRing R] (σ : R →+* R) (b : Matrix (Fin n) (Fin n) R) (hb : Formalism.UG.cT σ b = b) :
    Formalism.UG.cT σ (blk4 1 b 0 1) * blk4 0 1 (-1) 0 * blk4 1 b 0 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hb, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem unipBar_unitary {R : Type} [CommRing R] (σ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (hc : Formalism.UG.cT σ c = c) :
    Formalism.UG.cT σ (blk4 1 0 c 1) * blk4 0 1 (-1) 0 * blk4 1 0 c 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hc, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem JR_Jst (D : D7) (n : ℕ) : JR (F := D.host.F) (AF D.host.F) (Jst D n) = blk4 0 1 (-1) 0 := by
  rw [JR, Jst, block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _)]

def nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) b = b) : G D n :=
  (⟨⟨blk4 1 b 0 1, blk4 1 (-b) 0 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 b 0 1) * JR (AF D.host.F) (Jst D n) * blk4 1 b 0 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unip_unitary _ b hb⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) c = c) : G D n :=
  (⟨⟨blk4 1 0 c 1, blk4 1 0 (-c) 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 0 c 1) * JR (AF D.host.F) (Jst D n) * blk4 1 0 c 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unipBar_unitary _ c hc⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

theorem mat_nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb) : mat (nEl b hb) = blk4 1 b 0 1 := rfl

theorem mat_nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc) : mat (nBarEl c hc) = blk4 1 0 c 1 := rfl

theorem cT_starRingEnd (M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]


set_option maxHeartbeats 1000000 in
theorem exists_I (hL : LocRedField) (k : G D n) (τ : D.what₂.Tau) :
    ∃ I : Finset (Fin n), IsUnit (blkDm ((mat k).map (psiT D τ) * wIm I)).det := by
  set M := (mat k).map (psiT D τ) with hM
  have hgU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have hu : Mᴴ * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0 := by
    have := congrArg (fun X => X.map (psiT D τ)) hgU
    simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at this
    exact this
  have hJJ : (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
    rw [submatrix_fromBlocks_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
    rw [← block_matrix_one, ← blk4_neg, neg_zero]
  have hinv : ((-(blk4 0 1 (-1) 0)) * Mᴴ * blk4 0 1 (-1) 0) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, Matrix.neg_mul, hJJ, neg_neg]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hinv
  have hg : Matrix.nonsingInvUnit M hdet ∈ Formalism.UG.UJ (starRingEnd ℂ) (J2 ℂ n) := by
    show Formalism.UG.cT (starRingEnd ℂ) M * J2 ℂ n * M = J2 ℂ n
    rw [cT_starRingEnd]
    exact hu
  obtain ⟨I, hI⟩ := hL ℂ (starRingEnd ℂ) (fun a => star_star a) n _ hg
  exact ⟨I, hI⟩

end PositivityTheory.Rg.Sw.Glob.GenInfH

namespace PositivityTheory.Rg.Sw.Glob

open GenInfH PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

set_option maxHeartbeats 1000000 in
theorem kInInf_of (hU : UnitD) (hL : LocRedField) : KInInf := by
  intro D n k hk hfin
  classical
  choose I hI using exists_I hL k
  set B : Matrix (Fin n) (Fin n) (AE D) :=
    Matrix.of fun i j => glueA D (splitInv D fun τ => (eI (I τ) : Matrix (Fin n) (Fin n) ℂ) i j) 0 with hBdef
  have hBτ : ∀ τ, B.map (psiT D τ) = eI (I τ) := by
    intro τ; ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  have hBf : B.map (finPart D) = 0 := by
    ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, finPart_glueA, Matrix.zero_apply]
  have hBB : B * B = B := by
    apply mat_ext D
    · intro τ; rw [Matrix.map_mul, hBτ, eI_mul_self]
    · rw [Matrix.map_mul, hBf, Matrix.zero_mul]
  have hBc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    apply mat_ext D
    · intro τ; rw [cT_map_psiT', hBτ, eI_conjTranspose]
    · rw [PositivityTheory.Rg.Sw.Glob.EmbP.cT_map_fin, hBf]
      ext i j; simp [Formalism.UG.cT]
  have hBc' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [cT_neg', hBc]
  set W : G D n := nEl B hBc * nBarEl (-B) hBc' * nEl B hBc with hW
  have hWmat : mat W = blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1 := rfl
  have hWτ : ∀ τ, (mat W).map (psiT D τ) = wIm (I τ) := by
    intro τ
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBτ, weyl_idem _ (eI_mul_self _)]
    rfl
  have hWf : (mat W).map (finPart D) = 1 := by
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBf, neg_zero, block_matrix_one, Matrix.one_mul, Matrix.one_mul]
  have hunit : IsUnit (blkDm (mat (k * W))).det := by
    apply GenInfH.isUnit_of_comps
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hWτ]
      exact (hI τ).ne_zero
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hfin, hWf, Matrix.one_mul,
        blkDm_one, Matrix.det_one]
      exact isUnit_one
  have h1 := hU D n (k * W) hunit
  have h2 : W ∈ Subgroup.closure (genSet D n) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inr ⟨-B, rfl⟩))
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
  have : k = (k * W) * W⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenTop
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenTopH

variable {D : D7} {n : ℕ}

theorem mat_projFin (g : G D n) : (mat g).map (finPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projFin D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

theorem mat_projInf (g : G D n) : (mat g).map (infPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projInf D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

end PositivityTheory.Rg.Sw.Glob.GenTopH

namespace PositivityTheory.Rg.Sw.Glob

theorem genA_of : UnitD → PIn → KInInf → KInFin → GenA := by
  intro _ hP hKi hKf D n
  show Subgroup.closure (genSet D n) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  refine Subgroup.mul_mem _ (hP D n p hp) ?_
  rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]
  have hk' := mem_levelAll.1 hk
  refine Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofInf]; exact one_mem _
    · rw [projArch_ofInf, projInfArch_projInf]; exact hk'.2 w
  · rw [GenTopH.mat_projFin, projFin_ofInf]; rfl
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofFin, projFinLoc_projFin]; exact hk'.1 v
    · rw [projArch_ofFin]; exact one_mem _
  · intro τ
    have e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D) := rfl
    rw [e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]
    exact Matrix.map_one _ (map_zero _) (map_one _)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasDeriv
section
noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalc2H

open DCalcH DCalcBH DCalcDH DCalcEH

variable {m n : ℕ}

theorem hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun t => fF c X P u t) (fF c X (dil c X P) u t) t :=
  fF_hasDeriv c X P u t

theorem quot_le (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s B : ℝ)
    (hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ B) (h : ℝ) (hh : |h| ≤ 1) :
    ‖fF c X P u (s + h) - fF c X P u s‖ ≤ B * |h| := by
  have hcv : Convex ℝ (Set.Icc (s - 1) (s + 1)) := convex_Icc _ _
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hsh : s + h ∈ Set.Icc (s - 1) (s + 1) := by
    rw [abs_le] at hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have := hcv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => fF c X P u t)
    (fun t _ => (hasDeriv c X P u t).hasDerivWithinAt) hB hs hsh
  simpa [Real.norm_eq_abs] using this

theorem l2conv (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) (s : ℝ) :
    Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, a, hK, ha, hb⟩ := fF_bound c hc X (dil c X P) s
  suffices key : Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ _u : Fin m → Fin n → ℂ, (0 : ℝ))) by simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    refine Continuous.aestronglyMeasurable ?_
    have h1 := fF_cont c X P (s + h)
    have h2 := fF_cont c X P s
    have h3 := fF_cont c X (dil c X P) s
    fun_prop
  · have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| ≤ 1 ∧ h ≠ 0 := by
      refine (eventually_nhdsWithin_of_eventually_nhds ?_).and self_mem_nhdsWithin
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [hev] with h ⟨hh, h0⟩
    refine Eventually.of_forall fun u => ?_
    have hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ K * Real.exp (-(a * sqN u)) := fun t ht => hb u t ht
    have hq := quot_le c X P u s _ hB h hh
    have hhpos : 0 < |h| := abs_pos.2 h0
    have e1 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ ≤ K * Real.exp (-(a * sqN u)) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hhpos]
      exact hq
    have e2 : ‖fF c X (dil c X P) u s‖ ≤ K * Real.exp (-(a * sqN u)) := hb u s ⟨by linarith, by linarith⟩
    have e3 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ≤ 2 * K * Real.exp (-(a * sqN u)) := by
      calc _ ≤ ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ + ‖fF c X (dil c X P) u s‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2
        ≤ (2 * K * Real.exp (-(a * sqN u))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
      _ = (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  · exact (integrable_gauss (2 * a) (by positivity)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have : Tendsto (fun h : ℝ => (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s) (𝓝[≠] 0) (𝓝 0) := by
      have h2 := (hasDeriv c X P u s).tendsto_slope_zero
      have h3 := h2.sub_const (fF c X (dil c X P) u s)
      rw [sub_self] at h3
      refine h3.congr' (Eventually.of_forall fun h => ?_)
      show h⁻¹ • (fF c X P u (s + h) - fF c X P u s) - fF c X (dil c X P) u s =
        (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    have := (this.norm).pow 2
    simpa using this

end DCalc2H

end PositivityTheory.Rg.Sw.Glob

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermFourierZero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

theorem hermCocompact (D : D7) (r : ℕ) :
    ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K := by
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKx x
  refine ⟨-γ, neg_mem hγ, ?_⟩
  rwa [sub_neg_eq_add, add_comm]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem hermFourierZero (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (lam : Measure (hermA D r)) (hH : lam.IsAddHaarMeasure) (𝓖 : Set (hermA D r))
    (h𝓖 : IsAddFundamentalDomain (ratHerm D r) 𝓖 lam) (φ : hermA D r → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, ∀ l ∈ ratHerm D r, φ (x + l) = φ x)
    (hco : ∀ β : HermE D r,
      ∫ b in 𝓖, φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam = 0) :
    ∀ x, φ x = 0 := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨K, hK, hc⟩ := hermCocompact D r
  intro x
  refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam h𝓖 hK hc (T := ratHerm D r)
    (fun t b => chi ψ t.1.1 b) (fun t => continuous_chi hψ t.1.1) ?_ ?_ ?_ ?_ ?_ φ hφ hper ?_ x
  · intro t y l hl
    show chi ψ t.1.1 (y + l) = chi ψ t.1.1 y
    rw [chi_add_right, chi_rat hψ (hmem t) ⟨l, hl⟩, mul_one]
  · intro y
    exact chi_zero_left ψ y
  · intro s t y
    exact chi_add_left ψ s.1.1 t.1.1 y
  · intro t y
    show star (chi ψ t.1.1 y) = chi ψ (-t.1.1) y
    rw [chi_neg_left]
    exact star_psi' hψ _
  · intro a b hab
    refine rat_of_chi hψ (-a + b) fun t => ?_
    have h1 : chi ψ t.1.1 a * chi ψ t.1.1 (-a) = 1 := by
      rw [← chi_add_right, add_neg_cancel, chi_zero_right]
    rw [chi_add_right, ← hab t, mul_comm]
    exact h1
  · intro t
    obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := r)).2 t
    have h1 : ∀ b : hermA D r, chi ψ (-t).1.1 b =
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := fun b => by
      show chi ψ (-t.1.1) b = _
      rw [chi_neg_left, ← hβ, ofHermE_val]
    simp only [h1]
    exact hco β

end PositivityTheory.Rg.Sw.Glob
end
end

