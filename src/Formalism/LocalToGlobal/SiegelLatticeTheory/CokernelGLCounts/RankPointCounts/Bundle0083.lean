module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealConjugatorData
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RealConjugatorData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) :
    Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_inv' {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ = (uMat g)⁻¹ := by
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)⁻¹
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g * (uMat g)⁻¹ = 1 := by
  rw [← uMat_inv']
  show (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ * uMat g = 1 := by
  rw [← uMat_inv']
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

def cMr (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)

theorem cMr_eq (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    cMr C γ τ y = Formalism.L2.SG.RealFrameCoordinates.cMg C γ τ y := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ
  simp only [Matrix.mul_assoc]

theorem cMr_closedEmb : Topology.IsClosedEmbedding (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  set g := uMat (γ (vOf X τ))
  have h1 : g * g⁻¹ = 1 := uMat_mul_inv _
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  let L : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ ≃ₜ
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
    { toFun := fun M => C.Qi τ * g⁻¹ * M * (g * C.Q τ)
      invFun := fun M => g * C.Q τ * M * (C.Qi τ * g⁻¹)
      left_inv := fun M => by
        show g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹) = M
        calc g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹)
            = g * (C.Q τ * C.Qi τ) * g⁻¹ * M * (g * (C.Q τ * C.Qi τ) * g⁻¹) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [hQQi, Matrix.mul_one, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun M => by
        show C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ) = M
        calc C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ)
            = C.Qi τ * (g⁻¹ * g) * C.Q τ * M * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp ((Formalism.REAL.isClosedEmbeddingMatrix _ (X.B.I.ε (vOf X τ))).1)

theorem cMr_measEmb : MeasurableEmbedding (cMr C γ τ) := (cMr_closedEmb C γ τ).measurableEmbedding

variable (u u' : D.what₂.Word)

theorem conjugator_inverse : (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ =
    C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  refine Matrix.inv_eq_right_inv ?_
  show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = 1
  calc C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ)
      = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, hQiQ]

theorem stV_iff (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ) ↔
      cMr C γ τ y ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := y.2
  have hy' : (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)).2
  have h1 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u τ).1 _ hy
  have h2 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u' τ).1 _ hy'
  have e2 : C.Qi τ * uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) * C.Q τ = cMr C γ τ y := by
    rw [cMr_eq]
    unfold Formalism.L2.SG.RealFrameCoordinates.cMg
    rw [show uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = uMat ((γ (vOf X τ))⁻¹) * uMat y * uMat (γ (vOf X τ)) from rfl,
      uMat_inv']
  have e1 : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)) * Matrix.of (cMr C γ τ y) *
      (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ = C.Qi τ * uMat y * C.Q τ := by
    rw [conjugator_inverse]
    show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ)) *
      (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = C.Qi τ * uMat y * C.Q τ
    calc _ = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * uMat y *
          (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, Matrix.mul_one]
  show (Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat y) ∧ Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))) ↔ _
  rw [h1, h2, e2]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    convert ha using 1
    exact e1
  · rintro ⟨hb, ha⟩
    refine ⟨?_, hb⟩
    convert ha using 1
    exact e1.symm

theorem rset_range (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ)) :
    m ∈ Set.range (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hmU : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm.1.1
  have hgi0 : (uMat (γ (vOf X τ))⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (γ (vOf X τ))⁻¹ =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹).2
  rw [uMat_inv'] at hgi0
  set g := uMat (γ (vOf X τ))
  have hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (γ (vOf X τ)).2
  have hgi : (g⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g⁻¹ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := hgi0
  have hQi : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    rw [← hH]
    calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
        = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  set M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹ with hM
  have hMU : Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M
        = (g⁻¹)ᴴ * ((C.Qi τ)ᴴ * ((Matrix.of m)ᴴ * ((C.Q τ)ᴴ *
            (gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g) * C.Q τ) * Matrix.of m) * C.Qi τ) * g⁻¹ := by
          rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg, hH, hmU, hQi, hgi]
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  refine ⟨toUJn M hMU, ?_⟩
  show C.Qi τ * g⁻¹ * M * (g * C.Q τ) = Matrix.of m
  rw [hM]
  calc C.Qi τ * g⁻¹ * (g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹) * (g * C.Q τ)
      = (C.Qi τ * (g⁻¹ * g) * C.Q τ) * Matrix.of m * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of m := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.RealConjugatorData

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
section
noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem permSign_mul_self₂ : Formalism.L2.SG.LsDatumB.sgnP (D := D) p * Formalism.L2.SG.LsDatumB.sgnP p = 1 := by
  unfold Formalism.L2.SG.LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sgn_conj_intUp {ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (hρ : (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ (Z.M p).R) :
    (∀ a, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a a = 1) ∧
      (∀ a b, b < a → (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = 0) ∧
      ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b ∈ (Z.M p).R := by
  have e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
    intro a b
    simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [e, hρ.2.1 a b h]; simp
  · rw [e]
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

theorem modeL (hs : (Z.M p).split = none) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  have hR : (Z.M p).R = (Z.M p).L.O := by
    unfold Formalism.MainNotions.S.Loc.Model.R
    rw [hs]
  have eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by
    intro X
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K := by
    refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
    · rw [hR]
      simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.LocCntLat.GC.cj_mem_O _ (hNO b a)
  have hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M) := ⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩
  have hdet : IsUnit K.det := by
    have hb : K.BlockTriangular OrderDual.toDual := fun i j hij => hKlow.2.1 i j hij
    have hd : K.det = 1 := by
      rw [Matrix.det_of_lowerTriangular K hb]
      simp [hKlow.1]
    rw [hd]
    exact isUnit_one
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]
  refine ⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p,
    Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩
  rw [eZZ, eZZ, hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeL

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentMatrixMapSecondComponent
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Sandwich

variable {K : Type*} [CommRing K] {r : ℕ}

theorem corner_sandwich (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hA : ∀ i, A i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hB : ∀ j, B (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : K) :
    A * cornerM (r := r) c * B = cornerM c := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hA, hB]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    have h0 : ∀ k, (A i k * if k = Fin.last r ∧ l = Fin.last r then c else 0) = 0 := by
      intro k
      simp [hl]
    simp [h0]
  · simp

theorem Ec_eq_cornerM : (Ec (K := K) r) = cornerM 1 := rfl

end Sandwich

section Comp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L)

def π1 : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def π2 : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem π1_apply (x : E) : π1 M g x = (g.e x).1 := rfl
theorem π2_apply (x : E) : π2 M g x = (g.e x).2 := rfl

variable {r : ℕ}

def mmG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).2, (g.e (L j i)).1)

def uuG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).1, (g.e (L j i)).2)

theorem middleMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π1 M g) = P.map (π2 M g) := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
theorem middleMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π2 M g) = (L.map (π1 M g))ᵀ := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
theorem unipotentMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π1 M g) = P.map (π1 M g) := by
  ext i j
  simp [uuG, π1_apply, π2_apply]
theorem unipotentMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π2 M g) = (L.map (π2 M g))ᵀ := by
  ext i j
  simp [uuG, π1_apply, π2_apply]

theorem zzPlus_map_firstComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π1 M g) =
      ((g.q : F))⁻¹ • Zh.map (π1 M g) + (T / (g.q : F)) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π1_apply]
    ring
  · simp [h, cornerM, π1_apply]
    ring

theorem zzPlus_map_secondComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π2 M g) =
      (-((g.q : F))⁻¹) • (Zh.map (π2 M g))ᵀ + (-(T' / (g.q : F))) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π2_apply]
    ring
  · simp [h, cornerM, π2_apply]
    ring

end Comp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

