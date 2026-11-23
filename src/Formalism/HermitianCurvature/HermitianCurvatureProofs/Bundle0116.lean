module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAtOfExists
section
open Matrix MeasureTheory Finset
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF

theorem interp_any {ι : Type} [Fintype ι] (node : ι → ℂ) (hinj : Function.Injective node) (f : ι → ℂ) :
    ∃ q : Polynomial ℂ, ∀ i, q.eval (node i) = f i := by
  classical
  refine ⟨Lagrange.interpolate Finset.univ node f, fun i => ?_⟩
  exact Lagrange.eval_interpolate_at_node f hinj.injOn (Finset.mem_univ i)

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem frame_dframe (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ γ : B.Mat k r}
    (hD : D.IsDFrame S ν' m₀ γ) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs) :
    Q.IsFrameOf k r [γ⁻¹ *ᵥ S.z, S.z'] Bs := by
  subst hr
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨hB1, hB2, fun a v hv => ?_⟩
  simp only [List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl | hv
  · obtain ⟨-, ⟨α, -, hα⟩, -⟩ := hD
    have hcof : Formalism.FourierDecayAlt.D.cofL S γ = S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL
      simp [Matrix.adjugate_fin_one, fvec, Matrix.one_apply]
    rw [hcof] at hα
    have hvb : (fun i : Fin (2 * 0 + k + 1) => if 0 ≤ i.val ∧ i.val ≤ 0 + k then (γ⁻¹ *ᵥ S.z) i else 0) =
        γ⁻¹ *ᵥ S.z := by
      funext i
      have := i.isLt
      rw [if_pos (by omega)]
    have hpr : γ⁻¹ *ᵥ S.z = Formalism.FourierDecayAlt.D.prW k 0 S.z' (γ⁻¹ *ᵥ S.z) +
        (herm (Hpk k 0) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k 0) S.z' S.z') • S.z' := by
      unfold Formalism.FourierDecayAlt.D.prW
      dsimp only
      rw [hvb, sub_add_cancel]
    have h1 : herm (Hpk k 0) (Bs a) ν' = 0 := hB3 a ν' (by simp)
    have h2 : herm (Hpk k 0) (Bs a) S.z' = 0 := hB3 a S.z' (by simp)
    rw [hpr, hα]
    unfold herm at h1 h2 ⊢
    rw [star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2, smul_zero,
      smul_zero, add_zero]
  · exact hB3 a S.z' (by simp)
  · simp at hv

end frame

def HeadWeightAtOfEx : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.CutWord P p.l0 w → PBI.LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexOrder

theorem head_weight_at_of_exists : DiagonalScalarMatrices.HeadWeightAtOfEx := by
  intro Wp Wq _ _ _ _ _ _ P p w X μ L st ν'r m₀r hD hcut hLF x hx γ₀ hγG hζ hγF hex h hh y e
  obtain ⟨hl1, hlk, hk2⟩ := p.hl
  have hr : P.r - P.r = 0 := by omega
  have hD' := hD
  obtain ⟨hPl, -, -, -, hq, hinv, -, -⟩ := hD'
  have hOK := hPl.1

  have hw := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P P.r) _ _ _ _ st p.l0 hOK hl1 hlk hq hinv w hcut.1 hcut.2

  have hGx : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hx' : (x.1, γ₀) ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a ha => by
      exfalso; have h1 := a.isLt; have h2 : (JC.parLev P P.r).r = P.r - P.r := rfl; omega⟩, ?_⟩
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx

  have hbase := hLF.2.2
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  obtain ⟨Bs', hB'⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_exists P.k (P.r - P.r) (by omega) (p.T.bs P.r).z' ν'r
    (p.T.bs P.r).z'_mem (p.T.bs P.r).T'_pos hν hνz hνν
  have hBγ := DiagonalScalarMatrices.frame_dframe (p.T.bs P.r) hr hγF hB'

  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  set f : M.Ty P → ℂ := fun ρ => Fr.cs (M.x0 P p.l0 ρ) (M.qC P) (D.positionted w) e with hfdef
  obtain ⟨q, hq'⟩ := DiagonalScalarMatrices.interp_any (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) hY₀ f
  set V := ((y e : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
    (p.T.bs P.r).π (p.T.bs P.r).π') : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ with hVdef
  have hV := PBI.grpInt_at_dframe p hLF (y e) x hx hγG hζ hγF
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := DiagonalScalarMatrices.dw_pt (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD (D.positionted w) hw Y₀ e q hq' y x.1 γ₀ hx' Bs' hBγ v
  have h2 := DiagonalScalarMatrices.poly_types p ν'r m₀r hLF hB' V hV (hex (y e)) (Y₀ : ℂ) q v
  rw [show ((JC.parLev P P.r).k : ℂ) = (P.k : ℂ) from rfl, ← hVdef] at h1
  erw [h2] at h1
  rw [h1]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  rw [hq' ρ]
  set ζx := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζx
  have hTb : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hTb' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hTr : Tz P.k (P.r - P.r) (p.T.bs P.r).z = P.T := hPl.2.2.2.1
  have hTr' : Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T' := hPl.2.2.2.2.1
  have hzγ : Q.zetaL (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (Fin.last (JC.parLev P P.r).r) γ₀ = ζx := hζ
  have hGG : Q.GGl (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ =
      Complex.normSq ζx - P.T * P.T' := by
    show Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = _
    rw [hζ, hTr, hTr']
  have hG0 : 0 < Complex.normSq ζx - P.T * P.T' := by rw [← hTr, ← hTr']; exact hGx
  have hlen : (D.positionted w).length = w.length := List.length_ofFn
  have hcW : Top.cW P p.l0 w e ρ = f ρ := by
    simp only [Top.cW, hfdef]
    congr 1
  have hc := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
    Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin w.length) P.k P.u P.u' (M.rho P ρ) p.l0 P.T P.T'
    (D.positionted w) hl1 hlk (Formalism.FourierDecayAlt.P.types_interlace P p.hP.1 ρ) p.hP.1.T_pos p.hP.1.T'_pos hw.2.1 hw.2.2 e
  have hpos : 0 < f ρ := by rw [Complex.lt_def]; exact ⟨hc.1, hc.2.symm⟩
  have hre : 0 < (f ρ).re := (Complex.lt_def.1 hpos).1
  have him : (f ρ).im = 0 := (Complex.lt_def.1 hpos).2.symm
  have hfre : f ρ = ((f ρ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hW := PBI.wPt_app (P.T * P.T') ζx h P.r hh
  have hWnn : 0 ≤ Top.wPt (P.T * P.T') P.r (h ++ [(1, ζx)]) := by
    rw [hW]; exact div_nonneg (Complex.normSq_nonneg _) hG0.le
  unfold Top.dH
  rw [hTb, hTb', hW, hcW, Real.sq_sqrt (mul_nonneg (pow_nonneg (by rw [← hW]; exact hWnn) _) hre.le), hGG, hzγ, hlen]
  rw [hfre]
  push_cast
  rw [div_eq_mul_inv, Complex.ofReal_re]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisMeasConjInv
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

private theorem iotaLev_one_eq_blk3 (ρ : ℕ) (g : B.Mat k ρ) :
    ιLev k 1 ρ g = U.blk3 (j := 1) 1 0 0 0 g 0 0 0 1 := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective q
  rw [Ux3.block3_apply]
  have vX : ∀ x : Fin 1, ((U.eB k 1 ρ) (Sum.inl (Sum.inl x))).val = 0 := fun x => by
    simp [U.eB]
  have vV : ∀ v : Fin (2 * ρ + k + 1), ((U.eB k 1 ρ) (Sum.inl (Sum.inr v))).val = 1 + v.val := fun v => by
    simp [U.eB]
  have vS : ∀ b : Fin 1, ((U.eB k 1 ρ) (Sum.inr b)).val = 2 * ρ + k + 2 := fun b => by
    simp [U.eB] <;> omega
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp only [Formalism.QuantumDeterminants.ιLev, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, vX, vV, vS, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | (congr <;> (try apply Fin.ext) <;> simp [vV])

theorem lev_mMap (ρ : ℕ) (g g' : B.Mat k ρ) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    ιLev k 1 ρ g * U.mMap k 1 ρ Z γ * ιLev k 1 ρ g' = U.mMap k 1 ρ Z (g * γ * g') := by
  rw [iotaLev_one_eq_blk3, iotaLev_one_eq_blk3]
  simp only [U.mMap]
  rw [Ux5.block3_mul_blocks, Ux5.block3_mul_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem sgs_alg (ρ : ℕ) (h0 y h0' y' : B.Mat k ρ) (hh0 : IsUnit h0.det) (hy : IsUnit y.det) (hh0' : IsUnit h0'.det)
    (hy' : IsUnit y'.det) (a a' : B.Mat k (1 + ρ)) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    (ιLev k 1 ρ h0)⁻¹ * (a * ιLev k 1 ρ y)⁻¹ * U.mMap k 1 ρ Z γ * (a' * ιLev k 1 ρ y') * ιLev k 1 ρ h0' =
      ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0))⁻¹ *
        U.mMap k 1 ρ Z ((y * h0)⁻¹ * γ * (y' * h0')) * ((ιLev k 1 ρ (y' * h0'))⁻¹ * a' * ιLev k 1 ρ (y' * h0')) := by
  have hL0 := PI.QnLevBasicsW.level_group_homomorphism
  have hL := hL0
  unfold Formalism.QuantumDeterminants.LevHom at hL
  have ιmul : ∀ g h : B.Mat k ρ, ιLev k 1 ρ (g * h) = ιLev k 1 ρ g * ιLev k 1 ρ h := (hL k 1 ρ).2
  have ιone : ιLev k 1 ρ (1 : B.Mat k ρ) = 1 := (hL k 1 ρ).1
  have ιinv : ∀ g : B.Mat k ρ, IsUnit g.det → (ιLev k 1 ρ g)⁻¹ = ιLev k 1 ρ g⁻¹ :=
    fun g hg => PIQnLT.ιLev_inv hL0 g hg
  have hW : IsUnit (y * h0).det := by
    rw [Matrix.det_mul]
    exact hy.mul hh0
  have hW' : IsUnit (y' * h0').det := by
    rw [Matrix.det_mul]
    exact hy'.mul hh0'
  have hW1 : ∀ X, ιLev k 1 ρ (y * h0) * (ιLev k 1 ρ (y * h0)⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW, ιone, one_mul]
  have hW2 : ∀ X, ιLev k 1 ρ (y' * h0') * (ιLev k 1 ρ (y' * h0')⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW', ιone, one_mul]
  have hLw : ∀ X, ιLev k 1 ρ h0⁻¹ * (ιLev k 1 ρ y⁻¹ * X) = ιLev k 1 ρ (y * h0)⁻¹ * X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_inv_rev]
  have hRw : ιLev k 1 ρ y' * ιLev k 1 ρ h0' = ιLev k 1 ρ (y' * h0') := (ιmul _ _).symm
  rw [Matrix.mul_inv_rev a, ιinv _ hh0, ιinv _ hy, ιinv _ hW, ιinv _ hW', ← lev_mMap]
  rw [Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹ * a) (ιLev k 1 ρ (y * h0)),
    Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹) a, ιinv _ hW, ιinv _ (Matrix.isUnit_nonsing_inv_det _ hW),
    Matrix.nonsing_inv_nonsing_inv _ hW]
  simp only [mul_assoc]
  rw [hLw, hRw, hW1, hW2]

theorem psi_Qm (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : Mt k (1 + ρ)} {y : Mt k ρ}
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (hy : Matrix.of y ∈ Nset k ρ) :
    psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (D.castM (Nat.add_comm 1 ρ) (Matrix.of a)) *
        psi k ρ z0 cStd (Matrix.of y) := by
  show psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd
      (D.castM (Nat.add_comm 1 ρ) (Matrix.of a * ιLev k 1 ρ (Matrix.of y))) = _
  rw [psi_castM, psi_castM, Qx4.psi_mul (Qx4.lift_inWb hz0) ha (B2x6.lev_n hy), Qx4.psi_lev]

theorem psi_conjLev (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : B.Mat k (1 + ρ)}
    {y h0 : B.Mat k ρ} (ha : a ∈ Nset k (1 + ρ)) (hy : y ∈ Nset k ρ) (hh0 : h0 ∈ UWset k ρ z0) :
    psi k (1 + ρ) (liftVec k 1 ρ z0) cStd ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0)) =
      psi k (1 + ρ) (liftVec k 1 ρ z0) cStd a := by
  have hz1 := Qx4.lift_inWb hz0
  have hyN : ιLev k 1 ρ y ∈ Nset k (1 + ρ) := B2x6.lev_n hy
  have hhW : ιLev k 1 ρ h0 ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := Dx2.Tower.lev_UW 1 ρ z0 h0 hh0
  have hu : (ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y ∈ Nset k (1 + ρ) :=
    WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hyN) ha) hyN
  have e : (ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0) =
      (ιLev k 1 ρ h0)⁻¹ * ((ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y) * ιLev k 1 ρ h0 := by
    rw [Dx2.Tower.lev_mul, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [e, Qx4.psi_conjW' hz1 hhW hu, Qx4.psi_conjN' hz1 hyN ha]

theorem heis_meas_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    (B2.μHeis k ρ).map (conjM ((ιLev k 1 ρ g)⁻¹)) = B2.μHeis k ρ := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure k ρ g⁻¹ hgi
  rwa [LongWeylElement.lev_inv _ hu] at h

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerBound
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cmHalfIntegralGenerator_mem_algebraicClosure {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) : w0 ∈ DDsp σ w0 := by
  have hone : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  refine Submodule.subset_span ⟨1, hone, ?_⟩
  show σ 1 w0 = w0
  rw [(MatrixMultiplicationContinuity.sigma_facts hds).1]; rfl

theorem enorm_smulRight {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E) (b : F) :
    ‖(innerSL ℂ a).smulRight b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, ENNReal.ofReal_mul (norm_nonneg _)]

theorem mt_cont : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := by
  first
    | exact continuous_id
    | fun_prop
    | continuity

theorem inner_bound (hNI : NormInv) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    (hGc : ∀ᵐ x ∂μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) {C1 C2 a b : ℝ}
    (hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-a))
    (hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a)
    {P Q γi : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hγ : γi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ x, ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ ∂μG ≤
      ENNReal.ofReal (|C1| * |C2|) * ‖B.gN (Q * γi * P⁻¹) ^ (-b)‖ₑ *
        ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
  obtain ⟨hPi, hPP, -⟩ := MatrixMultiplicationContinuity.uh_inv hP
  set Y : Mx k r := Q * γi * P⁻¹ with hY
  have hYU : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hQ hγ) hPi
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ with hF
  have hFm : Measurable F := by
    have c1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e1 (P * Matrix.of x)) :=
      he1.comp (continuous_const.matrix_mul mt_cont)
    have c2 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e2 (Q * (γi * Matrix.of x))) :=
      he2.comp (continuous_const.matrix_mul (continuous_const.matrix_mul mt_cont))
    exact c1.measurable.enorm.mul c2.measurable.enorm
  have hNI' := hNI k r
  calc ∫⁻ x, F x ∂μG = ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM P⁻¹ x) ∂μG := (lint_left hG hPi hFm).symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ) * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
        apply lintegral_mono_ae
        filter_upwards [hGc] with x hx
        have e1x : P * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x) = Matrix.of x := by
          show P * (P⁻¹ * Matrix.of x) = Matrix.of x
          rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
        have e2x : Q * (γi * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x)) = Y * Matrix.of x := by
          show Q * (γi * (P⁻¹ * Matrix.of x)) = Q * γi * P⁻¹ * Matrix.of x
          simp only [Matrix.mul_assoc]
        simp only [hF]
        rw [e1x, e2x]
        have hYx : Y * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hYU hx
        have ht1 : 1 ≤ B.gN (Matrix.of x) := (hNI'.2 _ hx).2
        have htp : 0 < B.gN (Matrix.of x) := lt_of_lt_of_le one_pos ht1
        have hs1 : 1 ≤ B.gN (Y * Matrix.of x) := (hNI'.2 _ hYx).2
        have hYp : 0 ≤ B.gN Y ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
        have bnd1 : ‖e1 (Matrix.of x)‖ ≤ |C1| * B.gN (Matrix.of x) ^ (-a) :=
          (hb1 _ hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htp.le _))
        have bnd2 : ‖e2 (Y * Matrix.of x)‖ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) := by
          refine (hb2 _ hYx).trans ?_
          calc C2 * B.gN (Y * Matrix.of x) ^ (-a) ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-a) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
            _ ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-b) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)) (abs_nonneg _)
            _ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) :=
                mul_le_mul_of_nonneg_left (gN_mul_rpow hNI hx hYU hb0) (abs_nonneg _)
        have key : |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b))) =
            (|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b)) := by
          have : B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b = B.gN (Matrix.of x) ^ (-(a - b)) := by
            rw [← Real.rpow_add htp]; ring_nf
          calc |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)))
              = (|C1| * |C2|) * B.gN Y ^ (-b) * (B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b) := by ring
            _ = _ := by rw [this]
        have hxp : 0 ≤ B.gN (Matrix.of x) ^ (-(a - b)) := Real.rpow_nonneg htp.le _
        have hC : 0 ≤ |C1| * |C2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have L : ‖e1 (Matrix.of x)‖ₑ * ‖e2 (Y * Matrix.of x)‖ₑ =
            ENNReal.ofReal (‖e1 (Matrix.of x)‖ * ‖e2 (Y * Matrix.of x)‖) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
        have R : ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ =
            ENNReal.ofReal ((|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b))) := by
          rw [Real.enorm_eq_ofReal hYp, Real.enorm_eq_ofReal hxp, ENNReal.ofReal_mul (mul_nonneg hC hYp),
            ENNReal.ofReal_mul hC]
        rw [L, R]
        apply ENNReal.ofReal_le_ofReal
        rw [← key]
        exact mul_le_mul bnd1 bnd2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _))
    _ = ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG :=
        lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrApply
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section gen

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def inE : α × (β × γ) ≃ᵐ β × (α × γ) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)).trans MeasurableEquiv.prodAssoc)

theorem inE_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (inE : α × (β × γ) ≃ᵐ β × (α × γ)) (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have e1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have e2 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)
  have e3 := measurePreserving_prodAssoc μb μa μc
  exact e3.comp (e2.comp e1)

end gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def rearr (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) :
    OD.RR k r w ≃ᵐ ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r :=
  (MeasurableEquiv.prodCongr inE inE).trans Dx2.SL.swap4

@[simp] theorem rearr_apply (w : Equiv.Perm (Fin (r + 1))) (q : OD.RR k r w) :
    rearr k r w q = ((q.1.2.1, q.2.2.1), ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2))) := rfl

private theorem measurePreserving_swap4 {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa]
    [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (Dx2.SL.swap4 : (α × β) × γ × δ ≃ᵐ (α × γ) × β × δ) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd)
  have e3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have e4 := measurePreserving_prodAssoc μc μb μd
  have e5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have h := (e5.comp ((MeasurePreserving.id μa).prod (e4.comp (e3.comp e2)))).comp e1
  convert h using 1
  funext p
  rfl

theorem mp_rearr (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1))) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') :
    MeasurePreserving (rearr k r w) (OD.nuR S w μ0 μ0')
      (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
        ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t3 : SFinite (volume : Measure (C2.LPidx w → ℂ)) := inferInstance
  haveI t4 : SFinite (volume : Measure (G.UT (r + 1) → ℂ)) := inferInstance
  have h1 := (inE_mp S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
    (inE_mp S.μW' (volume : Measure (G.UT (r + 1) → ℂ)) μ0')
  have h2 := measurePreserving_swap4 (volume : Measure (C2.LPidx w → ℂ)) (S.μW.prod μ0)
    (volume : Measure (G.UT (r + 1) → ℂ)) (S.μW'.prod μ0')
  exact h2.comp h1

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE
end

