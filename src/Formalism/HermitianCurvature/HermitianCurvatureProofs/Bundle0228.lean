module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0223
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0225
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalBuiltPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvMain
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

theorem assembleP {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (al : ι → ℂ) (R : ι → Fin t → Fin N) (be be' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → ι → ℂ) (qd : (Fin t → Fin N) → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ X : (Fin t → Fin N) → M, ∑ c ∈ T, (∑ i, al i * pc c i) • X c = lam • ∑ i, al i • X (R i))
    (hB : ∀ d, ∑ J ∈ T, be J * qd J d = mu * be' d) :
    ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ i, ∑ J ∈ T, (al i * be' J) • D (R i) J := by
  have e1 : ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ c ∈ T, ∑ i, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d := Finset.sum_comm
      _ = ∑ c ∈ T, ∑ i, ∑ d ∈ T, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
      _ = ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d =
      ∑ c ∈ T, (∑ i, al i * pc c i) • ∑ d ∈ T, (∑ J ∈ T, be J * qd J d) • D c d := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hB]
  rw [hA (fun c => ∑ d ∈ T, (mu * be' d) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (al i * be' J) * hlm

theorem assembleM {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (bb : ι → ℂ) (C : ι → Fin t → Fin N) (al al' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → (Fin t → Fin N) → ℂ) (qd : ι → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ c, ∑ J ∈ T, al J * pc c J = lam * al' c)
    (hB : ∀ X : (Fin t → Fin N) → M, ∑ d ∈ T, (∑ i, bb i * qd i d) • X d = mu • ∑ i, bb i • X (C i)) :
    ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ i, ∑ J ∈ T, (bb i * al' J) • D J (C i) := by
  have e1 : ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, ∑ c ∈ T, ∑ d ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
      _ = ∑ i, ∑ d ∈ T, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ d ∈ T, ∑ i, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d := Finset.sum_comm
      _ = ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d =
      ∑ d ∈ T, (∑ i, bb i * qd i d) • ∑ c ∈ T, (∑ J ∈ T, al J * pc c J) • D c d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hA]
  rw [hB (fun d => ∑ c ∈ T, (lam * al' c) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (bb i * al' J) * hlm

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem one_GV : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem left_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r := by
  have := WeylGroupFacts.uh_inv (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)
  rwa [Matrix.mul_inv_rev] at this

theorem rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (G : Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D p G = fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (G ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  rw [Formalism.FourierDecayAlt.P.JFxB.rho_eq_trn']
  funext x
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.trn, Matrix.mul_assoc]

open Classical in
theorem jset_eq : (Finset.univ.filter fun C : Fin (r + k) → Fin (2 * r + k + 1) => StrictMono C) = jSetR k r := rfl

theorem qminor_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) F) {g : Mat k r} (hg : g ∈ GV k r)
    (a b : Fin (r + k) → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (∑ c ∈ jSetR k r, ∑ d ∈ jSetR k r,
        (((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹.submatrix c a).det *
          ((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r).submatrix b d).det) •
        qminorOp (Q.EH k r) c d u F
          ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hAG := left_GV D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ GV k r := WeylGroupFacts.uh_mul hg hSG
  have hG' : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) (fun x =>
      F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG hSG
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) =
        fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
      funext x; simp only [Matrix.mul_assoc]
    rwa [e] at this
  have hFa : Loc ((r + k : ℕ) : ℕ∞) (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y))
      (g * (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG (one_GV (k := k) (r := r))
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * 1)) =
        fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y) := by
      funext x; simp only [Matrix.mul_one]
    rw [e] at this
    exact this _ hgS
  rw [rho_eq D p F]
  have h1 : qminorOp (Q.EH k r) a b u (fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))))) g =
      Formalism.FourierDecayAlt.P.JFxB.Lq D p (qminorOp (Q.EH k r) a b u (fun x =>
        F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) g) :=
    Formalism.FourierDecayAlt.P.CutMP.CapInv.post_qm (Formalism.FourierDecayAlt.P.JFxB.Lq D p) _ hG' a b u hg
  rw [h1]
  congr 1
  have h2 := qminor_right (Matrix.of p.2.2 * Matrix.of p.2.1) hSG a b u
    (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y)) g hgS hFa
  rw [jset_eq] at h2
  refine h2.trans (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_)))
  rw [qminor_left]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B RInvCov

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jDRInvFn_of (hA : RInvAlphaP) (hB : RInvBetaP) (hBL : RInvBetaLeftP) : JDRInvFn := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rhatOp k r D.z D.z' Y F)]
  show rhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rhatOp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleP (M := Wq →L[ℂ] Wp) (jSetR k r) (alP k r D.z') (rowsR k r)
    (fun J => beJ k r D.z g J)
    (fun J => beJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c i => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c (rowsR k r i)).det)
    (fun J d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix J d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r 0 Y) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun X => hA k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
    (fun d => by
      rw [hB k r D.z g _ hgG hSG d, hBL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS d])
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

theorem jDRInvFnM_of (hA : RInvAlphaM) (hAL : RInvAlphaLeftM) (hB : RInvBetaM) : JDRInvFnM := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rvhatOp k r D.z D.z' Y F)]
  show rvhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rvhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rvhatOp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleM (M := Wq →L[ℂ] Wp) (jSetR k r) (beM k r D.z') (colsV k r)
    (fun J => alJ k r D.z g J)
    (fun J => alJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c J => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c J).det)
    (fun t d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix (colsV k r t) d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r (Fin.last r) Y - 1) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun c => by
      rw [hA k r D.z g _ hgG hSG c, hAL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS c])
    (fun X => hB k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentiableAtOfPuncturedSmooth
section
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def V1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ (ℂ → E) where
  carrier := {f | ContDiffOn ℝ ∞ f {τ | τ ≠ 0}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change ContDiffOn ℝ ∞ (fun τ => c • f τ) _
    exact hf.const_smul c

theorem isOpen_ne_zero_complex : IsOpen {τ : ℂ | τ ≠ 0} := isOpen_ne

theorem differentiableAt_of_punctured_smooth {f : ℂ → E} (hf : f ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) : DifferentiableAt ℝ f τ :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_ne_zero_complex.mem_nhds hτ)

theorem contDiffOn_fderiv_punctured {f : ℂ → E} (hf : f ∈ V1 E) (v : ℂ) : ContDiffOn ℝ ∞ (fun τ => fderiv ℝ f τ v) {τ | τ ≠ 0} :=
  (hf.fderiv_of_isOpen isOpen_ne_zero_complex (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_wirtinger_dz {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dz f) {τ | τ ≠ 0} := by
  unfold PBP.dz
  exact ((contDiffOn_fderiv_punctured hf 1).sub ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem contDiffOn_wirtinger_dzbar {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dzb f) {τ | τ ≠ 0} := by
  unfold PBP.dzb
  exact ((contDiffOn_fderiv_punctured hf 1).add ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem dz_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (f + g) τ = PBP.dz f τ + PBP.dz g τ := by
  unfold PBP.dz
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add, smul_sub]
  abel

theorem dzb_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (f + g) τ = PBP.dzb f τ + PBP.dzb g τ := by
  unfold PBP.dzb
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

theorem dz_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (c • f) τ = c • PBP.dz f τ := by
  unfold PBP.dz
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

theorem dzb_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (c • f) τ = c • PBP.dzb f τ := by
  unfold PBP.dzb
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

def off0 (f : ℂ → E) : ℂ → E := fun τ => if τ = 0 then 0 else f τ

theorem off_zero_mem_punctured_smooth {f : ℂ → E} (hf : ContDiffOn ℝ ∞ f {τ | τ ≠ 0}) : off0 f ∈ V1 E :=
  hf.congr fun τ hτ => by simp [off0, show τ ≠ 0 from hτ]

theorem cd_id : ContDiffOn ℝ ∞ (fun τ : ℂ => τ) {τ | τ ≠ 0} := contDiffOn_id
theorem cd_conj : ContDiffOn ℝ ∞ (fun τ : ℂ => conj τ) {τ | τ ≠ 0} := Complex.conjCLE.contDiff.contDiffOn
theorem cd_inv : ContDiffOn ℝ ∞ (fun τ : ℂ => τ⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  exact (contDiffAt_inv ℂ (show τ ≠ 0 from hτ)).restrict_scalars ℝ |>.contDiffWithinAt
theorem cd_conjinv : ContDiffOn ℝ ∞ (fun τ : ℂ => (conj τ)⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fun τ : ℂ => conj τ) τ := Complex.conjCLE.contDiff.contDiffAt
  have h2 : conj τ ≠ 0 := by simpa using (show τ ≠ 0 from hτ)
  exact (((contDiffAt_inv ℂ h2).restrict_scalars ℝ).comp τ h1).contDiffWithinAt

def opP (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => τ • PBP.dz f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_id.smul (contDiffOn_wirtinger_dz f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dz_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dz_smul f.2 c hτ]
      simp only [smul_add, smul_comm τ c, smul_comm κ c]

def opPb (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => conj τ • PBP.dzb f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_conj.smul (contDiffOn_wirtinger_dzbar f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dzb_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dzb_smul f.2 c hτ]
      simp only [smul_add, smul_comm (conj τ) c, smul_comm κ c]

def opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : Module.End ℂ (V1 E) where
  toFun f := ⟨fun τ => m τ • f.1 τ, hm.smul f.2⟩
  map_add' f g := by ext τ; simp [smul_add]
  map_smul' c f := by ext τ; simp [smul_comm (m τ) c]

def site1 (κ : ℂ) : Wd.Site (Q.Pr (V1 E)) :=
  ⟨Q.mkP (opP κ) (-(opPb κ)), Q.mkP (opM (fun τ => τ) cd_id) (opM (fun τ => conj τ) cd_conj),
    Q.mkP (opM (fun τ => τ⁻¹) cd_inv) (opM (fun τ => (conj τ)⁻¹) cd_conjinv)⟩

def act1 {S : Type} [Fintype S] [DecidableEq S] (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) : Wd.Ix S → V1 E :=
  fun a => ∑ b, (M a b).1 (x b)

def oneBT {S : Type} [Fintype S] [DecidableEq S] (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    Wd.Ix S → V1 E :=
  act1 (Wd.bT (site1 κ) w) x

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OfFnSplit
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section helpers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mix_pushT (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (mk : List ℝ → List C.Letter) (P Q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) P Q =
      ∑ n : Fin K → Fin (d + 1), ((F7.thGrid grid n : ℝ) : ℂ) * KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) P Q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  simp only [apply_ite, Complex.ofReal_zero, zero_mul, ite_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]

end helpers

section lists

theorem ofFn_split {K : ℕ} (f : Fin K → ℝ) (ys₁ : List ℝ) (y : ℝ) (ys₂ : List ℝ)
    (h : List.ofFn f = ys₁ ++ y :: ys₂) :
    ∃ b₀ : Fin K, b₀.val = ys₁.length ∧ y = f b₀ ∧ ys₁.length + 1 + ys₂.length = K ∧
      ∀ y' ∈ ys₂, ∃ b' : Fin K, b₀ < b' ∧ y' = f b' := by
  have hlen : K = ys₁.length + 1 + ys₂.length := by
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_append, List.length_cons] at this
    omega
  have hb : ys₁.length < K := by omega
  refine ⟨⟨ys₁.length, hb⟩, rfl, ?_, hlen.symm, ?_⟩
  · have h1 : (List.ofFn f)[ys₁.length]'(by simp; omega) = (ys₁ ++ y :: ys₂)[ys₁.length]'(by simp) := by
      simp only [h]
    rw [List.getElem_ofFn, List.getElem_append_right (by omega)] at h1
    simp only [Nat.sub_self, List.getElem_cons_zero] at h1
    exact h1.symm
  · intro y' hy'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy'
    refine ⟨⟨ys₁.length + (i + 1), by omega⟩, by simp only [Fin.lt_def]; omega, ?_⟩
    have h1 : (List.ofFn f)[ys₁.length + (i + 1)]'(by simp; omega) =
        (ys₁ ++ y :: ys₂)[ys₁.length + (i + 1)]'(by simp; omega) := by simp only [h]
    rw [List.getElem_ofFn] at h1
    simp only [List.getElem_append, Nat.add_sub_cancel_left, List.getElem_cons_succ,
      show ¬ (ys₁.length + (i + 1) < ys₁.length) by omega, dite_false] at h1
    exact h1.symm

theorem rhyp_of {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ)
    (C : ℝ) : ∀ ys : List ℝ, (∀ ys₁ y ys₂, ys = ys₁ ++ y :: ys₂ →
      0 < (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re ∧
      (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re) → RHyp l0 a e ρ Pv C ys
  | [], _ => trivial
  | y :: ys, H => ⟨H [] y ys rfl, rhyp_of l0 a e ρ Pv C ys fun ys₁ y' ys₂ h => H (y :: ys₁) y' ys₂ (by rw [h]; rfl)⟩

end lists

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocBOf
section
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

def GermPartsC : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n v, GermRealisation.GermFibres (PBL.setC S p (cutSeq S p f χ n)) v ∧ GermRealisation.GermCont (PBL.setC S p (cutSeq S p f χ n)) v

theorem germLocB_of (hI : IntB) (hG : GermPartsC) : GermLocB := by
  intro Cb
  obtain ⟨c1, h1⟩ := hI Cb
  obtain ⟨c2, h2⟩ := hG Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hI' := h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v
  obtain ⟨hF, hC⟩ := h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v
  exact GermRealisation.germLoc_of_fibres hI' hB.1 hB.2.1 hF hC

end

end Formalism.FourierDecayAlt.P.PBASM
end

