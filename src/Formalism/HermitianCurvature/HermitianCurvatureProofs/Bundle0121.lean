module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0116
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

def Vp (P : M.Par) (Y : ℂ) (i : ℕ) : Wd.M2 (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => Wd.Ts (MA.siteA P (MA.DQ P) l) Y).prod

theorem Vp_zero (P : M.Par) (Y : ℂ) : Vp P Y 0 = 1 := by
  simp [Vp]

theorem Vp_succ (P : M.Par) (Y : ℂ) (i : ℕ) (h : i < P.r) :
    Vp P Y (i + 1) = Wd.Ts (MA.siteA P (MA.DQ P) ⟨i, h⟩) Y * Vp P Y i := by
  simp [Vp, List.take_add_one, h]

theorem sitesCommonSpace_v0_eq_Vp (P : M.Par) (Y : ℂ) : Wd.v0 (MA.sites P (MA.DQ P)) Y = fun b => Vp P Y P.r b 0 := by
  funext b
  simp [Wd.v0, MA.sites, Vp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le, Function.comp_def]

theorem Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) * V 0 0 + -σ.c * V 1 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 1 0 = σ.ci * V 0 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

section ind

theorem actA_p (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).p f = fun ρ => MA.eulerQ (TT := P.TT) (M.vc l) (f ρ) :=
  actA_sc P _ f

theorem actA_c (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).c f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ :=
  actA_sc P _ f

theorem actA_ci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).ci f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc l)) * f ρ :=
  actA_sc P _ f

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Y : ℂ) • (Q.vAB P.r (Y : ℂ) i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 0) Φ =
        (Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc ((Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_vector_transition_holds : GVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
  have h := vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases b
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadVectorOfParts
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

def Exh : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V F₂ (h ++ [(1, ζ)])) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

def HeadVecOfParts : Prop := HighestUnipotentIntegral → Exh → HeadVec

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_vector_of_parts : PBI.HeadVecOfParts := by
  intro hU5 hExh Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF h hh Φ hΦ e
  obtain ⟨F₂, hF₂, hV, hJ⟩ := hExh Wp Wq P p F w X μ L st Cb hD hdd hF hcut e h hh
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hr : P.r - P.r = 0 := by omega
  have hGx : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hGx
    nlinarith [mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos]
  have hZ : Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ = D.ptMatN [(1, ζ)] (P.r - P.r + 1) := by
    ext a b
    have ha : a = Fin.last _ := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
    have hb : b = Fin.last _ := Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
    subst ha hb
    rw [← PBI.zetaL_eq_zhat, hζ]
    simp [D.ptMatN, D.ptEntry, hr]
  have hγGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ := by
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx
  show p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = _
  rw [hV, hU5 Wp Wq P p F₂ h ζ hh ν'r m₀r hF₂ hζ0 hLev.1 hLev.2.1,
    PBM.vector_level_zero_eq_jacquet hr (p.T.bs P.r) ν'r m₀r hLev.2.2 _ ζ (by linarith) γ₀ hγG hZ hγF]
  exact hJ Φ hΦ x.1 γ₀ hγG hγGG

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisConjInt
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem phi_cont (ρ : ℕ) : Continuous (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  have e : (Dx2.MN.phi (k := k) (ρ := ρ)) = fun x => Dx2.MN.phi x := rfl
  rw [e]
  simp only [Dx2.MN.phi]
  fun_prop

def heisT (ρ : ℕ) (x : B2.HPar k ρ) : Mt k (1 + ρ) := Matrix.of.symm (B2.heis0 k ρ x)

theorem heis_cont (ρ : ℕ) : Continuous (heisT (k := k) ρ) := B2x5.continuous_heis0 k ρ

theorem heis_emb (ρ : ℕ) : MeasurableEmbedding (heisT (k := k) ρ) :=
  (heis_cont ρ).measurableEmbedding (Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed k ρ).1

def phiE (ρ : ℕ) : U.RC k 1 ρ ≃ᵐ B2.HPar k ρ where
  toFun := Dx2.MN.phi
  invFun p := (fun i _ => p.1 i, (fun _ => 0, fun _ => p.2))
  left_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Dx2.MN.phi, Prod.mk.injEq]
    refine ⟨?_, Subsingleton.elim _ _, ?_⟩
    · funext i a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
    · funext a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
  right_inv p := by simp [Dx2.MN.phi]
  measurable_toFun := (phi_cont ρ).measurable
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst).prodMk
      (continuous_const.prodMk (continuous_pi fun _ => continuous_snd))

theorem phi_emb (ρ : ℕ) : MeasurableEmbedding (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  exact (phiE ρ).measurableEmbedding

theorem heis_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : B.Mat k (1 + ρ) → B.Mat k (1 + ρ) → E) :
    ∫ p : Mt k (1 + ρ) × Mt k (1 + ρ), Φ (Matrix.of p.1) (Matrix.of p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, Φ (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
        ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
  have e0 : B2.μHeis k ρ = (volume : Measure (B2.HPar k ρ)).map (heisT ρ) := rfl
  have e1 : (B2.μHeis k ρ).prod (B2.μHeis k ρ) =
      ((volume : Measure (B2.HPar k ρ)).prod volume).map (Prod.map (heisT (k := k) ρ) (heisT ρ)) := by
    rw [e0, Measure.map_prod_map _ _ (heis_emb ρ).measurable (heis_emb ρ).measurable]
  rw [e1, ((heis_emb ρ).prodMap (heis_emb ρ)).integral_map]
  have hmp : MeasurePreserving (Prod.map (Dx2.MN.phi (k := k) (ρ := ρ)) (Dx2.MN.phi (k := k) (ρ := ρ)))
      ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) ((volume : Measure (B2.HPar k ρ)).prod volume) := by
    have := (Dx2.MN.phi_mp (k := k) (ρ := ρ)).prod (Dx2.MN.phi_mp (k := k) (ρ := ρ))
    simpa [U.muRC] using this
  rw [← hmp.integral_comp ((phi_emb ρ).prodMap (phi_emb ρ))]
  apply integral_congr_ae
  filter_upwards with xx
  rw [Dx2.MN.rn_heis, Dx2.MN.rn_heis]
  rfl

def conjE {r : ℕ} (b : B.Mat k r) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM b
  invFun := conjM b⁻¹
  left_inv x := by
    show b⁻¹ * (b * Matrix.of x * b⁻¹) * b⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hb, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one]
  right_inv x := by
    show b * (b⁻¹ * Matrix.of x * b⁻¹⁻¹) * b⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hb, Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]
  measurable_toFun := B2x5.measurable_conjM b
  measurable_invFun := B2x5.measurable_conjM b⁻¹

theorem heis_conj_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g g' : B.Mat k ρ}
    (hg : g ∈ B.GV k ρ) (hg' : g' ∈ B.GV k ρ) (Φ : Mt k (1 + ρ) × Mt k (1 + ρ) → E) :
    ∫ p, Φ (conjM ((ιLev k 1 ρ g)⁻¹) p.1, conjM ((ιLev k 1 ρ g')⁻¹) p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ p, Φ p ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
  have := sf_heis (k := k) ρ
  have hu : IsUnit ((ιLev k 1 ρ g)⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg))
  have hu' : IsUnit ((ιLev k 1 ρ g')⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg'))
  have m1 : MeasurePreserving (conjE _ hu) (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu).measurable, heis_meas_conj_inv ρ hg⟩
  have m2 : MeasurePreserving (conjE _ hu') (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu').measurable, heis_meas_conj_inv ρ hg'⟩
  have := (m1.prod m2).integral_comp ((conjE _ hu).measurableEmbedding.prodMap (conjE _ hu').measurableEmbedding) Φ
  exact this

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of p.2)) •
    (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹) ∂(Bs.μW'.prod Bs.μN)

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def pairLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

variable {μ : Measure (Mt k r)} {i : Fin (r + 1)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem pairLev_swap (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairLev μ i Ψ Φ c = conj (pairLev μ i Φ Ψ c) := by
  unfold pairLev
  rw [← integral_conj]
  congr 1
  funext c'
  rw [pairAt_swap, map_mul, Complex.conj_ofReal]

theorem pairLev_smul_left (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i (a • Φ) Ψ c = a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_left]
  ring

theorem pairLev_zero_left (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairLev μ i 0 Ψ c = 0 := by
  unfold pairLev
  have h0 : ∀ c', pairAt μ (0 : RadSp k r z z' π π') Ψ c' = 0 := fun c' => by
    have := pairAt_smul_left μ (0 : RadSp k r z z' π π') Ψ c' 0
    rwa [zero_smul, zero_mul] at this
  simp [h0]

theorem act_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := U.sum_mem fun b _ => (hM a b).1 _ (hx b)

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangularFactorMiddleRow
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

section N1

variable {k r : ℕ}

theorem tau_val (p : Fin (2 * r + k + 1)) :
    (tau k r p).val = if p.val < r ∨ r + k < p.val then 2 * r + k - p.val else p.val := rfl

theorem sgn_one (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : WeylGroupFacts.sgn k r p = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg h]

theorem mulVec_hpk (v : Fin (2 * r + k + 1) → ℂ) (l : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) l = WeylGroupFacts.sgn k r l * v (tau k r l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tau k r l)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_row, if_neg hm, zero_mul]
  · simp

theorem herm_expand (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ l, star (w l) * (WeylGroupFacts.sgn k r l * v (tau k r l)) := by
  unfold herm; simp only [dotProduct, mulVec_hpk, Pi.star_apply]





end N1

section MajorantSquareBound

variable {k r : ℕ}

end MajorantSquareBound

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

