module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0255
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0060
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0256
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppOrbit
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem exists_orbit (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g0 : B.Mat k n) (h : PBQ.pbF Bj B0 e H g0 ≠ 0) :
    ∃ x, PBQ.GoodP Bj x ∧ ∃ ξ : Mt k n × Mt k n, PBG.InR B0 ξ ∧
      H (D.castM e (PBQ.sP Bj x) * g0 * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  unfold PBQ.pbF
  rw [← integral_zero (PBQ.XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  show PBQ.pbI Bj B0 e H g0 x = 0
  unfold PBQ.pbI
  have hK : PBG.Kr B0 H (D.castM e (PBQ.sP Bj x) * g0) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    rw [hno x hx ξ hξ, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

theorem norm_entry_le_gN (g : B.Mat k n) (i j : Fin (2 * n + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem orbit_gen (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hz : B0.z = D.castV e (liftVec k p ρ Bj.z))
    (Z : Matrix (Fin p) (Fin p) ℂ) (μ : B.Mat k ρ) (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k ρ)
    (x : PBQ.XP k p ρ) (hx : PBQ.GoodP Bj x) (ξ : Mt k n × Mt k n) (hξ : PBG.InR B0 ξ) (g : B.Mat k n)
    (hg : g = D.castM e (PBQ.sP Bj x) * D.castM e (U.mMap k p ρ Z μ) * Matrix.of ξ.2 * Matrix.of ξ.1) :
    g ∈ B.GV k n ∧ (∃ u : Matrix (Fin p) (Fin p) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ ∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧
      (∀ l, Dmin k n B0.z B0.z' g l = Dmin k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) l) ∧
      Gf k n B0.z B0.z' g = Gf k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hg ⊢
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  have hm : U.mMap k p ρ Z μ ∈ B.GV k (p + ρ) := (Formalism.FourierDecayAlt.P.slice_membership k p ρ).1 Z μ hZ hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (PartialBesselProperness.sP_GV Bj x) hm) hξ.2.1)
      hξ.1.1
  · refine ⟨G.upper (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩),
      LeftFubiniLemmas.upper_isUpUni _, fun a b => ?_⟩
    have hZh : U.Zh k p ρ g = Z * G.upper (fun q : G.UT p =>
        (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
      have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice k p ρ 0 0 Z μ
      rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
      rw [hg, PBQ.zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, PBQ.zh_sP_mul, e0,
        PBQ.nblk_upper _ hξ.2]
    rw [← hZh]
    exact norm_entry_le_gN g _ _
  · obtain ⟨h, hh, m, hmN, hs⟩ := PartialBesselProperness.leftFactor_mem Bj x
    rw [← hz] at hh
    have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
    have hmu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hmN.1
    set pp : B.SS k (p + ρ) := ((Matrix.of.symm h⁻¹, Matrix.of.symm m⁻¹), ξ) with hpp
    have hin : B0.inSS pp := ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN, hξ.1, hξ.2⟩
    have hsg : B.sgs pp (U.mMap k p ρ Z μ) = g := by
      rw [hg, hs]
      simp only [B.sgs, hpp]
      change (h⁻¹)⁻¹ * (m⁻¹)⁻¹ * U.mMap k p ρ Z μ * Matrix.of ξ.2 * Matrix.of ξ.1 = _
      rw [Matrix.nonsing_inv_nonsing_inv _ hhu, Matrix.nonsing_inv_nonsing_inv _ hmu]
    refine ⟨fun l => ?_, ?_⟩
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs B0 hin _ l
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs B0 hin _

end gen

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lowV_top {P : M.Par} (p : KB.Pl P Wp Wq) (e : P.r + (P.r - P.r) = P.r) :
    U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z) = (p.T.bs P.r).z ∧
      U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z') = (p.T.bs P.r).z' := by
  unfold D.LevTower.base
  rw [← p.T.z_lev P.r le_rfl, ← p.T.z'_lev P.r le_rfl, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩

theorem orbit_point {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Z : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)) (hZ : Z.det ≠ 0)
    (hμ : μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)) (h : CutEX.pbTop p G Z μ ≠ 0) :
    ∃ g ∈ B.GV P.k P.r, G g ≠ 0 ∧ ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧ Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ = Z.det ∧
      Gf P.k P.r p.T.base.z p.T.base.z' g =
        Complex.normSq Z.det * Gf P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' μ := by
  have e : P.r + (P.r - P.r) = P.r := by omega
  have hμGV : μ ∈ B.GV P.k (P.r - P.r) := hμ.1
  unfold CutEX.pbTop PBQ.pbT at h
  obtain ⟨x, hx, ξ, hξ, hG⟩ := exists_orbit _ _ _ _ _ h
  have hz : p.T.base.z = D.castV e (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) := (p.T.z_lev P.r le_rfl).symm
  obtain ⟨hGV, ⟨u, hu, hb⟩, hD, hGf⟩ := orbit_gen (p.T.bs P.r) p.T.base e hz Z μ hZ hμGV x hx ξ hξ _ rfl
  refine ⟨_, hGV, hG, u, hu, hb, ?_, ?_⟩
  · rw [hD]
    rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM e _ _ _ P.r (by omega) (by omega), Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r)]
    have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice P.k P.r (P.r - P.r) 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
    unfold U.DjU
    rw [e0]
  · rw [hGf, gf_castM e]
    have hz0 := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
    have hz0' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
    have hG0 := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r) _ _ hz0 hz0' 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG0
    obtain ⟨hl1, hl2⟩ := lowV_top p e
    rw [hG0, hl1, hl2]

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

theorem zxH_rfl (h : C.LPt) (v : XH h) : zxH h (D.ptSize h) rfl v = LeftFubiniLemmas.lhOf (D.ptPerm h) v *
    U.hMat (D.ptPerm h) (D.ptDiag h) := by
  first
  | rfl
  | simp [zxH]

theorem supp_of (hW : PartialBesselProperness.PbWords) (hP : ProperDomP) : Supp := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ K _ hK0
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  have hhh : D.IsLocPt h (D.ptSize h) := ⟨hh1, rfl⟩
  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ i, D.ptDiag h i ≠ 0 := ptDiag_ne hhh

  have hR1 : ∀ ew : Wd.Ix (Fin w.length), ∃ R1 : ℝ, ∀ v : XH h, R1 < ‖v‖ → ∀ g ∈ B.GV P.k P.r,
      U.Zh P.k (D.ptSize h) (P.r - D.ptSize h) (D.castM e.symm g) =
        LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) →
      pbF (p.T.bs (D.ptSize h)) p.T.base e
        (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) (by omega) w ew) g = 0 := by
    intro ew
    refine pb_head_support (p.T.bs (D.ptSize h)) p.T.base e (D.ptPerm h) (D.ptDiag h) hd _ Cs hCc ?_
    intro g hg hgC
    by_contra hne
    exact hgC (Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) (by omega) w ew g hg hne)
  choose R1 hR1 using hR1
  refine ⟨⋃ ew, Metric.closedBall (0 : XH h) (R1 ew), isCompact_iUnion fun ew => isCompact_closedBall _ _,
    fun v hv τ hτK ew => ?_⟩
  have hτ : τ ≠ 0 := hK0 hτK
  have hvR : R1 ew < ‖v‖ := by
    by_contra hle
    have hle : ‖v‖ ≤ R1 ew := not_lt.mp hle
    exact hv (Set.mem_iUnion.2 ⟨ew, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩)
  have hpt := pts Wp Wq P p (D.ptSize h) hj h hhh γ hγ hΩ v
  have hyD := hpt.2 τ hτ
  have hyG := x0_GV hj hpt.1 hτ hγ
  have hz : p.T.base.z = D.castV e (liftVec P.k (D.ptSize h) (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z) :=
    (p.T.z_lev (D.ptSize h) (by omega)).symm
  have hPW := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e hz (D.ptSize h)
    (by omega) F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ (show D.ptSize h ≤ D.ptSize h from le_rfl) (show D.ptSize h ≤ P.r by omega))
    (hP Wp Wq P p (D.ptSize h) (by omega) Cs hCc) w ew _ hyD hyG
  unfold phf
  unfold pbT
  rw [hPW]
  refine hR1 ew v hvR _ hyG ?_
  rw [leading_block_of_base_point hj _ τ γ e.symm, zxH_rfl]

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem residue_operator_holds : JDOpR := jDOpR_of_vStepB mirror_residue_second_move

theorem hat_quadratic_operator_holds : JDHatOpQQ :=
  jDHatOpQQ_of_opA_opR_residue_splitting (jDOpA_of_parts polynomial_decay_admissible capelli_minors_holds) residue_operator_holds residue_splitting_holds
    mirror_residue_splitting_holds hat_lagrange_decay_holds hat_nodes_decay_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section WaveJc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJc (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    HasCompactSupport G ∧ ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJc : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJc P z z' π π' D l Ψ}

end WaveJc

def JSliceGenC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → SliceGood X μ l c Ψ

def JSSob2 : Prop :=
  ∀ (t0 : ℂ) (δ : ℝ), 0 < δ → ∃ K : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f fx fy fxy : ℂ → E),
    (∀ t ∈ Metric.closedBall t0 (2 * δ),
      HasFDerivAt f (Complex.reCLM.smulRight (fx t) + Complex.imCLM.smulRight (fy t)) t) →
    (∀ t ∈ Metric.closedBall t0 (2 * δ), ∃ fyy : E,
      HasFDerivAt fy (Complex.reCLM.smulRight (fxy t) + Complex.imCLM.smulRight fyy) t) →
    ContinuousOn fx (Metric.closedBall t0 (2 * δ)) → ContinuousOn fxy (Metric.closedBall t0 (2 * δ)) →
    ∀ t ∈ Metric.ball t0 δ, ‖f t‖ ^ 2 ≤
      K * ∫ s in Metric.closedBall t0 (2 * δ), (‖f s‖ ^ 2 + ‖fx s‖ ^ 2 + ‖fy s‖ ^ 2 + ‖fxy s‖ ^ 2)

def JSMeas : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (c : Fin r → ℂ)
    (Φ Ψ : RadSp k r z z' π π'),
    Measurable (fun q : (ℂ × Cf r l.succ) × Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)))

def SpectralL2Locality : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → ∀ (js : List (Fin 6)) (t0 : ℂ),
      t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
        LevelSquareIntegrable μ l.succ (wOp X l js Ψ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ M

def JSWordNF : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π')), multiplicationOperator Wv (fun c _ => fsv s (c l)) →
    ∀ js : List (Fin 6), ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
      (∀ i, ContinuousOn (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
      ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
        (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
          ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

def JSRadLoc : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    HasCompactSupport G → ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ js : List (Fin 6), (∀ j ∈ js, j = 0 ∨ j = 3) → ∀ t0 : ℂ, t0 ≠ 0 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
        LevelSquareIntegrable μ l.succ (wOp X l js Φ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Φ) (wOp X l js Φ) c t‖ ≤ M

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBdd
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem norm_fsv_rd (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have h : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [h, Real.exp_zero]

theorem hsVec_smul_rd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem radial_boundedness : RDBdd := by
  intro k r Wp Wq _ _ _ _ _ _ D F H _ _
  refine ⟨∫ q, ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖, fun s => ?_⟩
  have h1 : 1 < r + 2 := by omega
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  have hJ : ∀ g, B.JF D (wvG D.z D.z' s F) g = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • B.JF D F g := fun g =>
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv F g
  unfold B.beta betaBig
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)))
  show ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D (wvG D.z D.z' s F) (B.gq D q)))‖ = _
  rw [hJ, hsVec_smul_rd, inner_smul_right]
  simp only [norm_mul, norm_fsv_rd, one_mul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBeta
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_beta_identity : RDBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D μ hμ
  obtain ⟨C1, hC1, hpair⟩ := Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ
  refine ⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ)
    (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)
  have hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H := by simp
  rw [hsum] at h
  rw [← h]
  unfold LocFacts₂ P5.form
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c' := by
    funext l
    simp only [glue]
    have h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) := Nat.zero_le _
    rw [dite_eq_left h0, dite_eq_left h0]
  simp only [hg, Finset.univ_unique, Finset.sum_singleton]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOutJ
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem wave_outgoing_orbital : WaveOutJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hdat hl0 hle hz hz' hπ hπ' l hl u v hu hv c hc s Wv hW
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hdat.2.1
  haveI := sfinite_of_isHaarOn _ μ hμ

  have hl2u := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hu b)
  have hl2v := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hv b)
  have hW1 : ∀ c' : Fin P.r → ℂ, ‖fsv s (c' l)‖ = 1 := fun c' => HerC.norm_fsv s (c' l)
  have hl' : l.castSucc = 0 := by
    ext
    simp [hl]
  have keyu : ∀ b, LevelSquareIntegrable μ l.castSucc (u b) c := by
    intro b
    rw [hl']
    exact (hl2u b).2 c
  have keyv : ∀ b, LevelSquareIntegrable μ l.castSucc (v b) c := by
    intro b
    rw [hl']
    exact (hl2v b).2 c

  have keyW : ∀ b, LevelSquareIntegrable μ l.castSucc (Wv (u b)) c := by
    intro b
    have h := keyu b
    unfold LevelSquareIntegrable at h ⊢
    simp only [waveOut_pairAt_self μ hW hW1]
    exact h
  have hd := dens_int μ hμ l (fun b => Wv (u b)) v (fun b => mul_lc hW _ (hl2u b).1)
    (fun b => (hl2v b).1) c keyW keyv
  rw [← hd.2]
  simp_rw [waveOut_dens μ l s hW u v c]

end Formalism.FourierDecayAlt.P.CutSE
end
end

