module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0231
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0228
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCB
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0229

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundOnEarlierRegion
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_earlier_region : OnOldBound := by
  intro k ρ Wp Wq _ _ _ _ Bs w m
  obtain ⟨K, hK, hM⟩ := mDiff_ccle Bs w m
  refine ⟨K, hK, fun σ hσ ys => ?_⟩
  induction ys with
  | nil => intro A x c hx e; exact hM σ hσ A x c hx e
  | cons y ys ih =>
    intro A x c hx e
    exact ih A (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) c (fun e' => hx _)
      (fun a => e a.succ)

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem smooth_forms_stability_holds : JAFFStable := FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLJCommC
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_sa (k r o : ℕ) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (6 * (r : ℝ) * (o : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : 0 ≤ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) := by positivity
  have h2 : 0 ≤ (r : ℝ) * (6 * (r : ℝ) + 1) := by positivity
  refine ⟨by linarith, ?_⟩
  nlinarith

theorem sAJCommC_of_thetaJ (hT : LT.ThetaJ) : SAJCommC := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ hΘ F hFs hFc _hFO U X hU hX hagree y hy hyU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl

  have hAg := QO.agree_qOf (T v).base X F U hX
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    QO.qOf (T v).base.z (T v).base.z' ⁻¹' U with hVdef
  have hVo : IsOpen V := QO.isOpen_qOf _ _ hU
  have hJV : ∀ g ∈ V, g ∈ B.GV S.G.k S.G.r → X g = B.JF (T v).base F g := fun g hg hgG =>
    hAg g ⟨hgG, hg.1⟩ hg.2
  have hq : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hy.1, by rw [← hTT]; exact hy.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base y ∈ V := ⟨hg0.2, by
    show QO.qOf (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ U
    rw [QO.qOf_gq (T v).base hq]; exact hyU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') X :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hX.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base y ∈ UU := ⟨hg0, hg0V⟩

  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs hFc
    (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) +
      (S.G.r : ℝ) * (4 * (S.G.r : ℝ) + 2 * (S.G.k : ℝ)) * (6 * (S.G.r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU
    (thrW_sa S.G.k S.G.r (B.opOrder Θ)) hΘ.1 hΘ.2 hFs hIn hUU hCkF
  have hg0G : B.gq (T v).base y ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun g => Tm.coefAdj g (X g)) (f' := fun g => Tm.coefAdj g (B.JF (T v).base F g))
      (fun g hg hgG => by simp only [hJV g hg hgG]) _ hg0V hg0G]

theorem sAJCommC_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : SAJCommC :=
  sAJCommC_of_thetaJ (LT.thetaJ_of_adjComm hAC)

theorem self_adjoint_commutation_compact : SAJCommC :=
  sAJCommC_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def eP (k r : ℕ) (z' ν v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν

theorem eP_add (z' ν x y : Fin (2 * r + k + 1) → ℂ) : eP k r z' ν (x + y) = eP k r z' ν x + eP k r z' ν y := by
  unfold eP
  rw [PRhoCut.FL.prWv_add, DU.hadd_l, add_smul]
  abel

theorem eP_smul (z' ν : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    eP k r z' ν (c • x) = c • eP k r z' ν x := by
  unfold eP
  rw [PRhoCut.FL.prWv_smul, DU.hsmul_l, smul_sub, smul_smul]

def ioLin (k r : ℕ) (μ : B.Mat k r) (z' ν : Fin (2 * r + k + 1) → ℂ) :
    (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) where
  toFun v := μ *ᵥ eP k r z' ν v
  map_add' x y := by rw [eP_add, Matrix.mulVec_add]
  map_smul' c x := by rw [eP_smul, Matrix.mulVec_smul]; rfl

theorem ioMulVec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  have e : SSn.io0 k r z z' μsec ζ =
      LinearMap.toMatrix' (ioLin k r (NF.muZ k r μsec ζ) z' (SSn.nu0' k r z z' μsec ζ)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JDAToda

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem omB_eq {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Gauge.OmB Bs = Q.OmPlus k r Bs.z Bs.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, show Dmin k r Bs.z Bs.z' g ⟨0, by omega⟩ = 1 by unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by show a.val + 1 ≤ r; have := a.isLt; omega)⟩

theorem gg_pos {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hcg : wCell k r (Fin.last r) c * g ∈ Gauge.OmB Bs) :
    0 < GGl k r Bs.z Bs.z' g := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hmin := big_cell_minors_holds k r Bs.z Bs.z' c μ Bs.z_mem Bs.z'_mem
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ Bs.z') Bs.z = zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r Bs.z Bs.z' (bigCell k r c μ) ⟨r, by omega⟩ = ∏ a, c a := by
    have h := hmin.1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    simp
  have hP0 : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r Bs.z Bs.z' (bigCell k r c μ) (Fin.last (r + 1)) =
      (∏ a, c a) * zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    unfold Formalism.QuantumDeterminants.zeta at hzeta
    rw [hr] at hzeta
    rw [← hzeta, mul_div_cancel₀ _ hP0]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r c μ) =
      Complex.normSq (∏ a, c a) * GGl k r Bs.z Bs.z' (B2.embWb k r μ) := by
    unfold Gf GGl
    rw [hlast, hr, Complex.normSq_mul]
    ring
  have h1 := hcg.1
  rw [e, hGf] at h1
  exact pos_of_mul_pos_right h1 (Complex.normSq_nonneg _)

theorem minorCell_of {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hf : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') J) (hLf : LeftEq k r Bs.z 0 (OmPlus k r Bs.z Bs.z') J)
    (hRf : RightEq k r Bs.z' 0 (OmPlus k r Bs.z Bs.z') J) (y : ℂ) (x : (Fin r → ℂ) × Mx k r)
    (hx : x ∈ DomR k r Bs.z Bs.z') :
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 := by
  have hRR := Formalism.FourierDecayAlt.P.right_rule_derivative
  have hLR := Formalism.FourierDecayAlt.P.left_rule_cell
  have hTC := Formalism.FourierDecayAlt.P.torus_cell
  have hGP := Formalism.FourierDecayAlt.P.gauge_positivity
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl
  have vAB_loc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
      (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
      (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
    intro i
    induction i with
    | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
    | succ i ih =>
      intro f₁ f₂ h c hc
      have hi' := ih f₁ f₂ h
      by_cases hi : i < r
      · simp only [Q.vAB, dif_pos hi]
        refine ⟨?_, ?_⟩
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
          have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
            filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc'
            exact (hi' c' hc').1
          simp only [pOp, wirt, if_pos hc, hev.fderiv_eq]
          rw [(hi' c hc).1, (hi' c hc).2]
        · simp only [ciOp]
          rw [(hi' c hc).1]
      · simp only [Q.vAB, dif_neg hi]
        exact hi' c hc
  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    refine (vAB_loc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1
  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D J) J (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

theorem uC_zero (k r : ℕ) (y : ℂ) : Q.uC k r 0 y = y + ((2 * r + k : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.CutMP.JDAToda

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jda_capelli_toda_proof : JDACapToda := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvFinal
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_function_positive_holds : JDRInvFn :=
  jDRInvFn_of inverse_alpha_positive_holds inverse_beta_positive_holds inverse_beta_left_positive

theorem inverse_function_minus_holds : JDRInvFnM :=
  jDRInvFnM_of inverse_alpha_minus_holds inverse_alpha_left_minus inverse_beta_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJ
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

def mLev (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (τ : ℂ) (γ : B.Mat P.k (P.r - (j + 1))) : B.Mat P.k (P.r - j) :=
  D.castM (by omega : 1 + (P.r - (j + 1)) = P.r - j) (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ)

def kapJ (P : M.Par) (j : ℕ) : ℂ := ((P.r - j : ℕ) : ℂ) + (P.k : ℂ) / 2

def HeadJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        (oneBT (kapJ P j) (D.positionted w) φ e).1 t

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingLoweringRelations
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem raising_lowering_relations : KrAA := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  exact (PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne)) r le_rfl u 0 hx).1

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

namespace Formalism.FourierDecayAlt.P

theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
end
end

