module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiExThetaGeneral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Outright
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.KerSp

theorem locSp_latK_isPt : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  intro D i hi T bad lev p G A a hco hS hI hB hT c g x hx v hTv
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hdual := GlobalTheory.smul_dualSet_latAd_mem D.sp (gramN D i hi) hco T lev.Lb hT hLb lev.Lb_dual x.1 x.2
  have hLA : LatAdLoc A lev.Lb := GlobalTheory.TwV.latAdLoc_of A lev.Lb hS hI lev.Lb_fin lev.Lb_span
  unfold Formalism.MainNotions.G.KAat.latK Formalism.L2.PairingIndexBounds.F.toStd
  rw [GlobalTheory.TwV.locSp_map, GlobalTheory.TwV.CompSp.locSp_compan_eq D.sp (G.P.W v) (G.P.Qq v) (A.iw v) (gramN D i hi) a T _ hTv hdual,
    GlobalTheory.TwV.SpanPt.locSp_latAd_isPt A lev.Lb hLA hB c g x.1 hx v, GlobalTheory.TwV.SpanPt.colSpan_map]
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rfl

end GlobalTheory.TwV.KerSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTuple
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000

theorem smulLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {a N : ℕ} (hr : a = N) (σ : E →+* E) (Jm : Matrix (Fin N) (Fin N) E)
    (g : GL (Fin N) E) (A A' : Submodule (𝓞 E) (Fin a → E)) (B B' : Submodule (𝓞 E) (Fin N → E)) (hA : HEq A B) (hA' : HEq A' B')
    (hB : B' = SDLat.smulLat (eMat rfl σ Jm g) B) : A' = SDLat.smulLat (eMat hr σ Jm g) A := by
  subst hr
  cases eq_of_heq hA
  cases eq_of_heq hA'
  exact hB

theorem kerN_smul : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLat hMove
  have hLat' : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLat
  have hch : J.chart std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) = J.chart std j hj.le (c, La) :=
    _root_.GlobalTheory.TwV.Xc.chart_eq_of_comp S hD hS j hj.le c _ _ hLat' hLat
  have h1 := (hD j hj.le (c, La) hLat).2.2.1
  have h2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hLat').2.2.1
  obtain ⟨hg, hpt, -, -⟩ := hMove
  rw [hch, hpt] at h2
  exact smulLat_of_heq hr _ _ g _ _ _ _ h1 h2 (latK_rat_mul_lev D _ _ _ _ _ _ _ _ κ g hg)

end GlobalTheory.TwV.Xc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLawAndFixedCoordinateStabiliserLaw
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem site_law_xiIn : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pair → S.Pos → S.Move → S.Away → S.Law ∧
    Lt.LawInLt (sysS H X std) S.hfin S.E S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT ∧
    AdmLoc.XiIn (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPair hPos hMove hAway
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.TieBase.base_data t
  obtain ⟨hcl, hSS⟩ := GlobalTheory.BadPrimes.lev_pos_and_noConj J.A J.dtU J.a J.pins J.tie
  have hmm : (sysS H X std).mm = D.R.m := (DelB.sysS_ranks S).1
  have hLaw : S.Law :=
    GlobalTheory.TwU.LawAll.kapLawLt_frecG D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
      (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
      (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair hPos hMove
  refine ⟨hLaw, ?_, ?_⟩
  · intro j hj c L0 La' ε hrep hL' hε
    letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    exact GlobalTheory.TwU.KapLawLt.stab (h := hLaw) (hj := hj) c L0 La' ε (repOf_lat _ S.hfin j (c, L0) hrep) hL' hε
  · intro v j hj
    have hRB := GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt (D.what₂.places.resChar w) (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau
      (hT.gat_pos u w hg)
      (Formalism.L2.PairingIndexBounds.F.FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT)) hLaw
    exact hRB.2 v j hj
      (GlobalTheory.XiGen.xiEx_theta_general D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq
        (Formalism.L2.PairingIndexBounds.Rec.model_at_split_places_holds D) (Formalism.L2.PairingIndexBounds.Rec.split_place_moves_compose D) (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
        (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair v j hj (hAway v j (hmm ▸ hj)))

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeights
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem liftWt_of_lt (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) (r : ℕ) (hr : r < m + j * (t + 1) + 1) (h : r < m + 1) :
    liftWt t m lam w j ⟨r, hr⟩ = lam ⟨r, h⟩ := by
  simp [liftWt, h]

theorem liftWt_blk (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j b : ℕ) (hr : m + 1 + b * (t + 1) < m + j * (t + 1) + 1) :
    liftWt t m lam w j ⟨m + 1 + b * (t + 1), hr⟩ = -w (b + 1) := by
  have hd : b * (t + 1) / (t + 1) = b := Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [liftWt]
  rw [dite_eq_right (show ¬ (m + 1 + b * (t + 1) < m + 1) by omega)]
  simp only [Nat.add_sub_cancel_left, hd]


set_option maxHeartbeats 1000000 in
theorem wtOK_sites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → WtOK (sysS H X std) D (hT.gat_pos u w hg) u μ j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj ⟨a⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hw0 := ((H.core j hj1) (((I.at' j hj1).st.eC.symm a).1)).wt
  have hrk := ((I.at' j hj1).st.loc (((I.at' j hj1).st.eC.symm a).1)).rk
  unfold WtTie at hw0
  rw [J.pos j hj1] at hw0
  have ht : (sysS H X std).t = D.R.t := X.fl_t
  have hk : (sysS H X std).G.P.m + 1 = D.R.k := by
    have := (lev0At J.Gd u w hg).A.rk
    simpa [Ranks.N] using this
  set pos := hT.gat_pos u w hg with hpos
  have hA : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (r : ℕ) (hr : r < (sysS H X std).G.P.m + 1),
      (((sysS H X std).G.P.lam0 v s ⟨r, hr⟩ : ℤ) : ℚ) = hcToWeightQ (D.hcW u (pos ⟨v, s⟩)).u ⟨r, by omega⟩ := by
    intro v s r hr
    have hr' : r < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by omega
    have h1 := hw0 v s ⟨r, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨r, hr'⟩ = (sysS H X std).G.P.lam0 v s ⟨r, hr⟩ :=
      liftWt_of_lt (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) r hr' hr
    rw [h3] at h1
    rw [h1]
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨r, hr'⟩)
    rw [dite_eq_left (show ((finCongr hrk) ⟨r, hr'⟩ : ℕ) < D.R.k from (by simp; omega))] at h2
    exact h2
  have hB : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (b : ℕ) (hb : b ≤ j),
      (((sysS H X std).w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
    intro v s b hb
    have hlt : b * ((sysS H X std).t + 1) < (j + 1) * ((sysS H X std).t + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos _)
    have hr' : (sysS H X std).G.P.m + 1 + b * ((sysS H X std).t + 1) < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by
      omega
    have h1 := hw0 v s ⟨_, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨_, hr'⟩ = -((sysS H X std).w v (b + 1) s) :=
      liftWt_blk (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) b hr'
    rw [h3] at h1
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨_, hr'⟩)
    have hv : ((finCongr hrk) ⟨_, hr'⟩ : ℕ) = D.R.k + b * (D.R.t + 1) := by
      simp only [finCongr_apply, Fin.coe_cast]
      rw [← hk, ← ht]
    have hd : (D.R.k + b * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = b := by
      rw [Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
    have he : ∀ (b' : ℕ) (hb' : b' < D.R.m), b' = b → (D.hcW u (pos ⟨v, s⟩)).e ⟨b', hb'⟩ = (D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩ := by
      rintro b' hb' rfl; rfl
    rw [dite_eq_right (show ¬ (((finCongr hrk) ⟨_, hr'⟩ : Fin _) : ℕ) < D.R.k by rw [hv]; omega)] at h2
    rw [he _ _ (by rw [hv, hd]), hv, hd] at h2
    have h4 : ((-((sysS H X std).w v (b + 1) s) : ℤ) : ℚ) = -wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
      rw [h1]; exact h2
    push_cast at h4
    linarith
  have hcT : ∀ i, ((CmpJ.cTw D i : ℤ) : ℚ) = (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
    intro i
    obtain ⟨c, hc⟩ := D.R.t_odd
    have h2 : i * (D.R.t + 1) / 2 = i * (c + 1) := by
      rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, ← mul_assoc, mul_comm i 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    simp only [CmpJ.cTw, h2]
    push_cast
    rw [hc]
    push_cast
    ring
  refine ⟨(GlobalTheory.TwV.DelB.sysS_ranks S).2.2.2 j, ?_, ?_, ?_⟩
  · intro τ i
    generalize hvs : pos.symm τ = vs
    obtain ⟨v, s⟩ := vs
    have hτ : τ = pos ⟨v, s⟩ := by rw [← hvs]; simp
    subst hτ
    have hS := Formalism.L2.KerInert.SecondKernelSharpWeights.sharp_weight_formula D ex.tw u μ j hj (pos ⟨v, s⟩) i
    have hL := (ex.tw.fm u μ).lam_eq j hj.le (pos ⟨v, s⟩) i
    have hSs := (D.chTw u μ).sSharp_eq j hj (pos ⟨v, s⟩)
    have hwj := hB v s j le_rfl
    have hk' : (D.gat u w hg).P.m + 1 = D.R.k := hk
    have hcomm := Nat.mul_comm j (D.R.t + 1)
    have hiN : i.1 < D.R.k + j * (D.R.t + 1) := by have := i.2; simp only [Ranks.N] at this; exact this
    apply Int.cast_injective (α := ℚ)
    simp only [hvs, Sys.nuv, nu]
    by_cases hr : i.1 < D.R.k
    · rw [if_pos (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      simp only [lamI]
      rw [dite_eq_left (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      have hl0 := hA v s i.1 (by omega)
      rw [dite_eq_left hr] at hL
      simp only [Nat.add_sub_cancel]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs
      push_cast at hS hSs hwj
      rw [hl0]
      linarith
    · have hjt : (j + 1) * (D.R.t + 1) = j * (D.R.t + 1) + (D.R.t + 1) := by ring
      rw [if_neg (show ¬ (1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1) by omega)]
      rw [if_pos (show (sysS H X std).G.P.m + 1 < i.1 + 1 ∧ i.1 + 1 ≤ NN (sysS H X std).G.P.m (sysS H X std).t (j + 1) by
        simp only [NN]; rw [ht]; omega)]
      have hidx : (i.1 + 1 - ((sysS H X std).G.P.m + 2)) / ((sysS H X std).t + 1) = (i.1 - D.R.k) / (D.R.t + 1) := by
        rw [ht]; congr 1; omega
      have hb : (i.1 - D.R.k) / (D.R.t + 1) < j := by
        apply Nat.div_lt_of_lt_mul; omega
      have hwb := hB v s ((i.1 - D.R.k) / (D.R.t + 1)) hb.le
      rw [dite_eq_right hr] at hL
      rw [hidx]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs hwb hL
      push_cast at hS hSs hwj hwb hL
      linarith
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSs := (D.chTw u μ).sSharp_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSs, hcT]
    simp only [Formalism.BasicNotions.wG, sExp', Ranks.N]
    push_cast
    ring
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSd := (D.chTw u μ).sDiv_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSd, hcT]
    simp only [Formalism.BasicNotions.wG, sExp, Ranks.N]
    push_cast
    ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStep
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.MvS

theorem cast_lev {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) (κ : (S.K β).lev.U) :
    ∃ κ' : (St.K (St.chOf c')).lev.U, κ'.1 = κ.1 ∧ (St.K (St.chOf c')).lev.chi κ' = (S.K β).lev.chi κ := by
  subst hSt hc' h hβ
  exact ⟨κ, rfl, rfl⟩


set_option maxHeartbeats 2000000 in
theorem pt_step {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (β : S.Ch) (hC : S.Core e β) (a : S.cmpt β)
    (γ : ((S.charts.gat β).lev a).Γ) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hg' : ∀ v, ((S.charts.gat β).lev a).smul γ L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : (S.loc β).IsPt a g x.1) (hx' : (S.loc β).IsPt a g' x'.1) :
    ∃ κ : (S.K β).lev.U, x'.1 = GlobalTheory.TwU.ratA D.host.F ((S.loc β).gamI a γ) * x.1 * κ.1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((S.K β).lev.chi κ : ℂˣ) : ℂ) ∧
        algebraMap G.O G.Kf ((((S.charts.gat β).lev a).χ γ : G.Oˣ) : G.O) = e r := by
  obtain ⟨κa, hκa⟩ := awayEx_of hC.good (S.K β).lev hC.gam a γ
  obtain ⟨ra, hra1, hra2⟩ := hC.chi a γ κa hκa
  obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.TwV.Xc.isPt_move_eq _ _ _ _ _ _ (S.loc β) _ _ _ _ (S.K β).lev hC.good hC.int hC.hypP hC.actB hC.bad_p a γ
    (hC.gamU a γ) κa hκa g g' (fun v => (hg' v).symm.trans (PStabEq.smul_colSpan (G := S.charts.gat β) a γ L g hg v)) x x' hx hx'
  refine ⟨κ, hκ1, ra⁻¹, ?_, ?_⟩
  · rw [map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc.MvS

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem moveBy_succ : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS i hi c La γ hL
  obtain ⟨⟨β, a⟩, rfl⟩ := (I.at' i hi).st.eC.surjective c
  have hC := H.core i hi β
  have hpt : ∀ L', ((I.at' i hi).st.loc β).IsPt a
      (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) L')
      (J.pt std (i + 1) hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).1 := by
    intro L'
    have h := (Joint.pt_succ_isPt t std J i hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).2
    have key : ∀ (b : Σ β : (I.at' i hi).st.Ch, (I.at' i hi).st.cmpt β), b = ⟨β, a⟩ → ∀ g x, ((I.at' i hi).st.loc b.1).IsPt b.2 g x →
        ((I.at' i hi).st.loc β).IsPt a g x := by
      rintro _ rfl g x h
      exact h
    exact key _ (Equiv.symm_apply_apply _ _) _ _ h
  have hb := Joint.basesAt_span t std J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) hL
  have hb' : ∀ v, (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) =
      colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La)) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
    intro v
    unfold basesAt
    exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj (i + 1)).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _))
      ⟨_, PStabEq.smul_colSpan (G := (I.at' i hi).st.charts.gat β) a γ La _ (fun v => hb v) v⟩
  obtain ⟨κ, hκ, r, hr1, hr2⟩ := MvS.pt_step (I.at' i hi).st _ β hC a γ La _ _ (fun v => hb v) (fun v => hb' v) _ _ (hpt La) (hpt _)
  have hc : (I.at' i hi).st.chOf (clsOf (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La) = β :=
    (clsOf_chart (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La hL).trans
      (congrArg Sigma.fst (Equiv.symm_apply_apply (I.at' i hi).st.eC ⟨β, a⟩))
  obtain ⟨κ', hκ'1, hκ'2⟩ := MvS.cast_lev (X.onCh i hi) (I.at' i hi).st (J.St (i + 1) hi) (J.st i hi) _
    (clsAt X H (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩) La) (clsAt_succ X H i hi _ La) β hc κ
  refine ⟨((I.at' i hi).st.loc β).gamI a γ, κ', hC.gamU a γ, ?_, ?_, r, ?_, hr2⟩
  · exact hκ.trans (congrArg _ hκ'1.symm)
  · intro hr v
    have hB : (J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc β).rk.symm) ((I.at' i hi).st.loc β).B := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).B = _
      rw [dite_eq_left hi]
      show Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).rk.symm)
        ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).B = _
      rw [Equiv.symm_apply_apply]
    have hJ : (J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc β).rk.symm) (finCongr ((I.at' i hi).st.loc β).rk.symm) := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).J = _
      rw [dite_eq_left hi]
    have hiw : (J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) = ((I.at' i hi).st.loc β).iw := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).iw = _
      rw [dite_eq_left hi]
      show ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).iw = _
      rw [Equiv.symm_apply_apply]
    have hρ : J.rho std v = ((I.at' i hi).st.loc β).iw v := (J.iw i hi β v).symm
    have hF : (J.fd std).frM (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v =
        (((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La))).toLinearMap)) *
          ((J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La)).1).map ((J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v)).submatrix
          (finCongr rfl) (finCongr rfl) := rfl
    rw [hF, hB, hJ, hiw, hρ]
    exact Mv0.frm_gen (Q := (sysS H X std).G.P.Qq v) _ ((I.at' i hi).st.loc β).rk hr (gramN D (i + 1) hi) ((I.at' i hi).st.loc β).B (((I.at' i hi).st.loc β).gamI a γ)
      (((I.at' i hi).st.loc β).iw v) _ (hC.actB a v γ)
  · exact hr1.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hκ'2.symm)

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDecompositionOccursInFamily
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem dec_update : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (γ : GL (Fin (D.R.N (j + 1))) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) → ∀ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = GlobalTheory.TwU.ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 → ∃ d : Dec J std, d.gam (j + 1) hj La = γ ∧ d.kap (j + 1) hj La = κ) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S hD j hj La hLa γ hγ κ hκ
  obtain ⟨d0⟩ := _root_.GlobalTheory.TwV.DelB.dec_exists S hD
  have key : ∀ k (hk : k ≤ D.R.m) (Lb : (sysS H X std).Lt k), ∃ (g : GL (Fin (D.R.N k)) D.host.E)
      (c : ((J.St k hk).K (J.chart std k hk Lb)).lev.U),
      g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) ∧
      (((sysS H X std).Pj k).IsLatTup Lb.2 →
        (J.pt std k hk Lb).1 = GlobalTheory.TwU.ratA D.host.F g * ((J.St k hk).y (clsAt X H k Lb.1 Lb.2)).1 * c.1) ∧
      (∀ _ : k = j + 1, HEq Lb La → HEq g γ ∧ HEq c κ) := by
    intro k hk Lb
    by_cases h : k = j + 1 ∧ HEq Lb La
    · obtain ⟨rfl, h2⟩ := h
      obtain rfl := eq_of_heq h2
      exact ⟨γ, κ, hγ, fun _ => hκ, fun _ _ => ⟨HEq.rfl, HEq.rfl⟩⟩
    · exact ⟨d0.gam k hk Lb, d0.kap k hk Lb, d0.mem k hk Lb, d0.eq k hk Lb, fun e hL => absurd ⟨e, hL⟩ h⟩
  choose g c hm he hh using key
  exact ⟨⟨g, c, hm, he⟩, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).1, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).2⟩

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarEqCharacterProduct
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB


set_option maxHeartbeats 1000000 in
theorem scalAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa'
  obtain ⟨hmm, ht, hN, -⟩ := _root_.GlobalTheory.TwV.DelB.sysS_ranks S
  have hj0 : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hdt0 := (hD j hj0 La hLa).2.2.2
  have hdt1 := (hD (j+1) hj1 La' hLa').2.2.2
  have e0 := d.eq j hj0 La hLa
  have e1 := d.eq (j+1) hj1 La' hLa'
  have M0 := _root_.GlobalTheory.TwV.mu_det_rat_y_lev J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj j hj0 (clsAt X H j La.1 La.2) (J.pt std j hj0 La) (d.gam j hj0 La) (d.mem j hj0 La) (d.kap j hj0 La) e0
  have M1 := _root_.GlobalTheory.TwV.mu_det_rat_y_lev J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j+1) hj1 (clsAt X H (j+1) La'.1 La'.2) (J.pt std (j+1) hj1 La') (d.gam (j+1) hj1 La') (d.mem (j+1) hj1 La') (d.kap (j+1) hj1 La') e1
  have C0 := _root_.GlobalTheory.TwV.DelB.chi_detId_kerN S hD d j hj0 La hLa
  have C1 := _root_.GlobalTheory.TwV.DelB.chi_detId_kerN S hD d (j+1) hj1 La' hLa'
  have eN0 : (((sysS H X std).Pj j).m + 1) / 2 = D.R.N j / 2 := by rw [hN]
  have eN1 : (((sysS H X std).Pj (j + 1)).m + 1) / 2 = D.R.N (j + 1) / 2 := by rw [hN]
  have R0 : ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ)⁻¹ *
        ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ (-(((D.R.N (j + 1) / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf]
  have R1 : ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) *
        ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ ((((D.R.N j / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf']
  simp only [Dec.sC, Dec.sP, Dec.uS, Dec.uT, scal0, Base.chiFac, dif_pos hj1, dif_pos hj0]
  rw [R0, R1, hdt0, hdt1, M0.1, M1.1, C0.1, C1.1, eN0, eN1, ht]
  exact _root_.GlobalTheory.TwV.DelB.pullback_contraction_scalars _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cTw D j) (cTw D (j + 1)) (Units.ne_zero _) (Units.ne_zero _) M0.2.1 M1.2.1 M0.2.2 M1.2.2
    (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) C0.2 C1.2

end GlobalTheory.TwV.DelB
end

