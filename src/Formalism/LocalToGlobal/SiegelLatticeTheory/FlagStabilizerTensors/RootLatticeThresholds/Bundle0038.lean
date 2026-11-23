module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRhoX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
  Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

theorem exists_b (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ b : Fin D.R.r → Fin X.B.I.n → X.B.I.E, IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
  rw [← X.n_eq]
  exact exists_redBasis (I := X.B.I) (w := wB X (D.naut.plGw kv.1 kv.2)) (hp := D.host.g_prime kv.1)
    (hcard := by rw [card_wB, card_res_host])

def redBX (kv : Σ k : Fin 2, D.nd.PlG k) : RedB X.B.I D.R.r where
  w := wB X (D.naut.plGw kv.1 kv.2)
  p := D.host.g kv.1
  hp := D.host.g_prime kv.1
  hcard := by rw [card_wB, card_res_host]
  hm := X.n_eq.symm
  b := Classical.choose (exists_b X kv)
  hb := Classical.choose_spec (exists_b X kv)

def rhoX : KSub X.B.I →* G0g D.nd := MonoidHom.pi fun kv => rhoB (redBX X kv)

theorem rhoX_apply (x : KSub X.B.I) (kv : Σ k : Fin 2, D.nd.PlG k) : rhoX X x kv = rhoB (redBX X kv) x := rfl

theorem goodAt_rhoX (x : KSub X.B.I) : GoodAt X x (rhoX X x) := by
  intro kv
  exact (redMat_iff X _ _ _ _).mpr (redMat0_of (I := X.B.I) (hb := (redBX X kv).hb) (h := rhoB_spec (redBX X kv) x))

theorem redMatB_one_of {I : AutInst} {m : ℕ} (R : RedB I m) {x : I.Gf}
    (h : ∀ i, I.fmat x *ᵥ iv I (R.b i) - iv I (R.b i) ∈ Lq I R.w) :
    RedMatB I R.w R.p R.b x (1 : Matrix (Fin m) (Fin m) (ZMod R.p)) := by
  haveI : Fact (1 < R.p) := ⟨R.hp.one_lt⟩
  intro i
  have hsum : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod R.p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (R.b j) = iv I (R.b i) := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply_eq, ZMod.val_one]
    · intro j _ hj
      simp [Matrix.one_apply_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  exact h i

theorem rhoX_eq_one_iff (x : KSub X.B.I) : rhoX X x = 1 ↔ (x : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  have hRK : Formalism.L2.SG.AllRowsOf.RedKer X :=
    Formalism.L2.SG.AllRowsOf.redKer_of (X := X) (Formalism.L2.SG.AllRowsOf.redKerOne_of (X := X)
      (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))
  constructor
  · intro h
    have h1 := goodAt_rhoX X x
    rw [h] at h1
    exact (hRK x x.2).1 h1
  · intro hx
    have hK : (x : X.B.I.Gf) ∈ X.B.I.Kset := x.2
    have hG := Formalism.L2.SG.AllRowsOf.goodAt_one_of_mem_Kg (X := X) hx
    funext kv
    rw [rhoX_apply]
    apply Units.ext
    have hR0 := (redMat_iff X _ _ _ _).mp (hG kv)
    have hR1 := hR0
    simp only [Pi.one_apply, Units.val_one] at hR1
    have hA := Formalism.L2.SG.Pf.AllRowsRedKerA.stepA (I := X.B.I) (redBX X kv).hp (redBX X kv).hcard hK hR1
    have hB : RedMatB X.B.I (redBX X kv).w (redBX X kv).p (redBX X kv).b x 1 :=
      redMatB_one_of (redBX X kv) fun i => by
        have h1 := hA _ (PIW.AdelClassFin.DictLat.iv_mem X.B.I ((redBX X kv).hb.1 i))
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    have h2 := matB_eq (redBX X kv) hK hB
    show ((rhoB (redBX X kv) x : GL (Fin D.R.r) (ZMod (redBX X kv).p)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p)) =
      ((1 : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p))
    rw [Units.val_one]
    exact h2

theorem ES_conj (S : Set (Tup2 D)) (γ P : G0g D.nd) : (ES S).coeff (P⁻¹ * γ * P) = (ES S).coeff γ := by
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)
  · rfl

theorem egA_rhoX (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (x : KSub X.B.I) : egA X a x = a.coeff (rhoX X x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by
  have h : (x : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ :=
    ⟨x.2, rhoX X x, goodAt_rhoX X x⟩
  unfold egA
  rw [dite_eq_left h]
  congr 1
  have hγ := Classical.choose_spec h.2
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Classical.choose h.2) kv = P⁻¹ * rhoX X x kv * P := by
    intro kv
    have h1 := (redMat_iff X _ _ _ _).mp (goodAt_rhoX X x kv)
    have h2 := (redMat_iff X _ _ _ _).mp (hγ kv)
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I _ _ (redBX X kv).hp (redBX X kv).hcard D.R.r
      (redBX X kv).hm x _ _ h1 h2
  choose P hP using hP
  have e1 : Classical.choose h.2 = P⁻¹ * rhoX X x * P := by
    funext kv
    rw [hP kv]
    rfl
  rw [e1, ha]

def RhoSurj : Prop := ∀ (D : D7) (X : HidaSetting D), Function.Surjective (rhoX X)

end Formalism.L2.SG.Pf.AllRowsRhoX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.ThmBUseR
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.BDatR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section J2

variable {D : D7}

def JointAmplitudeFactorizationRotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) (large₂ : SizeData₂ D) (C1 : ℝ)
    (W : D.what₂.Tau → LocW D.R.k D.R.rS) (A : ∀ τ, LocS (W τ)) (T T' : ℕ) (Cfac : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), Formalism.FourierDecayAlt.PN.IsPt X N γ → Formalism.L2.SG.RowsConc.toPts w = γ →
    Formalism.L2.SG.ThmBUse.IsRowPt D T T' w → 0 < N.jacobianSquareBound γ →
    ∃ (g : D.what₂.Tau → MatKR D.R.k D.R.rS) (θ' : D.what₂.Tau → ℝ)
      (νR : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      (∀ τ, RelPt D (W τ).z (W τ).z' (g τ) (ptLoc D τ w) ∧ normWin D large₂ C1 (θ' τ) ∧
        RMeas D (W τ) (g τ) (θ' τ) (νR τ)) ∧
      ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((A τ).J (νR τ) (g τ)))

private lemma prod_ofReal_le_lemma {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∏ i ∈ s, ENNReal.ofReal (x i) ≤ ENNReal.ofReal (∏ i ∈ s, x i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha]
  rcases le_or_gt 0 (x a) with h | h
  · rw [ENNReal.ofReal_mul h]; gcongr
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_mul]; simp

theorem jointAmplitude_bound_rotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) {large₂ : SizeData₂ D} {C1 Ca Ch Cg b : ℝ}
    {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : AmpIn large₂ C1 Ca u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D))
    (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hF : JointAmplitudeFactorizationRotated X N large₂ C1 I.W I.A (D.mem u).A.T (D.mem u').A.T Cfac) :
    JointNormBoundRotated X N (bdOf I.toInputs hok) (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) := by
  intro γ w hpt hw hrow
  by_cases hpos : 0 < N.jacobianSquareBound γ
  · obtain ⟨g, θ', νR, hτ, hle⟩ := hF γ w hpt hw hrow hpos
    have h1 : ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) ≤
        ∏ τ, (ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
          orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by
      apply Finset.prod_le_prod'
      intro τ _
      exact le_trans (I.hJ τ (g τ) (ptLoc D τ w) (hτ τ).1 (θ' τ) (hτ τ).2.1 (νR τ) (hτ τ).2.2)
        (by gcongr; exact orbSqO_le_bdOf I.toInputs hok hka τ _)
    rw [Finset.prod_mul_distrib] at h1
    have h2 := prod_ofReal_le_lemma Finset.univ (fun τ => I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))
    calc ENNReal.ofReal (N.jacobianSquareBound γ)
        ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) := hle
      _ ≤ ENNReal.ofReal Cfac * ((∏ τ, ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ ≤ ENNReal.ofReal Cfac * (ENNReal.ofReal (∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ = ENNReal.ofReal (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          JSqR D (bdOf I.toInputs hok) w := by
        rw [ENNReal.ofReal_mul hCfac, mul_assoc]; rfl
  · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hpos)]; simp

end J2

section Cut

open Formalism.L2.SG.Pf.JointAmplitudePoints

variable {D : D7} {X : HidaSetting D}

def RelPtExPR (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ,
      RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) (ptLoc D τ w)

private lemma toPts_inj_lemma {K : Type} [Zero K] {i : ℕ} (p q : Formalism.MainNotions.S.Point K (i + 1))
    (h : Formalism.L2.SG.RowsConc.toPts p = Formalism.L2.SG.RowsConc.toPts q) : p = q := by
  have h1 : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun s => s.1.blocks) h
  have key : ∀ r : Formalism.MainNotions.S.Point K (i + 1), List.ofFn (Formalism.L2.SG.RowsConc.toPts r).2 = r.1.map Prod.fst := by
    intro r
    apply List.ext_get
    · simp [Formalism.L2.SG.RowsConc.toPts, Composition.length]
    · intro n h1 h2
      simp [Formalism.L2.SG.RowsConc.toPts]
  have h2 : p.1.map Prod.fst = q.1.map Prod.fst := by
    rw [← key p, ← key q]
    exact congrArg (fun s : (Σ c : Composition (i + 1), (Fin c.length → K)) => List.ofFn s.2) h
  apply Subtype.ext
  rw [← List.zip_unzip p.1, ← List.zip_unzip q.1, List.unzip_fst, List.unzip_snd, List.unzip_fst,
    List.unzip_snd, h1, h2]

private lemma quot_scale_lemma_2 {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.MainNotions.S.IsQuotMeas μG μS ν) {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    Formalism.MainNotions.S.IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem jointAmplitudeFactorizationRotated_of (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExPR u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    JointAmplitudeFactorizationRotated (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (WX C u u') (AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 := by
  intro γ w hpt hw hrow hpos
  have hJB : (NOf2 Y u u' νL ν ng).jacobianSquareBound γ = J2of Y u u' ν γ := rfl
  rw [hJB] at hpos ⊢
  subst hw
  obtain ⟨w', hw', hrep⟩ := isPtRep_of_J2of hpos
  have hww : w' = w := toPts_inj_lemma w' w hw'
  subst hww
  have hP1 : 0 < localAmplitudeProduct u u' hB w' := hP w' hrow hpos
  haveI := Formalism.L2.SG.Pf.LTL.tau_nonempty D
  have hn : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos
  have hθ0 : thetaP u u' hB (J2of Y u u' ν (toPts w')) w' =
      (localAmplitudeProduct u u' hB w' / J2of Y u u' ν (toPts w')) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    simp only [thetaP, if_pos (And.intro hpos hP1)]
  have hθpos : 0 < thetaP u u' hB (J2of Y u u' ν (toPts w')) w' := by
    rw [hθ0]; apply Real.rpow_pos_of_pos; exact div_pos hP1 hpos
  have hν1 : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 (nu1P C u u' w' τ) := fun τ => by
    have h := hM w' hrow hrep τ
    simp only [nu1P, dif_pos h]
    exact h.choose_spec
  have hsc : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')
      (ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ) := fun τ => by
    obtain ⟨p, μR, hroot, hq⟩ := hν1 τ
    refine ⟨p, μR, hroot, ?_⟩
    rw [ENNReal.ofReal_one, one_smul] at hq
    rw [ENNReal.ofReal_inv_of_pos hθpos]
    exact quot_scale_lemma_2 hq (ENNReal.ofReal_pos.mpr hθpos).ne' ENNReal.ofReal_ne_top
  refine ⟨fun τ => gamP C u u' w' τ, fun _ => thetaP u u' hB (J2of Y u u' ν (toPts w')) w',
    fun τ => ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ,
    fun τ => ⟨hR w' hrow hrep τ, hT w' hrow hpos, hsc τ⟩, ?_⟩
  set θ0 := thetaP u u' hB (J2of Y u u' ν (toPts w')) w' with hθdef
  set J2 := J2of Y u u' ν (toPts w') with hJ2def
  have hfac : ∀ τ, hsNormSq ((AX hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) =
      θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ)) := fun τ => by
    show hsNormSq ((locS hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) = _
    rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, Complex.normSq_ofReal,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hθpos.le)]
  have hpow : θ0 ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2 := by
    rw [hθ0, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hpos).le]
    have : (1 : ℝ) / (2 * Fintype.card D.what₂.Tau) * ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  have hprod : ∏ τ, (θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))) = J2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    change (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2
    have e : (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau = (θ0 ^ (2 * Fintype.card D.what₂.Tau))⁻¹ := by
      rw [← mul_inv, ← pow_two, inv_pow, ← pow_mul]
    rw [e, hpow, inv_div, div_mul_cancel₀ _ hP1.ne']
  rw [ENNReal.ofReal_one, one_mul]
  simp only [hfac]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun τ _ => by
    have := Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))
    positivity), hprod]

end Cut

section Steps

open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Steps

end Formalism.L2.SG.Pf.BDatR
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.InvLast
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse (Formalism.L2.SG.RealObj.Dl Z (r + 1)) * Formalism.L2.SG.RealObj.Dl Z r := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hr : Formalism.L2.SG.RealObj.Dl Z r = (Z.submatrix (Fin.last r).succAbove (Fin.last r).succAbove).det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left (Nat.le_succ r)]
    congr 1; ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_last]; rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix, hfull, hr]
  have : ((-1 : ℂ) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

theorem gap_of_G {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 0 < Gv T T' Z) :
    1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0 := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hd : Formalism.L2.SG.RealObj.Dl Z (r + 1) ≠ 0 := by rw [hfull]; exact hZ.ne_zero
  rw [inv_last, Ring.inverse_eq_inv']
  set d := Formalism.L2.SG.RealObj.Dl Z (r + 1)
  set e := Formalism.L2.SG.RealObj.Dl Z r
  have hdd : d * starRingEnd ℂ d ≠ 0 := mul_ne_zero hd ((map_ne_zero _).2 hd)
  intro h0
  have h1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = 0 := by
    have e1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) =
        (d * starRingEnd ℂ d) * (1 - (T : ℂ) * T' * (d⁻¹ * e * starRingEnd ℂ (d⁻¹ * e))) := by
      have hcd : starRingEnd ℂ d ≠ 0 := (map_ne_zero _).2 hd
      rw [map_mul, map_inv₀]; field_simp
    rw [e1, h0, mul_zero]
  have h2 : ((Complex.normSq d - T * T' * Complex.normSq e : ℝ) : ℂ) = 0 := by
    rw [← h1]; push_cast; rw [Complex.mul_conj, Complex.mul_conj]
  have h3 : Complex.normSq d - T * T' * Complex.normSq e = 0 := by exact_mod_cast h2
  unfold Gv at hG
  rw [Complex.sq_norm, Complex.sq_norm] at hG
  linarith

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Easy

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem w_smooth (C : Choice X θ) (τ : D.what₂.Tau) :
    X.B.w (vOf X τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := by
  have hds := Formalism.L2.SG.Pf.dsTr C τ
  obtain ⟨hrep, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  have hy := C.y_mem τ
  have hw1 : ‖X.B.w (vOf X τ)‖ = 1 := (X.low (vOf X τ)).1
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) := ⟨P, hP, by rw [hiso _ hy, hw1], hmem⟩
  have hv0 := Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds hlow
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := WlocSk.HM.uh_inv hy
  have hsm := Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hv0 hyi
  have hinvy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (WlocSk.HM.isUnit_of_uh hy)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (C.y τ)⁻¹ (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) =
      X.B.w (vOf X τ) := by
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hyi _ hy, hinvy, hrep.1]
    rfl
  rw [e] at hsm
  exact hsm

theorem muS_haar (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (muS (C.muW u τ) (muNB D θ)) := by
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hz, hTz⟩ := zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  exact isHaarOn_muS hz hT (C.muW_haar u τ) (C.muW_one u τ) (kapN_ne_zero D hθ) (kapN_ne_top D θ)

end Easy

section Clauses

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def ContClause (C : Choice X θ) : Prop :=
  ∀ u τ, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))

def EquivClause (C : Choice X θ) : Prop :=
  ∀ u τ, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)

def ReprodClause (C : Choice X θ) : Prop :=
  ∀ u τ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
    MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (X.B.w (vOf X τ)) (Matrix.of g) •
        wT C u τ (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
    rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (X.B.w (vOf X τ))) (wT C u τ) x = wT C u τ x

def L2ChoiceCondition (C : Choice X θ) : Prop :=
  ∀ u τ, l2SG (C.nuS u τ) (wT C u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (wT C u τ) < ⊤

def EquivAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), EquivClause C

def L2ConditionAllChoices : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), L2ChoiceCondition C

def ContAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ContClause C

def ReprodAll : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ReprodClause C

theorem locFactor_of_clauses (C : Choice X θ) (hC : ContClause C) (hE : EquivClause C) (hR : ReprodClause C)
    (hL : L2ChoiceCondition C) : LocFactor C :=
  fun u τ => ⟨w_smooth C τ, (X.low (vOf X τ)).1, muS_haar C u τ, hC u τ, hE u τ, hR u τ, (hL u τ).1, (hL u τ).2⟩

theorem locFactor_of (hCA : ContAll) (hEA : EquivAll) (hRA : ReprodAll) (hLA : L2ConditionAllChoices)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (C : Choice X θ) : LocFactor C :=
  locFactor_of_clauses C (hCA D X θ C) (hEA D X θ C) (hRA D hG X θ C) (hLA D hG X θ C)

end Clauses

end Formalism.L2.SG.Pf.LocF
end
end

