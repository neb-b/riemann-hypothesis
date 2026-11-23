module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ThA

private lemma inv_mul_comm_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (a h : Matrix n n ℂ)
    (hah : a * h = h * a) : h⁻¹ * a = a * h⁻¹ := by
  by_cases hh : IsUnit h.det
  · calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hah]
      _ = a * h⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h a, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hh, Matrix.zero_mul, Matrix.mul_zero]

private lemma inv_mul_conj_mul_conj_eq_conj_of_commute {n : Type*} [Fintype n] [DecidableEq n] (a H M g M' H' : Matrix n n ℂ)
    (ha : IsUnit a.det) (c1 : a * H = H * a) (c2 : a * H' = H' * a) :
    H⁻¹ * (a * M * a⁻¹)⁻¹ * g * (a * M' * a⁻¹) * H' =
      a * (H⁻¹ * M⁻¹ * (a⁻¹ * g * a) * M' * H') * a⁻¹ := by
  have e1 : (a * M * a⁻¹)⁻¹ = a * M⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]
  have d1 : H⁻¹ * a = a * H⁻¹ := inv_mul_comm_of_mul_comm a H c1
  have d2 : a⁻¹ * H' = H' * a⁻¹ := inv_mul_comm_of_mul_comm H' a c2.symm
  rw [e1]
  simp only [Matrix.mul_assoc]
  rw [d2, ← Matrix.mul_assoc H⁻¹ a, d1, Matrix.mul_assoc]

theorem besselJ_conj {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : μW (UWset k r z)ᶜ = 0) (hN : μN (Nset k r)ᶜ = 0) (hW' : μW' (UWset k r z')ᶜ = 0)
    (a : B.Mat k r) (ha : IsUnit a.det)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a) (hc' : ∀ h ∈ UWset k r z', a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n)
    (hp' : ∀ n ∈ Nset k r, psi k r z' c (a * n * a⁻¹) = psi k r z' c' n)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (μN.map (conjM a)) μW' F g =
      besselJ k r z z' c' π π' μW μN μW' (fun x => F (a * x * a⁻¹)) (a⁻¹ * g * a) := by
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE (k := k) (r := r) a ha).measurable
  let E : Mt k r ≃ᵐ Mt k r := BesselUnitaryEquiv.conjE (k := k) (r := r) a ha
  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl (Mt k r)).prodCongr E).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr E)
  have hpm : ∀ (ν : Measure (Mt k r)) [SFinite ν],
      (ν.prod μN).map (Prod.map id (conjM a)) = ν.prod (μN.map (conjM a)) := by
    intro ν _
    rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]
  have hμ : (μW.prod (μN.map (conjM a))).prod (μW'.prod (μN.map (conjM a))) =
      ((μW.prod μN).prod (μW'.prod μN)).map Φ := by
    rw [← hpm μW, ← hpm μW', Measure.map_prod_map _ _ (measurable_id.prodMap hm) (measurable_id.prodMap hm)]
    rfl
  have aW : ∀ᵐ x ∂μW, x ∈ UWset k r z := ae_iff.2 hW
  have aN : ∀ᵐ x ∂μN, x ∈ Nset k r := ae_iff.2 hN
  have aW' : ∀ᵐ x ∂μW', x ∈ UWset k r z' := ae_iff.2 hW'
  have q1 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae aW)
  have q2 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae aN)
  have q3 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae aW')
  have q4 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae aN)
  unfold besselJ
  rw [hμ, integral_map_equiv]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2, q3, q4] with p h1 h2 h3 h4
  have hΦ : Φ p = ((p.1.1, conjM a p.1.2), (p.2.1, conjM a p.2.2)) := rfl
  have e2 : Matrix.of (conjM a p.1.2) = a * Matrix.of p.1.2 * a⁻¹ := rfl
  have e4 : Matrix.of (conjM a p.2.2) = a * Matrix.of p.2.2 * a⁻¹ := rfl
  rw [hΦ]
  dsimp only
  rw [e2, e4, hp (Matrix.of p.1.2) h2, hp' (Matrix.of p.2.2) h4,
    inv_mul_conj_mul_conj_eq_conj_of_commute a (Matrix.of p.1.1) (Matrix.of p.1.2) g (Matrix.of p.2.2) (Matrix.of p.2.1) ha
      (hc (Matrix.of p.1.1) h1) (hc' (Matrix.of p.2.1) h3)]

theorem besselJ_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW'] (t : ℝ≥0∞)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (t • μN) μW' F g =
      ((t.toReal ^ 2 : ℝ) : ℂ) • besselJ k r z z' c π π' μW μN μW' F g := by
  unfold besselJ
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, ← pow_two, Complex.coe_smul]

theorem besselJ_changeFrame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  intro k r L μsec Bs cN F hstd hR hc hκ0 hκT g
  obtain ⟨hz, hz', hπ, hπ', hμW, hμW', hμN, -⟩ := hstd
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  have hcα : L.c * (cStd / L.c) = cStd := by field_simp
  set α := cStd / L.c with hαdef
  obtain ⟨-, hT, -, -⟩ := _root_.GlobalTheory.ThA.TorusElt.torusElt k r α hα
  obtain ⟨hcz, hnz⟩ := hT L.z L.hz.1
  obtain ⟨hcz', hnz'⟩ := hT L.z' L.hz'.1
  have hmap := _root_.GlobalTheory.ThA.TorusJac.muN_map_conj k r α hα
  have ha : IsUnit (aT k r α).det := by
    rw [aT, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    split_ifs
    · exact pow_ne_zero _ hα
    · exact one_ne_zero
    · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))
  have hp : ∀ w : Fin (2 * r + k + 1) → ℂ,
      (∀ n ∈ Nset k r, ell k r w (aT k r α * n * (aT k r α)⁻¹) = α * ell k r w n) →
      ∀ n ∈ Nset k r, psi k r w L.c (aT k r α * n * (aT k r α)⁻¹) = psi k r w cStd n := by
    intro w hw n hn
    simp only [psi, hw n hn, ← mul_assoc, hcα]
  haveI : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hNc : (D.muN k r) (Nset k r)ᶜ = 0 := by rw [← hμN]; exact Bs.haarN.conc
  haveI : IsFiniteMeasureOnCompacts (D.muN k r) :=
    ⟨fun K hK => by rw [← hμN]; exact Bs.haarN.finite_compact K hK⟩
  have hW : L.μW (UWset k r L.z)ᶜ = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' (UWset k r L.z')ᶜ = 0 := L.hμW'.1.2.2.1
  have hx : 0 < ‖α‖ ^ B.kap k r := pow_pos (norm_pos_iff.mpr hα) _
  have hone : ENNReal.ofReal (‖α‖ ^ B.kap k r) * ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
  have hLμN : L.μN = (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)) •
      (D.muN k r).map (conjM (aT k r α)) := by
    rw [hmap, smul_smul, mul_assoc (L.κN * ENNReal.ofReal cN), hone, mul_one, mul_smul, ← hR.2]
    simp only [Formalism.MainNotions.S.LocBessel.μN, Formalism.MainNotions.S.haarLie, one_smul]
  have ht : (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)).toReal = lamN L cN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.1.le, ENNReal.toReal_ofReal hx.le]
    rfl
  have step : L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) •
      besselJ k r L.z L.z' L.c L.π L.π' L.μW ((D.muN k r).map (conjM (aT k r α))) L.μW' F g := by
    rw [← ht]
    show besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g = _
    rw [hLμN]
    exact besselJ_smul k r L.z L.z' L.c L.π L.π' L.μW _ L.μW' _ F g
  rw [step, besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW (D.muN k r) L.μW' hW hNc hW' (aT k r α) ha
    hcz hcz' (hp L.z fun n hn => (hnz n hn).2.2) (hp L.z' fun n hn => (hnz' n hn).2.2) F g,
    Formalism.FourierDecayAlt.B.JF, hz, hz', hπ, hπ', hμW, hμW', hμN]
  rfl

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem capParam_of_isHCTypeW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → (∀ i : Fin k, U (i.val + 1) = u i) → Q.CapParam k r z π U := by
  intro k r z u U Wp _ _ _ π hz hT hπ hU
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', hu'⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  intro Bs hB w v
  rw [hu'.2.2.2.2.2 Bs hB w v]
  congr 1
  have key : ∀ f : ℕ → ℝ, ∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (f i : ℂ)) =
      ∏ s : Fin k, (w - (k : ℂ) / 2 + 1 / 2 + (f (s.val + 1) : ℂ)) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range (fun i => w - (k : ℂ) / 2 + 1 / 2 + (f (1 + i) : ℂ))]
    exact Finset.prod_congr rfl fun s _ => by rw [add_comm 1 s.val]
  rw [key, key, ← GlobalTheory.SupNonzero.prod_eq hu' hπ']
  simp only [hU]

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := _root_.GlobalTheory.Dec.definite_count_of_finite B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := _root_.GlobalTheory.KernelExpansion.kernelB B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := _root_.GlobalTheory.KernelConv.kernelA B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDsModelOfInstData
section
open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isEnum_parA_zero (D : D7) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    IsEnum (parA (tparRec D) 0 τ) (fun i : Fin n => lamS D.R (D.hc τ) (Fin.cast hn i))
      (fun i => epsS D.R (Fin.cast hn i)) := by
  subst hn
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  simp only [Fin.cast_eq_self]
  refine ⟨?_, fun i => if h : i.val < D.R.k - 1 then (D.hc τ).v ⟨i.val, h⟩
    else if h' : i.val - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i.val - (D.R.k - 1), h'⟩ else 0, ?_, ?_⟩
  · have h := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
    intro a b hab
    have := h (a := Fin.cast (dimS_eq D.R).symm a) (b := Fin.cast (dimS_eq D.R).symm b) hab
    simpa [lamSH] using this
  · intro a
    simp only [lamS]
    split_ifs <;> simp
  · have hpar : ∀ a : ℕ, decide (a ≤ 0 ∨ Even (a - 0)) = decide (a % 2 = 0) := by
      intro a
      rw [decide_eq_decide, Nat.sub_zero, Nat.even_iff]
      omega
    ext x
    simp only [parA, TPar.Dpar, tparRec, tparHC, hpar, Nat.not_odd_zero, if_false, add_zero,
      Nat.not_lt_zero, Finset.filter_false, Finset.biUnion_empty, Finset.union_empty, Prod.mk.eta,
      Finset.image_id', Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨⟨i.val, by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
      · refine ⟨⟨i.val + (D.R.k - 1), by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
    · rintro ⟨a, rfl⟩
      by_cases h : a.val < D.R.k - 1
      · exact Or.inl ⟨⟨a.val, h⟩, by simp [epsS, h]⟩
      · have h' : a.val - (D.R.k - 1) < D.R.m := by have := a.2; omega
        exact Or.inr ⟨⟨_, h'⟩, by simp [epsS, h, h']⟩

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreUnique

theorem fibre_family_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' → fib = fib' := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib h1 fib' h2
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  exact PI.VolStabS.FibUniq.fib_eq_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib fib' h1 h2

end GlobalTheory.LocalFibreUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.ProdFactor

theorem integrable_phLoc_of_integrable_ph : ∀ (D : D7) (X : HidaSetting D), Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hX v
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hd : ∀ v, X.dv v ≠ 0 := fun v =>
    (fdegOf_pos (hU v) (X.ds v).2.2.2.2.1 (hw v)).ne'

  exact integrable_factor' X.B.I.ε X.B.σ X.B.w X.dv hU hw hd hX v

end GlobalTheory.ProdFactor
end

