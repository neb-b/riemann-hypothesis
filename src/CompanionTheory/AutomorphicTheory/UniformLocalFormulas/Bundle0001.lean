module

public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.MeasConjM
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyCV
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0015
public import Formalism.HermitianCurvature.StatementPN
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula
section
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj.InfCut
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem place_eq {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Q' : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Q' = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {t : ℝ} (ht : 0 < t)
    (hc : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = (t : ℂ) ^ (r - (a : ℕ)) • e a ∧
      Q *ᵥ Pi.single (esI k r a) 1 = (star ((t : ℂ) ^ (r - (a : ℕ))))⁻¹ • f a) (κ : ℝ≥0∞) :
    (haarLie (Nset k r) κ).comap (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (trG Q Q' γ) : Mt k r)) =
      (κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • refNg hn ε e f wf (z0v T z) := by
  subst hn
  have hF := JX.isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hF
  have emb' : MeasurableEmbedding (cM (ε := ε) Q' Q) := cM_measEmb (A' := Q) (B' := Q') h2 h2
  set P := Qm e f wf (z0v T z) with hP
  set P' := Qi ε e f wf (z0v T z) with hP'
  have p1 : P' * P = 1 := Qi_mul_Qm hF
  have p2 : P * P' = 1 := Qm_mul_Qi hF
  have hdi : (P' * Q)⁻¹ = Q' * P := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h2, Matrix.one_mul, p1]
  have hd : P' * Q ∈ UH (Hpk k r) := by
    show (P' * Q)ᴴ * Hpk k r * (P' * Q) = Hpk k r
    calc _ = Qᴴ * (P'ᴴ * Hpk k r * P') * Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [QiHQi hF, hg]
  have hmap := conj_levi hd ht
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).1, Matrix.mulVec_smul, ← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec])
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).2, Matrix.mulVec_smul, ← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec]
      simp)
  have hcomp : cM (ε := ε) P' P = conjM (P' * Q) ∘ cM (ε := ε) Q' Q := by
    funext g
    show P' * uMat g * P = P' * Q * (Q' * uMat g * Q) * (P' * Q)⁻¹
    rw [hdi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q' P, h2, Matrix.one_mul, ← Matrix.mul_assoc Q Q', h2, Matrix.one_mul]
  have hu : IsUnit (P' * Q).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hd
  have hinj : Function.Injective (conjM (k := k) (r := r) (P' * Q)) := fun x y h => by
    have h' : P' * Q * Matrix.of x * (P' * Q)⁻¹ = P' * Q * Matrix.of y * (P' * Q)⁻¹ := h
    have := congrArg (fun m => (P' * Q)⁻¹ * m * (P' * Q)) h'
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
    exact this
  have hκ : haarLie (Nset k r) κ = κ • haarLie (Nset k r) 1 := by simp [haarLie]
  ext s hs
  show (haarLie (Nset k r) κ).comap (cM (ε := ε) Q' Q) s =
    ((κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • (haarLie (Nset k r) 1).comap (cM (ε := ε) P' P)) s
  rw [emb'.comap_apply, Measure.smul_apply, emb.comap_apply, hκ, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  have h3 := congrArg (fun m : Measure (Mt k r) => m (cM (ε := ε) P' P '' s)) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  rw [← h3, Measure.map_apply (meas_conjM _) (emb.measurableSet_image.2 hs), hcomp, Set.image_comp,
    Set.preimage_image_eq _ hinj]

theorem pi_smul {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  have : ∀ i, SigmaFinite ((c : ℝ≥0∞) • μ i) := fun i => inferInstanceAs (SigmaFinite (c • μ i))
  refine Measure.pi_eq fun s _ => ?_
  simp [Measure.pi_pi, Finset.prod_mul_distrib]

theorem kap_real (k r : ℕ) :
    (B.kap k r : ℝ) = (4 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 2 * r) / 3 + k * ((r : ℝ) ^ 2 + r) := by
  have hs : B.kap k r = ∑ j ∈ Finset.range r, 2 * (2 * (j + 1) + k) * (j + 1) := by
    unfold B.kap Mdim
    rw [Fin.sum_univ_eq_sum_range (fun a => 2 * (2 * (r - a) + k + 1 - 1) * (r - a)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show r - (r - 1 - j) = j + 1 by omega]
    rfl
  rw [hs]
  clear hs
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.cast_add, ih]; push_cast; ring

def iF {D : D7} (X : HidaSetting D) : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    ((X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply] at h'
      exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h'),
     fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem disc_rd (D : D7) (X : HidaSetting D) : |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f := by
  refine Formalism.L2.SG.Pf.Carrier.EnergyMS.discRd_of (fun D X => ?_) finrank_E D X
  have hE : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.E X.ιE
  have hF : NumberField.discr X.B.I.F = NumberField.discr D.host.F :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.F (iF X)
  rw [hE, hF, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  push_cast
  rw [abs_pow]

theorem covariance_formula : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  intro D X Y θ C u hθ
  set ρ : ℝ := 2 * D.host.v with hρ
  have hρ1 : 1 ≤ ρ := Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D
  have hρ0 : 0 < ρ := by linarith
  have hrd : D.host.rdE = ρ := by rw [hρ]; unfold Formalism.BasicNotions.Host.v; ring
  have hfr : frS D = ((ρ⁻¹ : ℝ) : ℂ) := by
    unfold frS Formalism.BasicNotions.Host.ka
    congr 1
    have hv : D.host.v ≠ 0 := by intro h; rw [hρ, h] at hρ0; simp at hρ0
    rw [hρ]
    field_simp
  set c : ℝ≥0∞ := Formalism.MainNotions.S.kapN D θ * ENNReal.ofReal (((ρ⁻¹) ^ B.kap D.R.k D.R.rS)⁻¹) with hcdef
  have hloc : ∀ (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F), vOf X τ = v →
      Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ v = c • refNX X u v := by
    rintro τ v rfl
    obtain ⟨-, h2, hg, hcol⟩ := C.isT τ
    rw [hfr] at hcol
    exact place_eq (nX X) _ (eV X _) (ProductExactness.pV X _) (X.wfr u _) (ProductExactness.zV X u _) (ProductExactness.Tw_pos u) (fX_ee X _) (fX_ff X _)
      (fX_ef X _) (fX_ww X u _) (fX_ew X u _) (fX_fw X u _) (fX_ez X u _) (fX_fz X u _) (frame_real_z_z_eq_neg X u _) (fX_zw X u _)
      (C.Q τ) (C.Qi τ) h2 hg (inv_pos.2 hρ0) (fun a => hcol a a rfl) _
  have hv : Formalism.L2.SG.Pf.AmpWinGlob.muNv C = fun v => c • refNX X u v :=
    funext fun v => hloc (X.pl v) v (X.pl.symm_apply_apply v)
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
        SigmaFinite (Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ w) := by
      rintro τ w rfl
      exact Formalism.L2.SG.Pf.AmpWinLoc.sf_muNl C τ hθ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  have : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have hcov : Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) =
      Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) (Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hce : c = ENNReal.ofReal (ρ ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * ρ ^ (B.kap D.R.k D.R.rS : ℝ)) := by
    rw [hcdef, inv_pow, inv_inv, Real.rpow_natCast, ENNReal.ofReal_mul (by positivity)]
    rfl
  have href := covol_refN (covolN_of_coordCovol (coordCovol_of kapLaw_holds NOf.nofib_holds CovB.blockCovol_holds))
    refNBox_holds X u u (Y.FN u) (Y.FN_fund u)
  have hcard : Fintype.card (InfinitePlace X.B.I.F) = Fintype.card D.what₂.Tau := Fintype.card_congr X.pl
  have hf : D.R.f = Fintype.card D.what₂.Tau := D.what₂.card_Tau.symm
  unfold Formalism.L2.SG.LoopTerm.covN
  rw [hcov, hv, pi_smul _ (by rw [hce]; exact ENNReal.ofReal_ne_top), Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    href, disc_rd D X, hrd, hf, hcard, hce, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ← Real.rpow_natCast ρ, ← Real.rpow_mul hρ0.le, mul_comm ((Fintype.card D.what₂.Tau : ℕ) : ℝ), Real.rpow_mul hρ0.le,
    Real.rpow_natCast (ρ ^ Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k), ← mul_pow]
  congr 1
  have e : Formalism.L2.SG.Pf.LoopBCovN.eN D = -((D.R.rS : ℝ) * D.R.k) + (B.kap D.R.k D.R.rS : ℝ) +
      Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k := by
    rw [kap_real]
    unfold Formalism.L2.SG.Pf.LoopBCovN.eN Formalism.L2.SG.Pf.LsNc5.covolumeExponent
    ring
  rw [e, Real.rpow_add hρ0, Real.rpow_add hρ0]
  ring

end Formalism.MainStatements.RowRest
end
end

-- bundled from CompanionTheory.AutomorphicTheory.UniformLocalFormulas.HilbertSchmidtDiagonalInvariant
section
noncomputable section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
  Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocJEq Formalism.L2.SG.Pf.Carrier

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem muG_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Smap C τ γ) = muGB X (C.Q τ) (C.Qi τ) τ := by
  obtain ⟨h1, -, -⟩ := y_facts C τ
  set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ h1 with hy'
  have hr : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  have hm : Measurable fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := (AmpWinLoc.eT_emb C τ (vOf X τ)).measurable
  have e : Smap C τ γ = (fun z => (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ∘
      (fun z => z * y') ∘ fun z => γ⁻¹ * z := by
    funext z
    show Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) =
      Matrix.of.symm (C.Qi τ * (umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)
    congr 1
    simp only [Matrix.mul_assoc]
    rw [(C.isT τ).1, Matrix.mul_one]
  rw [e, ← Measure.map_map hm ((measurable_mul_const y').comp (measurable_const_mul γ⁻¹)),
    ← Measure.map_map (measurable_mul_const y') (measurable_const_mul γ⁻¹), map_mul_left_eq_self, map_mul_right_eq_self]
  rfl

theorem hs_J (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (trG (C.Q τ) (C.Qi τ) γ)) =
      AmpWin.kap u u' C hB τ * hs2 (JvX X u u' (vOf X τ) γ) := by
  rw [← muG_smap C τ γ, locJ_map_eq C hB u u' τ γ _ (integrand_aesm C hB u u' τ γ _),
    ← OOCoreHilbertSchmidt.hsNormSq_eq_hilbertSchmidt_sq]
  exact LTL.hsNormSq_smul _ _

theorem zhat_tr (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (trG (C.Q τ) (C.Qi τ) γ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) a b := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (trG (C.Q τ) (C.Qi τ) γ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat γ *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm trG hJ
    rw [← hH, ← LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ * (C.Qi τ * uMat γ * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat γ * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, LTL.Q_fvec C u τ a, LTL.Q_fvec C u' τ b, Matrix.mulVec_smul, LTL.hJ_smul_real, RelPtR.rv_crd_fvec,
    RelPtR.rv_crd_fvec]
  rfl

theorem hilbert_schmidt_diagonal_invariant (X : HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) {cv : Fin (D.R.rS + 1) → ℂ}
    (hc : cv ∈ GoodV (D := D) u u') {g g' : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv)
    (hg' : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g') = Matrix.diagonal cv) :
    hs2 (JvX X u u' v g') = hs2 (JvX X u u' v g) := by
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u') cv hc.1 hc.2 g g' hg hg'
  rw [heq]
  exact EnergyPfLoc.hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

def lamB (D : D7) (a : Fin D.R.rS) : ℝ := (D.host.rdE ^ (2 * (D.R.rS - a.val)))⁻¹

theorem rd_pos (D : D7) : 0 < D.host.rdE := EnergyConst.rdE_pos'

theorem lamB_pos (D : D7) (a : Fin D.R.rS) : 0 < lamB D a := inv_pos.2 (pow_pos (rd_pos D) _)

theorem rho_sq (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) : rhoF D a * rhoF D a = lamB D ⟨a.val, h⟩ := by
  unfold rhoF lamB
  rw [← Real.rpow_add (rd_pos D), ← Real.rpow_natCast, ← Real.rpow_neg (rd_pos D).le]
  congr 1
  push_cast [Nat.cast_sub h.le]
  ring

theorem rho_pos (D : D7) (a : Fin (D.R.rS + 1)) : 0 < rhoF D a := Real.rpow_pos_of_pos (rd_pos D) _

theorem place_pt (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    {sec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) sec)
    {cv : Fin (D.R.rS + 1) → ℂ} (hc : cv ∈ GoodV (D := D) u u') {g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}
    (hg : Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat g) = Matrix.diagonal cv) :
    hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS
      (fun a => ((lamB D a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩) (sec (cv ⟨D.R.rS, by omega⟩)))) =
      AmpWin.kap u u' C hB τ * hs2 (JvX X u u' (vOf X τ) g) := by
  obtain ⟨hz, hT⟩ := zTr C u τ
  obtain ⟨hz', hT'⟩ := zTr C u' τ
  have hζ : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) <
      Complex.normSq (cv ⟨D.R.rS, by omega⟩) := by
    have h := hc.2
    rw [EnergyCV.gv_diag] at h
    have h2 := (pos_iff_pos_of_mul_pos h).1 (lt_of_le_of_ne (sq_nonneg _) fun h0 => by rw [← h0, zero_mul] at h; exact lt_irrefl _ h)
    rw [hT, hT', Complex.normSq_eq_norm_sq]
    exact sub_pos.1 h2
  obtain ⟨hμ, hh⟩ := hsec.2 _ hζ
  set q : Fin D.R.rS → ℂ := fun a => ((lamB D a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩ with hq
  have hq0 : ∀ a, q a ≠ 0 := fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (lamB_pos D a).ne') (hc.1 _)
  set m := Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q (sec (cv ⟨D.R.rS, by omega⟩)) with hm
  have hmU : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.QuantumDeterminants.bigCellMem _ _ q _ hq0 hμ
  set g' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (transp_mem C τ hmU) with hg'
  have htr : trG (C.Q τ) (C.Qi τ) g' = m := by
    show C.Qi τ * (C.Q τ * m * C.Qi τ) * C.Q τ = m
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (C.isT τ).1, Matrix.one_mul, Matrix.mul_assoc, (C.isT τ).1, Matrix.mul_one]
  have hZ : Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat g') = Matrix.diagonal cv := by
    ext a b
    have h1 := zhat_tr C u u' τ g' a b
    rw [htr, hm, Formalism.QuantumDeterminants.bigCellZhat _ _ _ _ _ _ hz hz'] at h1
    have hρ : ((rhoF D a * rhoF D b : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (rho_pos D a) (rho_pos D b)).ne'
    refine mul_left_cancel₀ hρ ?_
    rw [← h1]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      split_ifs with ha
      · rw [rho_sq D a ha]
      · have hal : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
        subst hal
        rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ hz hz', hh, LTL.rhoF_last]
        simp only [mul_one, Complex.ofReal_one, one_mul]
        rfl
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, mul_zero]
  rw [← htr, hs_J C hB u u' τ g', hilbert_schmidt_diagonal_invariant X u u' _ hc hg hZ]

def Kpl (D : D7) : ℝ := 2 ^ (D.R.rS + 1) * ∏ a : Fin D.R.rS, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k D.R.rS a - 1)))⁻¹

theorem energy_prod (hB : WuBessel C) (u u' : D.what₂.Word)
    {sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (sec τ)) :
    ENNReal.ofReal (∏ τ, AmpWin.kap u u' C hB τ) * intCe X u u' 1 =
      ENNReal.ofReal (Kpl D) ^ D.R.f * ∏ τ, MMv D u u' (locS hB u u' τ) (sec τ) := by
  choose h hm hs using EnergyPfLoc.stepSecX_holds D X u u'
  have hL : EnergyPf.LocRep X u u' fun v cv => hs2 (JvX X u u' v (h v cv)) := by
    refine ⟨fun v => ⟨(EnergyPfLoc.jvX_meas X u u' v).comp (hm v), fun cv => EnergyPfLoc.hilbertSchmidt_sq_nonneg _⟩, fun c hc v => ?_⟩
    have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hs w (c w) (hc w)⟩
    have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
      unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
    exact hilbert_schmidt_diagonal_invariant X u u' v (hc v) (hs v (c v) (hc v)) (hh v)
  have hk0 : ∀ τ, 0 ≤ AmpWin.kap u u' C hB τ := fun τ => Complex.normSq_nonneg _
  have hpl : ∀ τ, ENNReal.ofReal (AmpWin.kap u u' C hB τ) *
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D := D)) =
      ENNReal.ofReal (Kpl D) * MMv D u u' (locS hB u u' τ) (sec τ) := by
    intro τ
    have h1 := EnergyCV.cv_inst u u' D.R.rS rfl (lamB D) (lamB_pos D) fun q =>
      hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q.1 (sec τ q.2)))
    refine Eq.trans ?_ h1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (goodV_meas u u') fun cv hcv => ?_
    simp only []
    rw [place_pt C hB u u' τ (hsec τ) hcv (hs _ cv hcv), ← ENNReal.ofReal_mul (hk0 τ)]
    congr 1
    ring
  rw [EnergyNF.intCe_eq_prodE _ hL, ENNReal.ofReal_prod_of_nonneg fun τ _ => hk0 τ,
    ← Fintype.prod_equiv X.pl.symm (fun τ => ∫⁻ cv in GoodV u u',
      ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D := D))) _ (fun τ => rfl),
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun τ _ => hpl τ, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, D.what₂.card_Tau]

theorem kpl_pow (D : D7) : Kpl D ^ D.R.f = 2 ^ (D.R.f * (D.R.rS + 1)) *
    (Formalism.FourierDecayAlt.PN.abelian₂ D.host.rdE D.R.rS D.R.k D.R.f *
      D.host.rdE ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)) := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hrd := rd_pos D
  set r := D.R.rS
  set S : ℕ := ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + D.R.k) with hS
  have h1 : ∏ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ = D.host.rdE ^ S := by
    have e : ∀ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ =
        D.host.rdE ^ (4 * (r - 1 - a.val + 1) * (2 * (r - 1 - a.val + 1) + D.R.k)) := fun a => by
      have ha : r - 1 - a.val + 1 = r - a.val := by have := a.2; omega
      unfold lamB Formalism.QuantumDeterminants.Mdim
      rw [inv_pow, inv_inv, ← pow_mul, ha, Nat.add_sub_cancel]
      congr 1
      ring
    rw [Finset.prod_congr rfl fun a _ => e a, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun a => 4 * (r - 1 - a + 1) * (2 * (r - 1 - a + 1) + D.R.k)) r,
      Finset.sum_range_reflect (fun j => 4 * (j + 1) * (2 * (j + 1) + D.R.k)) r]
  have h3 : (3 : ℝ) * S = 4 * r * (r + 1) * (2 * r + 1) + 6 * D.R.k * r * (r + 1) := by
    exact_mod_cast EnergyKM.sum_closed r D.R.k
  unfold Kpl Formalism.FourierDecayAlt.PN.abelian₂
  rw [h1, mul_pow, ← pow_mul, ← pow_mul, mul_comm (r + 1) D.R.f]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hrd]
  congr 1
  push_cast [Nat.cast_sub hk]
  linear_combination ((D.R.f : ℝ) / 3) * h3

theorem kpl_pos (D : D7) : 0 < Kpl D :=
  mul_pos (by positivity) (Finset.prod_pos fun a _ => inv_pos.2 (pow_pos (lamB_pos D a) _))

end Formalism.MainStatements.RowRest
end
end

