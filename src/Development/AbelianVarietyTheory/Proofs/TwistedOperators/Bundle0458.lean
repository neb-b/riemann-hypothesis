module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hθall⟩ := h
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, hmall⟩ := hAall A hA
  have e := hmall m hm
  have e' := ((h'.2.2 θ hθ).2 A hA).2 m hm
  have hμ' := h'.1
  have hB : ∀ ρ : D.what₂.Tau, ∃ B : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2),
      MeasurableSet B ∧ m ρ B ≠ 0 ∧ m ρ B ≠ ⊤ := by
    intro ρ
    obtain ⟨j1, j2, j3, -, j5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    haveI := hg ρ (m ρ) (hm ρ)
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
    exact ⟨C, hC.measurableSet, (by first | exact (Measure.measure_pos_of_mem_nhds (m ρ) hC1).ne' | exact (measure_pos_of_nonempty_interior (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'), hC.measure_lt_top.ne⟩
  choose B hBm hB0 hBt using hB
  set S := {h : GA D V | Lev.finE V h ∈ K ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hS : μ S = ∏ ρ, m ρ (B ρ) := e B hBm
  have hS' : μ' S = ∏ ρ, m ρ (B ρ) := e' B hBm
  have hp0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  have hpt : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hBt ρ
  have hc := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hcS : μ' S = (Measure.haarScalarFactor μ' μ : ENNReal) * μ S := by
    conv_lhs => rw [hc]
    rfl
  rw [hS, hS'] at hcS
  have hc1 : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hp0 hpt).1 (hcS.symm.trans (one_mul _).symm)
    exact this
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  intro D T L sc G M M' X K h h'
  unfold GlobalTheory.FunObj.Vol.IsAt at h h'
  split_ifs at h h'
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1

end GlobalTheory.HaarNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergRootSmulFiniteRationalLatticeDecomp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MultLatDecomp


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem heisO_eq_root_smul_finRat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf n hn w hw
  classical
  have hinf : w.map (infPart D) = 0 := by
    have h1 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hw
    funext i j
    have h2 : infPart D ((n • w) i j) = 0 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, map_nsmul] at h2
    have hn' : (n : D.host.F) ≠ 0 := by exact_mod_cast hn.ne'
    have h3 : (n : D.host.F) • infPart D (w i j) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h2
    show infPart D (w i j) = 0
    rw [← inv_smul_smul₀ hn' (infPart D (w i j)), h3, smul_zero]
  obtain ⟨M, u, hu, hM⟩ := GlobalTheory.LatVac.approx hS hT w
  have hw_eq : w = GlobalTheory.VacUnique.finRat S T M + u := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · have h1 : infPart D (w i j) = 0 := congrFun (congrFun hinf i) j
      have h2 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 :=
        congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add (f := _), h1, h2, GlobalTheory.LatVac.infPart_of_mem hu, add_zero,
        sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add (f := _), hM, sub_eq_zero]
      rfl
  have hmem : GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    have e : GlobalTheory.VacUnique.finRat S T (n • M) = n • w - n • u := by
      rw [map_nsmul, hw_eq, smul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem hw (nsmul_mem hu n)
  obtain ⟨ε, hε, hεf⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).2.2 f hf u hu
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ (GlobalTheory.VacUnique.finRat S T M) u f
  rw [hεf f hf, GlobalTheory.LatVac.heisO_smul] at h1
  have hinv : ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) = 1 := by
    rw [← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one]
  have hX : ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) =
      ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) := by
    rw [← ψ.map_add_eq_mul, symplOH, ← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  have hY : ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have e : n • symplO S T (GlobalTheory.VacUnique.finRat S T M) u = symplO S T (GlobalTheory.VacUnique.finRat S T (n • M)) u := by
      change n • GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T M) u =
        GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T (n • M)) u
      rw [map_nsmul (GlobalTheory.VacUnique.finRat S T), map_nsmul (GlobalTheory.LatVac.symplHom S T), AddMonoidHom.nsmul_apply]
    rw [e]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hmem hu
  have e1 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n = 1 := by
    rw [hX]; exact hY
  refine ⟨M, ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u), ⟨2 * n, by omega, ?_⟩, hmem, ?_⟩
  · calc (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n)
        = (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n) *
          (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n := by
          rw [e2, mul_one]
      _ = (ε ^ 2) ^ n * ((ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) *
          ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ 2) ^ n := by ring
      _ = 1 := by rw [e1, hinv]; simp
  · rw [hw_eq, mul_comm, mul_smul, h1, smul_smul, hinv, one_smul]

end GlobalTheory.MultLatDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFiniteRationalRealGaussian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTrans

theorem entry_tr (zz xx : ℂ) (r : ℝ) :
    -(Real.pi * Complex.I) * (-((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ (zz + xx) * -xx)).re : ℝ) : ℂ)) +
      -((Real.pi * r : ℝ) : ℂ) * ((‖zz + xx‖ ^ 2 : ℝ) : ℂ) =
    -((Real.pi * r : ℝ) : ℂ) * ((‖zz‖ ^ 2 : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * (2 * (r : ℂ) * (zz * starRingEnd ℂ xx)) - (Real.pi : ℂ) * (2 * (r : ℂ) * (xx * starRingEnd ℂ xx)) / 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem heisO_finRat_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hf Φ hΦ M X hX w hw
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨z, rfl⟩ : ∃ z, GlobalTheory.FockCompare.iotaW σ T S z = w := ⟨_, hch.iota_pi hw⟩
  have e : GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T M =
      ratW T S M + GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M) := by
    rw [GlobalTheory.VacUnique.ratW_eq hch, AddMonoidHom.map_sub]; abel
  show ψ (symplOH S T _ (GlobalTheory.VacUnique.finRat S T M)) * f (_ + GlobalTheory.VacUnique.finRat S T M) = _
  rw [GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T M) hw, AddChar.map_zero_eq_one, one_mul, e,
    hf.quasi, AddChar.map_neg_eq_inv, _root_.GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T _ _ (Or.inr (hch.real_iota T S _)),
    GlobalTheory.VacUnique.piW_ratW hθ, hch.pi_iota, ← Complex.exp_neg,
    hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO]
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) with hZ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M)) = Z + X := by
    rw [hZ, GlobalTheory.ThetaLawOF.zCo_iota hch, GlobalTheory.ThetaLawOF.zCo_iota hch, hX]; funext τ a b
    show ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) - Matrix.of (GlobalTheory.VacUnique.infRat S T M τ)) * GlobalTheory.FockPos.frAt frS τ) a b = _
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact sub_eq_add_neg _ _
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T M) (z - GlobalTheory.VacUnique.infRat S T M) =
      ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re := by
    rw [GlobalTheory.ThetaLawOF.omO_frame frS frT hS hT, ← hz2, GlobalTheory.ThetaLawOF.zCo_iota hch]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX]
    simp only [neg_neg]
  rw [hz2, hom]
  have kE : Complex.exp (-(-(Real.pi * Complex.I) * ((∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re : ℝ) : ℂ))) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry_tr (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    simp only [Pi.add_apply] at h ⊢
    push_cast at h ⊢
    linear_combination h
  rw [← mul_assoc, kE]
  ring

end GlobalTheory.MovedTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdaptedVectorSystemECoZCo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

def eCo (E : ∀ j, ℕ → (D.sp.Y j).V) (j i : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (E j i))

def zCo (z : ∀ j, (D.sp.Y j).V) (j : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (z j))

theorem normalFr_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) {j : ℕ} (hj : j < D.R.m) {i : ℕ}
    (hi : i < D.R.m - 1 - j) (r : Fin (D.sp.Y j).rank) :
    (D.sp.Y j).frame.repr (normalFr D j (E j) (Ev j) (z j) i) r =
      nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r := by
  have hpar := even_iff_odd_c hj
  have hb : 0 < bI D j := by unfold bI; omega
  rw [nfScal_kap j hb i]
  unfold normalFr adaptedVector nAux
  by_cases h1 : i < (D.R.m - 1 - j) / 2
  · have hb' : ¬ bI D j ≤ i := by unfold bI; omega
    simp only [if_pos h1, if_neg hb', one_mul]
    rfl
  · by_cases h2 : Even j ∧ i = (D.R.m - 1 - j) / 2
    · have hc : (D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2 := ⟨hpar.1 h2.1, h2.2⟩
      have hb' : ¬ bI D j ≤ i := by unfold bI; omega
      simp only [if_neg h1, if_pos h2, if_pos hc, if_neg hb', one_mul]
      rfl
    · have h3 : ¬ ((D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2) := fun h => h2 ⟨hpar.2 h.1, h.2⟩
      have hb' : bI D j ≤ i := by
        unfold bI
        by_cases hc : (D.R.m - 1 - j) % 2 = 1
        · have : i ≠ (D.R.m - 1 - j) / 2 := fun h => h3 ⟨hc, h⟩
          omega
        · omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_pos hb', map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl

theorem normalFr_zero_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) (hz0 : z 0 = D.sp.zm)
    {i : ℕ} (hi : i < D.R.m - 1) :
    ⇑((D.sp.Y 0).frame.repr (normalFr D 0 (E 0) (Ev 0) (z 0) i)) = frame0 (D := D) i := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hρ : nAux D 0 / 2 = D.R.rS := by unfold nAux Ranks.rS; omega
  unfold normalFr frame0
  rw [hρ]
  by_cases h1 : i < D.R.rS
  · rw [if_pos h1, dite_eq_left h1, (hE0 i h1).1]
  · rw [if_neg h1, dite_eq_right h1]
    by_cases h3 : i = D.R.rS
    · rw [if_pos ⟨(Nat.even_iff.2 rfl : Even 0), h3⟩, if_pos h3, hz0]
    · rw [if_neg (fun h => h3 h.2), if_neg h3, if_pos (Nat.even_iff.2 rfl : Even 0)]
      have h5 : 2 * D.R.rS - i < D.R.rS := by unfold Ranks.rS at *; omega
      have h6 : nAux D 0 - 1 - i = 2 * D.R.rS - i := by unfold nAux Ranks.rS at *; omega
      rw [dite_eq_left h5, h6, (hE0 _ h5).2]

theorem isAdaptedVectorSystem_eCo_zCo (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) : IsAdaptedVectorSystem (eCo E) (eCo Ev) (zCo z) := by
  intro j hj
  obtain ⟨hA, hB, hC⟩ := hAux j hj
  have hpar := even_iff_odd_c hj
  simp only [nAux] at hA hB hC
  simp only [eCo, zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
  refine ⟨fun i hi l hl => ⟨?_, ?_, ?_⟩, fun hc => ?_, fun x i' hi' => ?_⟩
  · refine hT_swap _ _ (hA i hi l hl).2.2 ?_
    split_ifs <;> simp
  · exact (hA l hl i hi).1
  · exact (hA l hl i hi).2.1
  · obtain ⟨h1, -, h3⟩ := hC (hpar.2 hc)
    exact ⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩⟩
  · unfold adaptedVector
    split_ifs with h1 h2
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hB _ h1 x).1
    · simp only [zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hC (hpar.2 h2.1)).2.1 x
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      refine (hB _ ?_ x).2
      by_cases hc : (D.R.m - 1 - j) % 2 = 1
      · have : i' ≠ (D.R.m - 1 - j) / 2 := fun h => h2 ⟨hc, h⟩
        omega
      · omega

end GlobalTheory.NormalFramesStd

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

theorem colsAt' (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    {j : ℕ} (hj : j < D.R.m) (β : GL (Fin (D.sp.Y j).rank) (EAf D)) (P : Formalism.L2.Host.PiBar D.host)
    {l : Fin 2} {PP : Pl D.host.E} (hl : P.Div l PP)
    (hA : AgreeAt PP β.val (chainMat D j (γ j) (E j) (Ev j) (z j) (D.host.g l)))
    {ei : AE D} (hei : Formalism.L2.NTheta.IsIdemAt ei PP) :
    (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
        (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
    ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
  refine ⟨fun i hi col hcol r => ?_, fun col l' hcl r => ?_⟩
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rw [if_neg (by omega), if_pos (by unfold nAux; omega), absNorm_of_div P hl,
      show (col : ℕ) - D.R.k = i by omega, normalFr_repr' E Ev z hj hi r]
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hl' : l' = ⟨col, (idx_lt hj col).1 h1⟩ := Fin.ext h2
      subst hl'
      rw [if_pos h1, colX_eq j _ col ((idx_lt hj col).1 h1)]
    · have h3 : ¬ (col : ℕ) < D.R.k := by omega
      have h4 : ¬ (col : ℕ) < D.R.k + nAux D j := by unfold nAux; omega
      have hl' : l' = ⟨(col : ℕ) - nAux D j, (idx_lt hj col).2 h4⟩ := Fin.ext (by simp only [nAux]; omega)
      subst hl'
      rw [if_neg h3, if_neg h4, colX_eq j _ _ ((idx_lt hj col).2 h4)]

theorem normalFrames_of_stdShape : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) → ∀ (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Formalism.IndefR.Lev.EAf D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V), (∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)) → (∀ j, j < D.R.m → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) → (∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) → z 0 = D.sp.zm → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.StdShape L γ E Ev z → (∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z' : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E), NormalFrames (betaYOf L.βY) e ev z' κ s L.Pg L.Pg ∧ NormalFrame0 (betaYOf L.βY 0) L.Pg L.Pg) ∧ XBasesG L.Pg L.βY := by
  intro D T L hPg γ E Ev z hγ hAux hE0 hz0 hSh
  have hshape : ∀ j < D.R.m, ShapeY L j (γ j) (E j) (Ev j) (z j) (betaYOf L.βY j) := fun j hj =>
    shape_betaYOf L γ E Ev z L.βY j hj.le (hSh.1 j hj (hAux _ (lt_of_le_of_lt (min_le_left _ _) hj)))
  have hcols : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
            (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
      ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
    intro j hj PP hPP ei hei
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    exact colsAt' γ E Ev z hj _ L.C.P hl ((hshape j hj).1 l PP hl) hei
  have hxspan : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
        XSpanAt j (betaYOf L.βY j).val ei col := by
    intro j hj PP hPP ei hei col hcol
    have hc := (hcols j hj PP hPP ei hei).2
    rcases hcol with h | h
    · exact ⟨_, hc col ⟨col, (idx_lt hj col).1 h⟩ (Or.inl ⟨h, rfl⟩)⟩
    · exact ⟨_, hc col ⟨(col : ℕ) - (D.R.m - 1 - j), (idx_lt hj col).2 (by unfold nAux; omega)⟩ (Or.inr ⟨h, rfl⟩)⟩
  have h0m : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  refine ⟨⟨eCo E, eCo Ev, zCo z, kap D, fun _ => 1,
    ⟨isAdaptedVectorSystem_eCo_zCo E Ev z hAux, kap_ne, fun _ => one_ne_zero, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro PP hPP j _ i hi
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    have hb : 0 < bI D j := by unfold bI; omega
    rw [nfScal_kap j hb i]
    split_ifs
    · unfold sgT
      split_ifs
      · rw [Valuation.map_neg, valuation_splitTraceElement_eq_one L.C.P hl]
      · exact valuation_splitTraceElement_eq_one L.C.P hl
    · exact map_one _
  · intro PP hPP ei hei j hj
    refine ⟨fun i hi col hcol r => ?_, hxspan j hj PP hPP ei hei⟩
    rw [if_pos hPP]
    exact (hcols j hj PP hPP ei hei).1 i hi col hcol r
  · intro PP hPP ei hei
    have hc := (hcols 0 h0m PP hPP ei hei).1
    refine ⟨fun i hi col hcol r => ?_, fun col hcol => hxspan 0 h0m PP hPP ei hei col
      (Or.inl (by rw [← Formalism.IndefR.Seed.FrmC.N_zero D]; exact hcol))⟩
    have hi' : i < D.R.m - 1 - 0 := by omega
    rw [if_pos hPP, hc i hi' col (by rw [hcol, Formalism.IndefR.Seed.FrmC.N_zero]) r, ← normalFr_repr' E Ev z h0m hi' r,
      normalFr_zero_repr' E Ev z hE0 hz0 hi]
  · intro j hj
    refine ⟨γ j, by rw [← crdLat_eq_l0X]; exact hγ j hj, fun PP hPP ei hei col l' hcl r => ?_⟩
    exact (hcols j hj PP hPP ei hei).2 col l' hcl r

end GlobalTheory.NormalFramesStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocSubLocGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

structure IsLocSub (τ : D.what₂.Tau) (B : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ B, rTr V (atTau θ V τ g) f ∈ B
  lie : ∀ X ∈ lieAt V τ, ∀ f ∈ B, Rder θ V τ X f ∈ B

def locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {B | ψ ∈ B ∧ IsLocSub θ M τ B}

theorem mem_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : ψ ∈ locGen θ M τ ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isLocSub_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : IsLocSub θ M τ (locGen θ M τ ψ) := by
  constructor
  · intro g hg f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.k g hg f (Submodule.mem_sInf.1 hf B hB)
  · intro X hX f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.lie X hX f (Submodule.mem_sInf.1 hf B hB)

theorem locGen_le {τ : D.what₂.Tau} {ψ : GA D V → ℂ} {B : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ B)
    (hB : IsLocSub θ M τ B) : locGen θ M τ ψ ≤ B :=
  sInf_le ⟨hψ, hB⟩

end GlobalTheory.CuspGKId

end
end

