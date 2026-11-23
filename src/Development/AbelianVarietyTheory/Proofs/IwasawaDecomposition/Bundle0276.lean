module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficients
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem exists_scalar_of_forall_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → Prop)
    (hP : ∀ f g, P f → P g → P (f + g)) (M : Module.End ℂ V) (h : ∀ f, P f → ∃ c : ℂ, ‖c‖ = 1 ∧ M f = c • f) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, P f → M f = c • f := by
  by_cases h0 : ∃ f₀, P f₀ ∧ f₀ ≠ 0
  · obtain ⟨f₀, hf₀, hne⟩ := h0
    obtain ⟨c, hc, ec⟩ := h f₀ hf₀
    refine ⟨c, hc, fun f hf => ?_⟩
    by_cases ha : ∃ a : ℂ, f = a • f₀
    · obtain ⟨a, rfl⟩ := ha
      rw [LinearMap.map_smul, ec, smul_comm]
    · obtain ⟨e, -, ee⟩ := h f hf
      obtain ⟨d, -, ed⟩ := h (f + f₀) (hP _ _ hf hf₀)
      rw [LinearMap.map_add (f := _), ec, ee, smul_add] at ed
      have k : (e - d) • f = (d - c) • f₀ := by
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ed, add_comm]
      have hed : e - d = 0 := by
        by_contra hn
        exact ha ⟨(e - d)⁻¹ * (d - c), by rw [mul_smul, ← k, smul_smul, inv_mul_cancel₀ hn, one_smul]⟩
      rw [hed, zero_smul] at k
      have hdc : d - c = 0 := (smul_eq_zero.1 k.symm).resolve_right hne
      rw [ee, sub_eq_zero.1 hed, sub_eq_zero.1 hdc]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := by
      by_contra hn
      exact h0 ⟨f, hf, hn⟩
    rw [this, LinearMap.map_zero, smul_zero]

theorem schur_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hcomm hiso
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  refine exists_scalar_of_forall_eigen _ (fun f g hf hg => GlobalTheory.OrientedHeis.theta_add hf hg) M fun f hf => ?_
  refine _root_.GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (M f) hf (hM f hf) fun w => ?_
  rw [← hcomm w f hf]
  exact _root_.GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hiso μ 𝓕 hμ h𝓕) _ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w) hf

end GlobalTheory.Mem.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInner
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.TopSchur

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem exists_vec_prod_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {W : Type}
    [AddCommGroup W] [Module ℂ W] (pr : W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (hpr : pr ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical
  have hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0 := by
    intro τ
    by_contra hz
    push_neg at hz
    apply hpr
    have hs : ∀ s : SmT M, s = 0 := by
      intro s
      induction s using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine LinearMap.ext fun w => LinearMap.ext fun s => ?_
    rw [hs s]
    simp
  choose v hv using hτ
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩
  intro h0
  exact hv τ (Subtype.ext h0)

theorem alg_step {d I p q x : ℂ} (hd : d ≠ 0) (hI : d * I = q * x) (hq : q = p) : I = x / d * p := by
  subst hq
  field_simp
  linear_combination hI

theorem dualNumber_unit_mul_decomposition {P c d x : ℂ} (hP : P = d) (hc : c = x / d) (hd : d ≠ 0) : P * c = x := by
  subst hP hc
  field_simp


set_option maxHeartbeats 400000 in
theorem topSchur : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'
  classical
  have hC := _root_.GlobalTheory.CoefDim.finrank_coef_eq_prod D G Pl0 T A Ks R F hB
  haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1
  have hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0 := by
    have := Module.finrank_pos (R := ℂ) (M := R.cX.W)
    exact_mod_cast this.ne'
  have hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ) := by
    rw [hC]; push_cast; rfl
  have key : ∀ v v' : R.MX.Vec,
      IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧
      ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v') ∂(R.νX t) =
      ⟪h, h'⟫_ℂ / (Module.finrank ℂ R.cX.W : ℂ) * ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
    intro v v'
    have hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    have hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    obtain ⟨a, ha⟩ := hr
    obtain ⟨a', ha'⟩ := hr'
    have hA := _root_.GlobalTheory.Mem.SchurW.schurW D G Pl0 T A Ks R F hB t h h' a a'
    obtain ⟨hint, hval⟩ := hA
    have hab := _root_.GlobalTheory.Mem.rieszProd_inner D G Pl0 T A Ks R F hB hP v v' a a' ha ha'
    simp only [ha, ha']
    refine ⟨hint, ?_⟩
    exact alg_step hd0 hval hab
  have hv := exists_vec_prod_ne R.MX R.prX hB.models.prX.1
  obtain ⟨v0, hv0⟩ := hv
  unfold ipMT Mult.ipM
  split_ifs with hex
  · have e1 := (hex.choose_spec v0 v0).2
    have hch : hex.choose * _ = _ * _ := e1.symm.trans (key v0 v0).2
    have hch' := mul_right_cancel₀ hv0 hch
    exact dualNumber_unit_mul_decomposition hcast hch' hd0
  · exfalso
    exact hex ⟨_, fun v v' => key v v'⟩

end GlobalTheory.Mem.TopSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan


set_option maxHeartbeats 10000000 in
theorem span_liftForm_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB _ _ i t
  classical
  have hHV := hB.models.HV i t
  have hjV := hB.models.jV
  have hExt : (R.B.L i t).pres.ExtBij :=
    (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have key : (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      fun x => (R.cV i).ext ((R.B.L i t).pres.extL (GlobalTheory.OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) := by
    funext x
    exact congrArg (R.cV i).ext (hjV i t _)
  have hR : Set.range (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      (R.cV i).ext '' ((R.B.L i t).pres.extL ''
        {f | ∀ u : F.P0, A.leftGroupActionLift i t (u : G) f = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • f}) := by
    rw [key]
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ _).1 ⟨x, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ f).2 hf
      exact ⟨x, rfl⟩
  rw [hR, Submodule.span_image]
  ext Y
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range]
  have hs1 := _root_.GlobalTheory.LiftSpanEig.eigen_span_iff (W := (R.cV i).W) (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL (R.cV i).coef.ρ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (A.leftGroupActionLift i t)
    (R.B.L i t).pres (R.B.L i t).act_tie hExt F.P0 F.ψ0⁻¹
  have hs2a := _root_.GlobalTheory.LevToQ.levtoq D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  have hs2b := _root_.GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    obtain ⟨hAd, hq⟩ := (hs1 Φ).1 hΦ
    refine ⟨?_, hs2b Φ hq⟩
    have h1 : Φ ∈ LinearMap.range (R.HV i t).e := by rw [hHV.2.1]; exact hAd
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨⟨y, rfl⟩, hlev⟩
    have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ y
    rw [hHV.2.1] at h1
    exact ⟨(R.HV i t).e y, (hs1 _).2 ⟨h1, hs2a _ hlev⟩, rfl⟩

end GlobalTheory.LiftSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.BddG

open GlobalTheory.LastSteps GlobalTheory.ColPeriod

theorem homBdd_of_good {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    {n' c' n c m : ℕ} (hc' : c' ≤ m) (hc : c + 1 ≤ m) {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ) :
    HomBdd P m Φ := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  refine ⟨fun x hx => (intHom_iff _).2 fun s l => ?_, fun x y hy => ?_⟩
  · have h1 := mem_homS_sclLat.1 (h.1 x hx) l s
    have hs := s.2
    have e : 0 ≤ (m : ℤ) - (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
      unfold LocE.scE
      dsimp only
      split_ifs <;> omega
    convert h1.mul (intAt_zpow e) using 1
    rw [mul_assoc, ← zpow_add₀ hq, add_sub_cancel, zpow_natCast, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · have h1 : ((qOf P : E) ^ ((m : ℤ) - 1)) • y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l s => ?_
      have hl := l.2
      have e : 0 ≤ (m : ℤ) - 1 + (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
        unfold LocE.scE
        dsimp only
        split_ifs <;> omega
      convert ((intHom_iff _).1 hy s l).mul (intAt_zpow e) using 1
      rw [zpow_add₀ hq, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 := h.2.1 x _ h1
    rwa [smul_smul, zpow_sub_one₀ hq, mul_comm _ (qOf P : E)⁻¹, mul_inv_cancel_left₀ hq, zpow_natCast] at h2

theorem good_omPhi_two {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)) (omPhi Ch sel mu cst i P hal h) := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  unfold lamYat at ha hb
  rw [if_pos hP] at ha hb
  refine good_om_two ?_ _ _ _ ha hb
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

theorem omPhi_bdd_type {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    (hal : AutY X R i) (h : AutY X R (i + 1)) (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  have hg := good_omPhi_two Ch sel mu cst i P hi hP ha hb
  refine ⟨homBdd_of_good (by unfold cOf; omega) (by unfold cOf; omega) hg, fun x hx => ?_⟩
  have := GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (chArg_int (hg.1 x hx))
  rwa [mul_neg, neg_neg] at this

end GlobalTheory.Mem.Col2.BddG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_change : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ (κ : GA D (Yc D k)), ∀ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), ∀ c : ℂ, (∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ) → ∀ y : R.CC t (k + 1), y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) → ∀ φ w g, (R.ioY t k y).1 (R.ItY k φ w) (g * κ) = c * levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' * (R.ioY t k y).1 (R.ItY k φ w) g := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ κ' hκ' c hc y hy φ w g
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  have hio := hch.ioY t k (by omega)
  have e1 := hio.eq y φ w (g * κ)
  have e2 := hio.eq y φ w g
  rw [← e1, ← e2]
  unfold Lift.liftInt

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hy)
  set χ1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) with hχ1
  have hlev : ∀ (u : SmT (R.MY (k + 1))) h, y.1 u (h * κ') = χ1 κ' * y.1 u h := by
    intro u h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := hm.lev v κ' hκ' h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
      ring
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
      ring
  have hleft : ∀ (u : SmT (R.MY (k + 1))), ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, y.1 u (γ * h) = y.1 u h := by
    intro u γ hγ h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (hm.aut v).left γ hγ h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
  have hω := hch.ωY t k hk
  have hpt := hch.ptY t k hk φ
  have hθ1 : ∀ h, thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) =
      c * thetaKO (R.ωY t k) g (h * κ'⁻¹) (R.toRealDat.ptY t k φ) := by
    intro h
    unfold thetaKO
    have e : ((g * κ, h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (g, h * κ'⁻¹) * (κ, κ') := by
      ext <;> simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply, hc φ, map_smul, Pi.smul_apply, smul_eq_mul]
  have hθ2 : ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, thetaKO (R.ωY t k) g (γ * h) (R.toRealDat.ptY t k φ) =
      thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) := by
    intro γ hγ h
    unfold thetaKO
    have e : ((g, γ * h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (1, γ) * (g, h) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have hmod := hP.char.base.models
  have hHF : (R.νY t (k + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · have h3 := hmod.νY t (k + 1) h2
      exact ⟨h3.1.1, h3.2⟩
    · have h3 := hmod.νY' t
      have e : D.R.m - 1 = k + 1 := by omega
      rw [e] at h3
      exact ⟨h3.1.1, h3.2⟩
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Yc D (k + 1))
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Yc D (k + 1))
  haveI := hHF.1
  haveI : (R.νY t (k + 1)).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hHF.1
  set Ψ : GA D (Yc D (k + 1)) → ℂ := fun h => thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) * y.1 w h with hΨ
  have hRI := Formalism.IndefR.Eqv.rightInv_holds (GA D (Yc D (k + 1))) (GQ (Yc D (k + 1))) (R.νY t (k + 1))
    (R.fdY t (k + 1)) hHF.2 Ψ (fun γ hγ h => by simp only [hΨ, hθ2 γ hγ h, hleft w γ hγ h]) κ'⁻¹
  calc ∫ h in R.fdY t (k + 1), thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) * y.1 w h ∂(R.νY t (k + 1))
      = ∫ h in R.fdY t (k + 1), c * χ1 κ' * Ψ (h * κ'⁻¹) ∂(R.νY t (k + 1)) := by
        congr 1
        funext h
        have e := hlev w (h * κ'⁻¹)
        rw [inv_mul_cancel_right] at e
        simp only [hΨ, hθ1 h, e]
        ring
    _ = c * χ1 κ' * ∫ h in R.fdY t (k + 1), Ψ h ∂(R.νY t (k + 1)) := by
        rw [integral_const_mul, hRI.2]

end GlobalTheory.Mem.R3.DTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

end GlobalTheory.TrueGeo.OfModel
end
end

