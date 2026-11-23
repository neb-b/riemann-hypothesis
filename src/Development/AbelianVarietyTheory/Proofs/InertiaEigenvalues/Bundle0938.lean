module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0937
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0013
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0012
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace

noncomputable section

namespace GlobalTheory.BadPlace


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem actO_one_inv_half {D : D7} {S T : HSp D} {e f : AE D} (hef : e * f = e) {γ : GA D T}
    (hγ : GlobalTheory.RawLift.TrivAt T f γ) {y : WO S T} (hy : IsHalf e y) : actO S T 1 γ⁻¹ y = y := by
  have h1 : f • Formalism.L2.Theta.mt T γ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext a b
    have := hγ a b
    rw [Matrix.sub_apply, mul_sub] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.1 this
  have h2 : Formalism.L2.Theta.mt T γ * Formalism.L2.Theta.mt T γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : f • Formalism.L2.Theta.mt T γ⁻¹ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    calc f • Formalism.L2.Theta.mt T γ⁻¹ = (f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) * Formalism.L2.Theta.mt T γ⁻¹ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (f • Formalism.L2.Theta.mt T γ) * Formalism.L2.Theta.mt T γ⁻¹ := by rw [h1]
      _ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by rw [Matrix.smul_mul, h2]
  have h4 : e • Formalism.L2.Theta.mt T γ⁻¹ = e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    rw [← hef, ← smul_smul, h3, smul_smul]
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = y := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hy a b
  have hone : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    simp only [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  unfold actO
  rw [hone, Matrix.mul_one]
  calc HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      = HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by rw [hy']
    _ = HMul.hMul (e • Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = HMul.hMul (e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [h4]
    _ = y := by rw [Matrix.smul_mul, Matrix.one_mul, hy']

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]


set_option maxHeartbeats 2000000 in
theorem coef_bad_vanish : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hC P hP e f hPI γ _ hTr k hk hlev
  obtain ⟨ea, Tm, c, hIS, hSe, hee, hf, hψ, hSV, hSW, hv0, hvl, hTm, hSB2, hSB1, hvP, hωk⟩ :=
    _root_.GlobalTheory.BadPlace.vec_read_at D G Pl0 T A Ks R F hL hF i t P hP e f hPI k hk
  have hdisj := _root_.GlobalTheory.BadPlace.disj_supp D G Pl0 T A Ks R F hL hF i t ea hIS P hP e f hPI k hk hlev
  have hW := (hF i t).datum
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [RealDat.ptP, pureTensorO, pureTensorL_one] at this
  have hef : e * f = e := by
    rw [hf, mul_add, hSe.1, hSe.2.1, add_zero]
  have e1 := GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hC (1, γ⁻¹)
    (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) (hW.om_pres (1, γ * k) _ hth) hth
  rw [← e1, ← Module.End.mul_apply, ← map_mul]
  have e2 : ((1 : GA D (Vc D i)), γ⁻¹) * (1, γ * k) = (1, k) := by
    ext
    · exact mul_one 1
    · exact (inv_mul_cancel_left γ k)
  rw [e2, hωk, thetaInner_smul_left]
  have hz := _root_.GlobalTheory.BadOrth.orth_of_disjoint D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) _ ea e (R.vacP i) Tm μ 𝓕 hψ hSV hSW hIS hSe hee hv0 hvl
    hTm hC _ _ hSB1 hSB2 (fun x x' hxx' h1 h2 => hdisj x x' (by rw [hf]; exact hxx') h1 h2) (R.ωP i t (1, γ⁻¹))
    (fun g hg => hW.om_pres _ _ hg) (fun y hy g hg => by
      rw [hW.om_heis _ _ _ _ hg, actO_one_inv_half hef hTr hy])
  rw [← hvP] at hz
  rw [hz, mul_zero]

end GlobalTheory.BadPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem eigen_law_absolute {M G Γ A V P : Type*} {J : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup P] [Module ℂ P] (io : V →ₗ[ℂ] P) (hinj : Function.Injective io) (val : Submodule ℂ P)
    (hran : LinearMap.range io = val) (act : A → P → P) (ρ : A → V → V) (hact : ∀ g v, act g (io v) = io (ρ g v))
    (E : M → G → V) (mv : Γ → G → J → G) (a : Γ → A) (lam : J → ℂ)
    (hlaw : ∀ f : G → V, (∃ x, E x = f) ↔ ∀ γ h k, f (mv γ h k) = lam k • ρ (a γ) (f h)) (F : G → P) :
    (∃ x, ∀ h, io (E x h) = F h) ↔ (∀ h, F h ∈ val) ∧ ∀ γ h k, F (mv γ h k) = lam k • act (a γ) (F h) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun h => ?_, fun γ h k => ?_⟩
    · rw [← hran, ← hx]
      exact ⟨_, rfl⟩
    · rw [← hx, ← hx, (hlaw _).1 ⟨x, rfl⟩ γ h k, map_smul, hact]
  · rintro ⟨hv, hl⟩
    subst hran
    choose f hf using hv
    obtain ⟨x, hx⟩ := (hlaw f).2 fun γ h k => hinj (by rw [map_smul, ← hact, hf, hf, hl])
    exact ⟨x, fun h => by rw [hx, hf]⟩

theorem _root_.GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → Function.Injective (fockOf Y (used_of_tw H.tw) j u) ∧
  LinearMap.range (fockOf Y (used_of_tw H.tw) j u) = (baseOf Z c w j).formsC (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu
  obtain ⟨hinj, hran⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu
  have hact := UpperTheory.KN.ioP_tprod_intertwines_action D X X0 Y S YS Z c w j H ι hι u hu
  have hlaw := UpperTheory.KN.automorphic_form_iff_rational_level_law D X X0 Y S YS Z c w j H ι hι
  refine ⟨?_, Submodule.ext fun F => ?_⟩
  · intro x y hxy
    have h1 : (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) =
        (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j y) :=
      funext fun h => hinj (congrFun hxy h)
    have h2 : X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j x) =
        X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j y) := by
      have h3 := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).1 h1
      rw [h3]
    rw [extV_formOf, extV_formOf] at h2
    exact (Y.IL.jMt _ (used_of_tw H.tw) j).injective (Subtype.ext h2)
  · have key := eigen_law_absolute (X.R.ioP j (PiTensorProduct.tprod ℂ u)) hinj _ hran (fun g P => (baseOf Z c w j).act g P)
      (fun g v => (X.R.cV j).ρ g v) hact
      (fun x => (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x))
      (fun (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)) =>
        Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) (fun γ => (γ : GA D (Vc D j)))
      (fun k => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ)) hlaw F
    refine Iff.trans ?_ (key.trans (Base.mem_formsC _).symm)
    exact ⟨fun ⟨x, hx⟩ => ⟨x, fun h => congrFun hx h⟩, fun ⟨x, hx⟩ => ⟨x, funext hx⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntireStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  first | (exact @GlobalTheory.RSPole.rs_pole_conj) | (exact GlobalTheory.RSPole.rs_pole_conj) | (intros; apply GlobalTheory.RSPole.rs_pole_conj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.RefPair


set_option maxHeartbeats 1000000 in
theorem thetaPair_of_hasThetaAt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (D : D7) {μt : D.what₂.Tup} {j : ℕ}
    (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (X : RowMod D rep j) (μ η : HChar D.host.E)
    (hΘ : HasThetaAt D Mr X μ η) (σ : D.what₂.FT) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S)
    (hPair : ∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F (D.what₂.thetaT μt j y) ≠ 0)
    (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hπ : IsLocS (n := D.R.nV) S s π) (hτ : IsLocS (rep σ).S s τ) (hU : GlobalTheory.SmGL.IsUnitarisable τ.ρ) :
    GlobalTheory.ThetaGL.ThetaPair (μ.loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w))) := by
  obtain ⟨Ω, _, _, ω, Λ, φ₀, hinv, hread, hloc⟩ := hΘ
  obtain ⟨f, hf, F, hF, hne⟩ := hPair
  have hFmem : Mr.real F ∈ NG.AFall D.host.E D.R.nV Mr.wt.ρ := by
    have : Mr.real F ∈ LinearMap.range Mr.real := LinearMap.mem_range_self _ _
    rw [Mr.real_range] at this
    exact this.1
  let Fp : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Λ φ₀ Fp yp ≠ 0 := by
    rw [← hread F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP μt j) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc : IsComp μ s.w (μ.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc μ s.w, fun _ => rfl⟩
  have hηc : IsComp η s.w (η.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc η s.w, fun _ => rfl⟩
  have hl := hloc s _ _ hμc hηc
  let ℓ0 : Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hl h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin

  have hFiso : (Fp : GAf D.host.E D.R.nV → Mr.wt.W) ∈ NG.isoTyp Mr.wt.ρ S := hF
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV Mr.wt S hS s π hπ c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1

  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (rep σ) s τ hτ c hc hci
  let ℓ2 : ↥(rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add (f := _)])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1

  let T' : π.V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := T1.codRestrict _ hT1.1
  let T'' : τ.V →ₗ[ℂ] ↥X.C := (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) : GAf D.host.E D.R.nV → Mr.wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → Mr.wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a), hT2.1 _⟩ : ↥(rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Λ ∘ₗ ι).compl₂ T').compr₂ (GlobalTheory.PairReadPf.precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (μ.loc s.w) τ.ρ
    (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)))
    ((hBZ _).1 (Fin D.R.r) _ _ τ.smooth τ.irr) hU (GlobalTheory.HeckeComp.smooth_loc μ s.w) b
    (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) :
      GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)) = h := by rw [exh]; exact back _ h
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg]; exact back _ g
  subst eh eg
  have hω := hιeq xh xg hxh hxg Φ Φ' hΦ'
  have key := hinv xh xg (ι Φ) (T' a) (T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh)) a))
    (T'' c') (T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg)) c'))
    (hT'eq xh hxh a) (hT''eq xg hxg c')
  rw [hω] at key
  show Λ (ι Φ') (T' (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)) _ a)) (T'' (τ.ρ _ c')) =
    Λ (ι Φ) (T' a) (T'' c')
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  exact key

end GlobalTheory.RefPair

namespace GlobalTheory.RefPair

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin


end GlobalTheory.RefPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul.Smooth

theorem zint_eq_mul_partialL_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro E _ _ _ a σ σ' ha hσ hσ' T hTs hψ hT hT'
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ ha hσ T hT
  obtain ⟨α', _ℓ', _Φ', _J', _η', π', ω', _φ', hα', hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ' ha hσ' T hT'
  subst hπ hπ'
  obtain ⟨μ₀, hμ₀, 𝓕₁, h𝓕₁⟩ : ∃ (μ : Measure (GA E (m + 1))) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E (m + 1))),
      IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
    haveI : DiscreteTopology (ratGL E (m + 1)).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E (m + 1)
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E (m + 1)).range
    exact ⟨Measure.haar, inferInstance, 𝓕, h𝓕 _⟩
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α' w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let αe' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α' ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hαe' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe' w.1 = α' w := fun w => dif_pos w.2
  have hsatσ : ∀ (ρ : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hs : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe w.1) = sat (CG.mk π) w.1 := fun w => by
    rw [hαe w]; exact hα w
  have hs' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe' w.1) = sat (CG.mk π') w.1 := fun w => by
    rw [hαe' w]; exact hα' w
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hs ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (αe' w)) := fun w hw => by
    rw [hs' ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨b, hb1, hbN, hbC, hbF⟩ := GlobalTheory.T.exists_bump_shintani_alt E m T hψ
  obtain ⟨φ, hφR, hU, hK, hW⟩ := hbF π αe hsat
  obtain ⟨φ', hφR', hU', hK', hW'⟩ := hbF π' αe' hsat'
  obtain ⟨hφ0, hφ0', N, Φ, hN, hΦc, hΦs, hΦr, hΦp, hC2⟩ := GlobalTheory.ZEul.unfolded_bump_eq E m T hTs hψ b hb1 hbN hbC π π' ω ω' hω hω' hωc hωc' αe αe'
    hsat hsat' φ φ' hφR hφR' hU hK hU' hK' hW hW'
  refine ⟨N, Φ, π, π', φ, φ', rfl, rfl, hφR, hφR', hφ0, hφ0', hN, hΦc, hΦs, ?_, ?_⟩
  · intro ℓ hℓ
    have hl : ℓ = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    exact hΦr
  intro μ hμ 𝓕 h𝓕
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.ZEul.exists_fundamentalDomain_NE E (m + 1) μ
  obtain ⟨c, hc, hC1⟩ := GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker E m μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC2 μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.T.exp_integral_differentiable_real_re_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  refine ⟨fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe' w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α' w i : ℂˣ) : ℂ) := by funext w i; rw [hαe' w]
    have hf1 : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1]; exact hfin x hx
    have hf1' : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe' w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1']; exact hfin' x hx
    obtain ⟨hd, hd', e12, e11, e22⟩ := hid x hx hf1 hf1'
    have z12 := (hC1 π π' ω ω' hω hω' hωc hωc' φ φ' hφR hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd').2
    have z11 := (hC1 π π ω ω hω hω hωc hωc φ φ hφR hφR N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd).2
    have z22 := (hC1 π' π' ω' ω' hω' hω' hωc' hωc' φ' φ' hφR' hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd' hd').2
    have A12 := (_root_.GlobalTheory.ZEul.hasSum_rsTerm_finsupp (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe' w.1) x hx hq hf1 hf1').tsum_eq
    have A11 := (_root_.GlobalTheory.ZEul.hasSum_rsTerm_finsupp (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe w.1) x hx hq hf1 hf1).tsum_eq
    have A22 := (_root_.GlobalTheory.ZEul.hasSum_rsTerm_finsupp (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe' w.1) (fun w => αe' w.1) x hx hq hf1' hf1').tsum_eq
    simp only [hs, hs'] at A12 A11 A22
    refine ⟨?_, ?_, ?_⟩
    · rw [z12, e12, A12]; ring
    · rw [z11, e11, A11]; ring
    · rw [z22, e22, A22]; ring

end GlobalTheory.ZEul.Smooth
end
end

