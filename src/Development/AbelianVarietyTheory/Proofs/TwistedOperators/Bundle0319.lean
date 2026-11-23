module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainEigenPartHasParameters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem val_hecke_of_mem_partFull_one {D : D7} {c : Com D} {s : PiLocalization₂ D} (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hu : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D s.V))
    (hR : Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R) (v : SmT s.M) :
    heckeLin s.V R (PiLocalization₂.val u v) = e P d • PiLocalization₂.val u v := by
  have h := ((mem_partFull c.θ s.M _ _ c.S e _).1 hu).2 P d R hR
  have key : heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = e P d • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    apply PiTensorProduct.ext
    ext x
    have := h x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at this ⊢
    convert congrFun this _ using 2 <;> simp [PiTensorProduct.lift_symm]
  exact congrFun (congrArg DFunLike.coe key) v |>.trans rfl

theorem partPar : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  intro hP D c hc j hj s hs u e hu
  obtain ⟨hval, hconj⟩ := _root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hP D c hc j hj s hs
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hlev : ∀ v, ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, (fun g => conj (PiLocalization₂.val u v g)) (g * k) =
      (1 : GA D s.V → ℂ) k * (fun g => conj (PiLocalization₂.val u v g)) g := by
    intro v k hk g
    simp only [(hval u v).2.2.2.1 k hk g, Pi.one_apply, one_mul]
  have hhk : ∀ v P d R, Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R →
      heckeLin s.V R (fun g => conj (PiLocalization₂.val u v g)) = (fun P d => conj (e P d)) P d • (fun g => conj (PiLocalization₂.val u v g)) := by
    intro v P d R hR
    rw [hconj, val_hecke_of_mem_partFull_one u e hu P d R hR v]
    funext g
    simp [map_mul]
  have hne : ∀ v, PiLocalization₂.val u v ≠ 0 → (fun g => conj (PiLocalization₂.val u v g)) ≠ 0 := by
    intro v h0 h
    apply h0
    funext g
    simpa using congrFun h g
  have hiff : ∀ v B, PiLocalization₂.val u v ≠ 0 →
      (ParFun c s (PiLocalization₂.val u v) B ↔ GlobalTheory.LFun.IsSysParamD D c.S s.V.rank (fun P d => conj (e P d)) B) := by
    intro v B h0
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph (hne v h0) (hlev v) (hhk v) B
  have second : ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
    intro w B hw hB
    refine ⟨?_, fun v hv => (hiff v B hv).2 ((hiff w B hw).1 hB)⟩
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun hu0 => ?_, second⟩
  have hu1 : (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu1 (LinearMap.ext hh)
  obtain ⟨C, hC⟩ := (hval u v).2.1
  have hbdd : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj.comp (hval u v).1), fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [(hval u v).2.2.1 γ hγ g]
    · simpa using hC g
  obtain ⟨B, hB, -⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s.V (s.J : Set (GA D s.V)) 1 c.S hsph
    _ hbdd (hne v hv) (hlev v) (fun P d => conj (e P d)) (hhk v)
  have hpf : ParFun c s (PiLocalization₂.val u v) B := hB
  exact ⟨B, second v B hv hpf⟩

end GlobalTheory.EvenOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.EvenOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  intro hCRD D c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := hpar v hv
  obtain ⟨h4a, _⟩ := _root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩ := h4a u v
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, Pi.one_apply, one_mul]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.ParamEigen.eig_of_param D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B
  obtain ⟨B', hB', hbd⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenMetric

variable {D : D7}

theorem finDim : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, FinDim D := by
  intro hP D c hc j _ s hs
  obtain ⟨U, hU, hUJ⟩ := hs.isOpen
  have : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) 1) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf ⟨U, hU, fun k hk hf => ⟨hUJ k hk hf, rfl⟩⟩
  exact Module.Finite.map _ _

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  set J : Set (GA D s.V) := (s.J : Set (GA D s.V))
  set χ : GA D s.V → ℂ := 1
  have hS : SchurMult c.θ s.M J χ s.ν s.fd := GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  obtain ⟨hI1, hI2⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M J χ s.ν s.fd hc.inf hs.haar hs.fund hS
    (GlobalTheory.GardingVec.sm_ne_bot D s.V s.par s.M)
  let T : s.CC c → MMap s.M := fun x => PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
  have hT : ∀ x : s.CC c, T x ∈ Mult c.θ s.M J χ := fun x => (mem_multT c.θ s.M J χ _).1 x.2
  have hTadd : ∀ x y : s.CC c, T (x + y) = T x + T y := fun x y => by
    simp only [T, Submodule.coe_add, map_add (f := _)]
  have hTsmul : ∀ (a : ℂ) (x : s.CC c), T (a • x) = a • T x := fun a x => by
    simp only [T, Submodule.coe_smul, map_smul]
  have hlin : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T y + a • T y') = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => (hI1 _ (hT x) _ (hT y) _ (hT y') a).1
  have hsym : ∀ x y : s.CC c, ipM s.M s.ν s.fd (T y) (T x) = star (ipM s.M s.ν s.fd (T x) (T y)) :=
    fun x y => (hI1 _ (hT x) _ (hT y) _ (hT y) 0).2
  have hzero : ∀ x : s.CC c, ipM s.M s.ν s.fd (T x) (T 0) = 0 := fun x => by
    have h := hlin x 0 0 1
    rw [one_smul, one_mul, show T 0 + T 0 = T 0 by simp [T]] at h
    linear_combination -h
  have hlin' : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T (y + a • y')) = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => by rw [hTadd, hTsmul]; exact hlin x y y' a
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => ipM s.M s.ν s.fd (T y) (T x))
      (fun x x' y => by simpa using hlin' y x x' 1)
      (fun a x y => by
        have h := hlin' y 0 x a
        rw [zero_add, hzero, zero_add] at h
        simpa using h)
      (fun x y y' => by
        rw [hsym x (y + y'), hsym x y, hsym x y']
        have h := hlin' x y y' 1
        rw [one_mul, one_smul] at h
        rw [h, star_add])
      (fun a x y => by
        rw [hsym x (a • y), hsym x y]
        have h := hlin' x 0 y a
        rw [zero_add, hzero, zero_add] at h
        rw [h, star_mul', smul_eq_mul, starRingEnd_apply])
  have hip : ∀ x y, ip x y = ipM s.M s.ν s.fd (T y) (T x) := fun _ _ => rfl
  have hpair : ∀ x y : s.CC c, ∀ w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν ∧
      ∫ g in s.fd, PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g) ∂s.ν = ip x y * ipD w w' := by
    intro x y
    refine GlobalTheory.ChainMetric.integ_pair (μ := s.ν) (A := s.fd) (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
      (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ipD (ip x y) ?_
    intro v v'
    obtain ⟨hi, he⟩ := ipM_spec s.M s.ν s.fd (T y) (T x) (hS hc.inf hs.haar hs.fund _ (hT y) _ (hT x)) v' v
    have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
        conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) = fun g => star (T y v' g) * T x v g := by
      funext g
      rw [GlobalTheory.ChainMetric.val_tprod, GlobalTheory.ChainMetric.val_tprod, starRingEnd_apply, mul_comm]
    rw [e, hip, hpure]
    exact ⟨hi, he⟩
  refine ⟨ipD, ip, hpure, hhermD, hposD, fun x y => ?_, fun x hx => ?_, fun x y w w' => (hpair x y w w').1,
    fun x y w w' => (hpair x y w w').2⟩
  · rw [hip, hip, hsym, starRingEnd_apply]
  · rw [hip]
    refine hI2 _ (hT x) fun h0 => hx ?_
    exact Submodule.coe_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem finDim_and_metEx : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D :=
  fun h h' D => ⟨finDim h D, metEx h' D⟩

end GlobalTheory.EvenMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAllMaps
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open GlobalTheory.HolDict GlobalTheory.BackForm
open scoped Classical

namespace GlobalTheory.CuspRepr


set_option maxHeartbeats 4000000 in
theorem exists_allMaps : ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ), ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → (∀ k ∈ K, ∀ y, RG V μ (k : GA D V) (Φ y) = Φ y) → ∃ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro D θ hθ V S M μ _ _ Φ hΦ K hK hKfix
  obtain ⟨𝓕, ρ, e, hp, hρ, he, hrep⟩ := _root_.GlobalTheory.TrModel.exists_model D V μ
  obtain ⟨hcusp, hequiv⟩ := (GlobalTheory.AutMult.mem_homDS hθ).1 hΦ
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), ∀ y, Φ' y = e (Φ y) :=
    ⟨(e.toContinuousLinearEquiv : DividedPowerChartLift V μ →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕)).compContinuousMultilinearMap Φ, fun _ => rfl⟩
  have e2 : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ' (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ' y) := by
    intro τ g hg y
    rw [hΦ', hΦ', hequiv τ g hg y, he]
  obtain ⟨r1, r2, -, r4, -, -⟩ := _root_.GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hp hρ
  let U : Subgroup (GA D V) := K.comap (GlobalTheory.AutMult.toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hK.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ' y) = Φ' y := by
    intro y k hk hk'
    have h1 : (⟨k, hk'⟩ : GfC V) ∈ K := by
      have h2 : GlobalTheory.AutMult.toFin V k ∈ K := hk
      rwa [show GlobalTheory.AutMult.toFin V k = ⟨k, hk'⟩ from GlobalTheory.AutMult.toFin_coe (⟨k, hk'⟩ : GfC V)] at h2
    rw [hΦ', ← he]
    exact congrArg e (hKfix _ h1 y)
  have hsmM := _root_.GlobalTheory.SmoothMultilinear.smooth_map D θ V hθ S M _ ρ Φ' e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    _root_.GlobalTheory.SmoothRep.exists_smooth_repr D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ' fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  have p1' : ∀ y : M.Vec, Repr V μ 𝓕 (e (Φ fun τ => (y τ : M.H τ))) (ψ y) := fun y => hΦ' _ ▸ p1 y
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => _root_.GlobalTheory.UnitarySmVec.smoothVec_basic V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (_root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ' fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ'.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ'.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := _root_.GlobalTheory.SobolevGrowth.pointwise_growth D θ V hθ μ 𝓕 ρ hp hρ U hU
  have hEq : GlobalTheory.RepSmooth.IsEquiv θ T := by
    intro τ g hg y z hz
    refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  have cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
      (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
      (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
      (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
        Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
      (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
      (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
      (τ : D.what₂.Tau) (v : M.Vec) :
      ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
    have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
    refine ⟨ℓ, ?_, hℓ'⟩
    obtain ⟨C', hC', hb⟩ := sum_bound
      (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
      (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
        intro l hl
        refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
        refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
        rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
        congr 2
        funext σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Function.update_of_ne h])
    refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
    · intro l hl
      obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
      exact lettersAt_mem (hL l' h')
    · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
      have h1 := hℓ' ⟨w, hw'⟩
      have h2 := hb ⟨w, hw'⟩
      have h3 := hC (Function.update v τ ⟨w, hw'⟩)
      rw [List.map_map, mul_assoc]
      simp only at h1
      rw [h1]
      refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have word_value (T : MMap M)
      (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
      (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
        Rder θ V τ X (T y) = T (Function.update y τ w))
      (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
      ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
    induction l with
    | nil => exact ⟨y, rfl⟩
    | cons p l ih =>
      obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩
  have hSob : GlobalTheory.RepSmooth.IsSob T := by
    intro τ y x
    obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ' T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this
  have hmult : IsMultMap θ M ∅ (fun _ => 1) T := by
    refine ⟨fun y => ⟨p2 y, p3 y, GlobalTheory.RepSmooth.zfin hEq hSob y, N, fun l hl x => ?_⟩, fun y => ?_,
      fun y k hk => hk.elim, hEq, hSob⟩
    · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
      obtain ⟨C, hC⟩ := hgr x
      refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ' fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
      rw [hy', mul_right_comm]
      exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
    · exact _root_.GlobalTheory.CuspRep.isCuspFun_of_mem_L2cusp D V μ _ (hcusp _) (ψ y) (p2 y).cont (p2 y).left ((hrep _ _).1 (p1' y))
  exact ⟨T, Submodule.subset_span hmult, fun v => (hrep _ _).1 (p1' v)⟩

end GlobalTheory.CuspRepr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem ratPt_mulVec_ratV : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E,
    ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  intro D V γ hγ y
  obtain ⟨e, he⟩ := GlobalTheory.Ker.Grp.exists_equiv V
  have h : mt V γ = ((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have := he (e.symm ⟨γ, hγ⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ y, ?_⟩
  rw [h]
  funext i
  simp only [ratV]
  exact (RingHom.map_mulVec (incA D) _ y i).symm

end GlobalTheory.SepPer

end
end

