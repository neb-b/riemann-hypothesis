module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutMult

open scoped InnerProductSpace
open GlobalTheory.Cusp


open Classical in
theorem rank_homIn_eq_rank_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} (hirr : σ.IsIrreducible)
    (hadm : IsAdmissible σ) (hcopy : IsCopyFinDS σ M π ⊤) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : GA D V →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) {U : Submodule ℂ K} (hU : IsClosed (U : Set K)) :
    Module.rank ℂ (homIn π ρ U) = Module.rank ℂ (homFinDS σ M ρ U) := by
  obtain ⟨T, hT, hinj, hd⟩ := hcopy
  have hTm := mem_homTensorPi.1 hT
  let f : homIn π ρ U →ₗ[ℂ] (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) :=
    { toFun := fun A => (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H K (A : H →L[ℂ] K)).toLinearMap ∘ₗ T
      map_add' := fun A B => by ext w y; simp
      map_smul' := fun c A => by ext w y; simp }
  have hmem : ∀ A, f A ∈ homFinDS σ M ρ U := fun A => by
    refine mem_homTensorPi.2 ⟨fun w y => ?_, fun g w y => ?_, fun i g w y => ?_⟩
    · exact A.2.1 _
    · change (A : H →L[ℂ] K) (T (σ g w) y) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.1 g w y)).trans (A.2.2 _ _)
    · change (A : H →L[ℂ] K) (T w _) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.2 i g w y)).trans (A.2.2 _ _)
  let F : homIn π ρ U →ₗ[ℂ] homFinDS σ M ρ U := f.codRestrict _ hmem
  have hdense : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  have hbij : Function.Bijective F := by
    constructor
    · intro A B hAB
      have e : ∀ w y, (A : H →L[ℂ] K) (T w y) = (B : H →L[ℂ] K) (T w y) := fun w y =>
        congrArg (fun Φ : homFinDS σ M ρ U => ((Φ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) w) y) hAB
      refine Subtype.ext (ContinuousLinearMap.ext_on hdense ?_)
      rintro _ ⟨w, y, rfl⟩
      exact e w y
    · intro Φ
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hirr hadm H π hπ T hT hinj hd K ρ hρ U hU Φ.1 Φ.2
      exact ⟨⟨A, hA⟩, Subtype.ext (LinearMap.ext fun w => ContinuousMultilinearMap.ext fun y => hAe w y)⟩
  exact (LinearEquiv.ofBijective F hbij).rank_eq


open Classical in
theorem mCusp_eq_mCuspDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  intro D V S M μ _ _ H _ _ π hπ W _ _ σ hirr hadm hcopy
  haveI : CompleteSpace H := hπ.complete
  exact rank_homIn_eq_rank_homFinDS hπ.unitary hirr hadm hcopy (isUnitaryRep_RG V μ) (isSubrep_L2cusp V μ).1

end GlobalTheory.AutMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDS
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

theorem topologicalClosure_span_eq_top_of_le {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) (s : Set U)
    (h : U ≤ (Submodule.span ℂ (Subtype.val '' s)).topologicalClosure) :
    (Submodule.span ℂ s).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s) := by
    exact congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)
  have h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U)) := by
    rw [hmap, ← Submodule.topologicalClosure_coe]
    exact h hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  exact h2

theorem exists_isIrrUnitary_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)),
      IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  intro D V S M μ _ _ W _ _ σ hirr hadm hm
  classical
  have hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥ := fun h => hm (by rw [mCuspDS, h]; simp)
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinj : Function.Injective T := injective_of_mem_homInto hirr hT hT0
  have hTt : T ∈ homFinDS σ M (RG V μ) ⊤ := homTensorPi_mono le_top hT
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U :=
    ⟨_, rfl⟩
  have hcopy : IsCopyFinDS σ M (RG V μ) U := ⟨T, hTt, hinj, hUdef⟩
  have hU := TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy
  refine ⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩
  have hmem : ∀ w y, T w y ∈ U := fun w y =>
    hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)
  let T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U :=
    { toFun := fun w => (T w).codRestrict U (hmem w)
      map_add' := fun a b => by ext y; simp
      map_smul' := fun c a => by ext y; simp }
  have hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y := fun _ _ => rfl
  have hTm := mem_homTensorPi.1 hTt
  refine ⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩,
    fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩
  · exact hTm.2.1 g w y
  · exact hTm.2.2 i g w y
  · have himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨w, y, rfl⟩, rfl⟩
        exact ⟨w, y, rfl⟩
      · rintro ⟨w, y, rfl⟩
        exact ⟨T' w y, ⟨w, y, rfl⟩, rfl⟩
    exact topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))

end GlobalTheory.AutMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorization
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

section Helpers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem conv_cosetInd_eq_smul (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) :
    conv μ f (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 = fun y => (μ.real K : ℂ) * f y := by
  classical
  funext y
  have hs : MeasurableSet ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)) :=
    (ho.preimage (continuous_const.mul continuous_id)).measurableSet
  have e : (fun x => f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y)) =
      ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)).indicator (fun _ => f y) := by
    funext x
    rw [GlobalTheory.InvBilinTest.cosetInd_apply]
    by_cases hx : y⁻¹ * x ∈ K
    · have h1 : x⁻¹ * y * 1⁻¹ ∈ K := by simpa using K.inv_mem hx
      rw [if_pos h1, Set.indicator_of_mem (show x ∈ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_one]
      have := hf _ hx y
      rwa [mul_inv_cancel_left] at this
    · have h1 : ¬ x⁻¹ * y * 1⁻¹ ∈ K := fun h => hx (by simpa using K.inv_mem h)
      rw [if_neg h1, Set.indicator_of_notMem (show x ∉ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_zero]
  show ∫ x, f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y) ∂μ = _
  rw [e, integral_indicator_const _ hs]
  simp only [Measure.real, measure_preimage_mul, Complex.real_smul]

theorem isIntegralOp_const_mul {W : Type} [AddCommGroup W] [Module ℂ W] {μ : Measure G}
    {σ : Representation ℂ G W} {f : G → ℂ} {A : W →ₗ[ℂ] W} (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A) (c : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun g => c * f g) (c • A) := by
  intro v l
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using (hA v l).1.const_mul c
  · rw [LinearMap.smul_apply, map_smul, smul_eq_mul, (hA v l).2, ← integral_const_mul]
    simp only [mul_assoc]

end Helpers


open Classical in
theorem hasTrace_repOp_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c → HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c := by
  intro D V lam S M T U μa μf μ _ _ fa ff hT ν hν H _ _ _ π hπ W _ _ σ hirr hadm hcopy c hc
  obtain ⟨-, -, -, -, hres, harch, hfin⟩ := hT
  have hff := hfin.isFinFamily
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨Tm, hTm, hinj, hdense⟩ := hcopy
  have hTm' : Tm ∈ homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) π ⊤ := hTm
  obtain ⟨A, hA, hAtr⟩ := hc
  have hσ : GlobalTheory.PRep.IsSmooth σ := hadm.1
  have hX := GlobalTheory.TrOpTensor.opTensor D V S M μa μf μ hres ν hν fa ff harch.mem hff W σ hσ H π hπ.unitary Tm hTm A hA
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  obtain ⟨U₀, hU₀, hbi⟩ := GlobalTheory.Orb.exists_biinvariant (f := finFn V ff) ⟨hlc, hcs⟩
  obtain ⟨K₀, hK₀o, hK₀c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup (GfC V), K = U₀ ⊓ K₀ := ⟨_, rfl⟩
  have hKo : IsOpen (K : Set (GfC V)) := hKdef ▸ hU₀.inter hK₀o
  have hKc : IsCompact (K : Set (GfC V)) := hKdef ▸ hK₀c.inter_left (U₀.isClosed_of_isOpen hU₀)
  have hKU : ∀ k ∈ K, k ∈ U₀ := fun k hk => (Subgroup.mem_inf.1 (hKdef ▸ hk)).1
  have hZ : FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) := hadm.2 K hKo hKc
  have hrange : LinearMap.range A ≤ GlobalTheory.PRep.fixed σ K := by
    rintro _ ⟨w, rfl⟩
    exact GlobalTheory.IwahoriRel.isIntegralOp_mem_fixed hA (fun k hk g => (hbi k (hKU k hk) g).1) w

  obtain ⟨e, he⟩ : ∃ e, e = GlobalTheory.InvBilinTest.cosetInd K hKo hKc 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = smoothOp σ ν e.1 := ⟨_, rfl⟩
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ e.1 P := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.smoothOp_integrand e.2.1 e.2.2 v).1
        (hσ.smoothOp_integrand e.2.1 e.2.2 v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hPdef, hσ.map_smoothOp e.2.1 e.2.2 l v]
      simp only [smul_eq_mul]
  have hconv := (GlobalTheory.OpConv.isIntegralOp_conv_and_translate _ ν W σ hσ _ ⟨hlc, hcs⟩ e.1 e.2 A P hA hP).1
  rw [he, conv_cosetInd_eq_smul ν K hKo hKc _ (fun k hk g => (hbi k (hKU k hk) g).2)] at hconv
  have hAP : A ∘ₗ P = (ν.real K : ℂ) • A := hconv.unique (isIntegralOp_const_mul hA _)
  have hvol : (ν.real K : ℂ) ≠ 0 := by
    have h1 : ν K ≠ 0 := (hKo.measure_pos ν ⟨1, K.one_mem⟩).ne'
    have h2 : ν.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_ne_top⟩
    exact_mod_cast h2
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hinner : ∀ w w' y y', inner ℂ (Tm w' y') (Tm w y) = bePi (Tm w) (Tm w') * ∏ τ, inner ℂ (y' τ) (y τ) :=
    fun w w' y y' => inner_eq_bePi hδ hπ.unitary (hTm'.1 w) (hTm'.1 w') y y'
  have hcond : ∀ w, (∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm w) (Tm z) = 0) → A w = 0 := by
    intro w hw
    have hPw : P w ∈ GlobalTheory.PRep.fixed σ K := hPdef ▸ hσ.smoothOp_mem_fixed (μ := ν) e.2.1 e.2.2 (fun k hk g => by
      simp only [he, GlobalTheory.InvBilinTest.cosetInd_apply, inv_one, mul_one, K.mul_mem_cancel_left hk]) w
    have hβP : ∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm (P w)) (Tm z) = (ν.real K : ℂ) * bePi (Tm w) (Tm z) := by
      intro z hz
      let l : W →ₗ[ℂ] ℂ :=
        { toFun := fun v => bePi (Tm v) (Tm z)
          map_add' := fun a b => by simp [bePi, inner_add_right]
          map_smul' := fun a b => by simp [bePi, inner_smul_right] }
      have hl : ∀ g ∈ K, l (σ g w) = l w := fun g hg => by
        have hz' : σ g z = z := mem_fixed.1 hz g hg
        show bePi (Tm (σ g w)) (Tm z) = bePi (Tm w) (Tm z)
        simp only [bePi]
        calc inner ℂ (Tm z fun i => unitVec (H := M.H i)) (Tm (σ g w) fun i => unitVec (H := M.H i))
            = inner ℂ (Tm (σ g z) fun i => unitVec (H := M.H i)) (Tm (σ g w) fun i => unitVec (H := M.H i)) := by rw [hz']
          _ = inner ℂ (π g (Tm z fun i => unitVec (H := M.H i))) (π g (Tm w fun i => unitVec (H := M.H i))) := by
            rw [(mem_homTensorPi.1 hTm').2.1, (mem_homTensorPi.1 hTm').2.1]; rfl
          _ = _ := inner_map_map hπ.unitary _ _ _
      have h1 := (hP w l).2
      have h2 : ∫ g, e.1 g * l (σ g w) ∂ν = ∫ g, (if g ∈ K then l w else 0) ∂ν := by
        refine integral_congr_ae (.of_forall fun g => ?_)
        by_cases hg : g ∈ K
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg, hl g hg]
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg]
      rw [h2, GlobalTheory.InvBilinTest.integral_ite K hKo] at h1
      exact h1
    have h0 : P w = 0 := by
      by_contra hne
      have hT0 : Tm (P w) ≠ 0 := fun h => hne (hinj (h.trans (map_zero Tm).symm))
      have hpos := bePi_self_pos hδ hπ.unitary (hTm'.1 (P w)) hT0
      rw [hβP (P w) hPw, hw (P w) hPw, mul_zero] at hpos
      exact lt_irrefl _ hpos
    have h3 := LinearMap.congr_fun hAP w
    rw [LinearMap.comp_apply, h0, map_zero, LinearMap.smul_apply] at h3
    exact (smul_eq_zero.1 h3.symm).resolve_left hvol
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have key := GlobalTheory.TensorTrace.hasTrace_finiteRank_tensor D.what₂.Tau M.H H W Tm (fun w w' => bePi (Tm w) (Tm w')) hinner hinj hdense A c hAtr
    (GlobalTheory.PRep.fixed σ K) hZ hrange hcond (fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)))
    (fun _ => 1) (fun τ => (harch τ).trace_self) (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) hX
  simpa using key

end GlobalTheory.AutMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeries
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.AutMult

theorem isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  classical
  intro D V S M H _ _ π hπ W _ _ σ hσ hσa hc H' _ _ π' hπ' W' _ _ σ' hσ' hσa' hc'
  have := hπ.complete
  have := hπ'.complete
  obtain ⟨T, hT, hTi, hTd⟩ := hc
  obtain ⟨T', hT', hTi', hTd'⟩ := hc'
  have hTf : T ∈ homFinDS σ M π ⊤ := hT
  have hTf' : T' ∈ homFinDS σ' M π' ⊤ := hT'
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  haveI : σ.IsIrreducible := hσ
  haveI : σ'.IsIrreducible := hσ'
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ.asModule
  haveI : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ'.asModule
  constructor
  · rintro ⟨A, hA⟩
    have hAs : ∀ g x, A.symm (π' g x) = π g (A.symm x) := fun g x => by
      apply A.injective
      rw [hA, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    let Ac : H' →L[ℂ] H := A.symm.toLinearIsometry.toContinuousLinearMap
    let T'' : W' →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
      (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H' H Ac).toLinearMap ∘ₗ T'
    have hT''v : ∀ w y, T'' w y = A.symm (T' w y) := fun _ _ => rfl
    have hT'' : ∀ w, T'' w ∈ homDS M π ⊤ := fun w => ⟨fun _ => trivial, fun τ g y => by
      rw [hT''v, hT''v, hTm'.2.2, hAs]⟩
    let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    let C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T'' w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
      bePi_self_pos hδ hπ.unitary (hT.1 x) ((map_ne_zero_iff T hTi).2 hx)
    have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
      change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
      rw [hTm.2.1, hTm.2.1, inner_map_map hπ.unitary]
    have hC : ∀ g x y, C (σ g x) (σ' g y) = C x y := fun g x y => by
      change ⟪T'' (σ' g y) _, T (σ g x) _⟫_ℂ = ⟪T'' y _, T x _⟫_ℂ
      rw [hT''v, hT''v, hTm'.2.1, hAs, hTm.2.1, inner_map_map hπ.unitary]
    obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
    obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W' σ σ' hσa hσa'.1 B C hBpos hB hC
    obtain ⟨w', hw'⟩ := exists_ne (0 : W')
    have h1 : T'' w' ≠ 0 := by
      intro h
      apply hw'
      apply hTi'
      rw [map_zero]
      ext y
      apply A.symm.injective
      rw [← hT''v, h]
      simp
    obtain ⟨y', hy'⟩ : ∃ y', T'' w' y' ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    obtain ⟨w, y, hwy⟩ : ∃ w y, ⟪T'' w' y', T w y⟫_ℂ ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hy'
      have hsub : Submodule.span ℂ {v | ∃ w y, v = T w y} ≤ (ℂ ∙ T'' w' y')ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨w, y, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hn w y))
      have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
      rw [hTd] at hcl
      exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
    have hC0 : C w w' ≠ 0 := fun h => hwy (by
      rw [inner_eq_bePi hδ hπ.unitary (hT.1 w) (hT'' w') y y']
      change C w w' * _ = 0
      rw [h, zero_mul])
    have hφ0 : φ w' ≠ 0 := fun h => hC0 (by rw [hCB, h, map_zero])
    let f : Representation.IntertwiningMap σ' σ := ⟨φ, fun g => LinearMap.ext fun y => hφ g y⟩
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hf0
    · exact ⟨(Representation.IntertwiningMap.ofBijective f hb).symm⟩
    · exact absurd (congrArg (fun F : Representation.IntertwiningMap σ' σ => F w') hf0) hφ0
  · rintro ⟨e⟩
    let T₂ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H' := T' ∘ₗ e.toLinearMap
    have hT₂ : T₂ ∈ homFinDS σ M π' ⊤ := by
      refine mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => ?_, fun τ g w y => hTm'.2.2 τ g (e w) y⟩
      change T' (e (σ g w)) y = _
      rw [show e (σ g w) = σ' g (e w) from Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w]
      exact hTm'.2.1 g (e w) y
    obtain ⟨B, hB, hBv⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hσ hσa H π hπ.unitary T hTf hTi hTd H' π'
      hπ'.unitary ⊤ isClosed_univ T₂ hT₂
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : T' (e w) ≠ 0 := fun h => hw (e.injective (hTi' (h.trans (map_zero T').symm) |>.trans (map_zero e).symm))
    obtain ⟨y, hy⟩ : ∃ y, T' (e w) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    have hB0 : B ≠ 0 := fun h => hy (by rw [← show B (T w y) = T' (e w) y from hBv w y, h]; rfl)
    have hm : multIn π π' ⊤ ≠ 0 := by
      intro h0
      rw [multIn, Submodule.rank_eq_zero] at h0
      exact hB0 (by simpa [h0] using hB)
    obtain ⟨f, hf⟩ := uEquiv_of_multIn_ne_zero hπ hπ' hm
    exact ⟨f, hf⟩

end GlobalTheory.AutMult
end
end

