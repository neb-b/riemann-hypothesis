module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.OffOp

section General

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A]

def splitEquiv (ι : A →* G) (π : G →* A) (hπι : ∀ a, π (ι a) = a) (hc : ∀ a g, π g = 1 → Commute (ι a) g) :
    π.ker × A ≃* G where
  toFun p := p.1 * ι p.2
  invFun g := (⟨g * (ι (π g))⁻¹, by simp [MonoidHom.mem_ker, hπι]⟩, π g)
  left_inv p := by
    have h : π p.1 = 1 := p.1.2
    ext <;> simp [hπι, h]
  right_inv g := by simp
  map_mul' p q := by
    have := (hc p.2 q.1 q.1.2).eq
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
    rw [← mul_assoc (q.1 : G), ← this, mul_assoc]

variable [T2Space A] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem exists_op (ι : A →* G) (π : G →* A) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ a, π (ι a) = a)
    (hc : ∀ a g, π g = 1 → Commute (ι a) g) (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure G) [ν.IsHaarMeasure]
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : GlobalTheory.PRep.IsSmooth σ)
    {φ : G → ℂ} (hφ : φ ∈ GlobalTheory.SplitWeil.SB G) :
    ∃ H : W →ₗ[ℂ] W, (∀ g x, H (σ (ι g) x) = σ (ι g) (H x)) ∧
      (∀ x, ∀ k ∈ leftStabilizer φ, π k = 1 → σ k (H x) = H x) ∧
      ∀ f ∈ GlobalTheory.SplitWeil.SB A, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ (σ.comp ι) f B →
        ∀ Ψ : G → ℂ, (∀ h a, π h = 1 → Ψ (h * ι a) = φ h * f a) → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ Ψ (H ∘ₗ B) := by
  classical
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hNc : IsClosed (π.ker : Set G) := by
    have hset : (π.ker : Set G) = π ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hNc.locallyCompactSpace
  let e : π.ker × A ≃ₜ* G :=
    { splitEquiv ι π hπι hc with
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hι.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ hπ
        exact (continuous_id.mul (hι.comp hπ).inv).subtype_mk _ }
  have he : ∀ p : π.ker × A, e p = (p.1 : G) * ι p.2 := fun p => rfl
  let μN : Measure π.ker := Measure.haar
  let P : Measure (π.ker × A) := μN.prod μ
  have hE : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  haveI : (P.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P e
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • P.map e := ⟨_, Measure.isMulLeftInvariant_eq_smul ν (P.map e)⟩
  let σN : Representation ℂ π.ker W := σ.comp π.ker.subtype
  have hσN : GlobalTheory.PRep.IsSmooth σN := fun x => (hσ x).preimage continuous_subtype_val
  let φN : π.ker → ℂ := fun h => φ h
  have hφN1 : IsLocallyConstant φN := hφ'.1.comp_continuous continuous_subtype_val
  have hφN2 : HasCompactSupport φN := hφ'.2.comp_isClosedEmbedding hNc.isClosedEmbedding_subtypeVal
  let T : W →ₗ[ℂ] W := smoothOp σN μN φN
  have hT : ∀ (l : Module.Dual ℂ W) (y : W), l (T y) = ∫ h, φN h * l (σN h y) ∂μN := by
    intro l y
    simpa [smul_eq_mul] using hσN.map_smoothOp (μ := μN) hφN1 hφN2 l y
  refine ⟨((c : ℝ) : ℂ) • T, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
    refine (hσN.map_smoothOp_of_intertwining (μ := μN) hσN hφN1 hφN2 (σ (ι g)) (fun h y => ?_) x).symm
    show σ (ι g) (σ h y) = σ h (σ (ι g) y)
    rw [← mul_apply_eq_comp, ← map_mul, (hc g h h.2).eq, map_mul, mul_apply_eq_comp]
  · intro x k hk hk1
    have hmem := hσN.smoothOp_mem_fixed (μ := μN) hφN1 hφN2
      (K := (leftStabilizer φ).comap π.ker.subtype) (fun k' hk' g => hk' g) x
    have hfix := (mem_fixed.1 hmem) ⟨k, MonoidHom.mem_ker.2 hk1⟩ hk
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
  · intro f hf B hB Ψ hΨ v l
    have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
    let F : π.ker × A → ℂ := fun p => φN p.1 * f p.2 * l (σ (e p) v)
    have hFe : ∀ p, Ψ (e p) * l (σ (e p) v) = F p := by
      intro p
      show Ψ (e p) * l (σ (e p) v) = φ p.1 * f p.2 * l (σ (e p) v)
      rw [he p, hΨ _ _ p.1.2]
    have hFlc : IsLocallyConstant F := by
      have h1 : IsLocallyConstant fun p : π.ker × A => φN p.1 := hφN1.comp_continuous continuous_fst
      have h2 : IsLocallyConstant fun p : π.ker × A => f p.2 := hf'.1.comp_continuous continuous_snd
      have h3 : IsLocallyConstant fun p : π.ker × A => l (σ (e p) v) :=
        ((hσ.isLocallyConstant_orbit v).comp_continuous e.continuous).comp l
      exact (h1.mul h2).mul h3
    have hFcs : HasCompactSupport F := by
      refine IsCompact.of_isClosed_subset (IsCompact.prod hφN2 hf'.2) (isClosed_tsupport F) ?_
      refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro p hp
      refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, zero_mul, zero_mul]
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, mul_zero, zero_mul]
    have hFi : Integrable F P := hFlc.continuous.integrable_of_hasCompactSupport hFcs
    refine ⟨?_, ?_⟩
    · rw [hν]
      refine Integrable.smul_measure_nnreal ?_
      rw [hE.integrable_map_iff]
      exact hFi.congr (Filter.Eventually.of_forall fun p => (hFe p).symm)
    · have hin : ∀ a, ∫ h, F (h, a) ∂μN = f a * l (T (σ (ι a) v)) := by
        intro a
        rw [hT, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show φN h * f a * l (σ (e (h, a)) v) = f a * (φN h * l (σ h (σ (ι a) v)))
        rw [he, map_mul, mul_apply_eq_comp]
        ring
      have hB2 := (hB v (l ∘ₗ T)).2
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply] at hB2
      rw [hν, integral_smul_nnreal_measure, hE.integral_map,
        integral_congr_ae (Filter.Eventually.of_forall hFe), integral_prod_symm F hFi,
        show (fun a => ∫ h, F (h, a) ∂μN) = fun a => f a * l (T (σ (ι a) v)) from funext hin, ← hB2]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, NNReal.smul_def,
        Complex.real_smul]

end General

variable {D : D7}

local instance (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) :=
  GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V

theorem isFinFamily_update {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) :
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (Function.update ff u f) := by
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v = u
    · subst hv
      simpa using hf
    · rw [Function.update_of_ne hv]
      exact hff.1 v
  · filter_upwards [hff.2, Filter.eventually_cofinite_ne u] with v hv hne
    rw [Function.update_of_ne hne]
    exact hv

theorem finite_mulSupport {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (g : GfC V) :
    (Function.mulSupport fun v => ff v (finLoc V v g)).Finite := by
  have hev := GlobalTheory.AdelicU.eventually_proj_mem_stabLoc (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V)
    (g := (g : GA D V))
  refine (Filter.eventually_cofinite.1 (hff.2.and hev)).subset fun v hv => ?_
  rintro ⟨h1, h2⟩
  apply hv
  show ff v (proj D.sp.cm.sig V.gram v (g : GA D V)) = 1
  rw [h1]
  exact (Set.indicator_of_mem h2 1).trans rfl

theorem finFn_update_mul {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) (h : GfC V) (a : Gv V u)
    (hh : finLoc V u h = 1) :
    finFn V (Function.update ff u f) (h * locFin V u a) =
      finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u)) h * f a := by
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have m1 := finite_mulSupport (isFinFamily_update hff u hf) (h * locFin V u a)
  have m2 := finite_mulSupport (isFinFamily_update hff u hu) h
  have hfin : ∀ (ff' : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GfC V),
      finFn V ff' g = ∏ᶠ v, ff' v (finLoc V v g) := fun _ _ => rfl
  have hloc : ∀ v, finLoc V v (locFin V u a) = proj D.sp.cm.sig V.gram v (emb D.sp.cm.sig V.gram u a) :=
    fun _ => rfl
  rw [hfin, hfin, ← mul_finprod_cond_ne u m1, ← mul_finprod_cond_ne u m2]
  have hoff : (∏ᶠ (v) (_ : v ≠ u), Function.update ff u f v (finLoc V v (h * locFin V u a))) =
      ∏ᶠ (v) (_ : v ≠ u), Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u) v (finLoc V v h) := by
    refine finprod_congr fun v => finprod_congr fun hv => ?_
    rw [Function.update_of_ne hv, Function.update_of_ne hv, map_mul, hloc, proj_emb_ne D.sp.cm.sig V.gram hv, mul_one]
  rw [hoff, Function.update_self, Function.update_self, map_mul, hh, hloc, proj_emb_self, one_mul]
  have h1 : unitLoc D.sp.cm.sig V.gram (frameLat V) u 1 = 1 :=
    (Set.indicator_of_mem (one_mem _) 1).trans rfl
  rw [h1, one_mul, mul_comm]

theorem exists_offOp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  intro D V u μf hμf hK ν hν W _ _ σ hσ ff hff
  haveI := hμf u
  haveI : LocallyCompactSpace (GfC V) := GlobalTheory.AdelicU.locallyCompactSpace_finPts D.sp.cm.sig V.gram
  haveI : ν.IsHaarMeasure := hν.1
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have hfam := isFinFamily_update hff u hu
  have hφ := (GlobalTheory.TrConv.conv_finFn D V μf hμf hK ν hν _ _ hfam hfam).2.2
  have hφ' : IsLocallyConstant (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) ∧
      HasCompactSupport (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) := hφ
  have hι : Continuous (locFin V u) := continuous_induced_rng.2 (continuous_emb D.sp.cm.sig V.gram u)
  have hπ : Continuous (finLoc V u) := (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val
  have hπι : ∀ a, finLoc V u (locFin V u a) = a := fun a => proj_emb_self D.sp.cm.sig V.gram u a
  have hc : ∀ a g, finLoc V u g = 1 → Commute (locFin V u a) g := fun a g hg =>
    Subtype.ext (commute_emb D.sp.cm.sig V.gram a hg).eq
  obtain ⟨H, h1, h2, h3⟩ := exists_op (locFin V u) (finLoc V u) hι hπ hπι hc (μf u) ν σ hσ hφ
  exact ⟨H, leftStabilizer _, isOpen_leftStabilizer hφ'.1 hφ'.2, h1, h2,
    fun f hf B hB => h3 f hf B hB _ fun h a hh => finFn_update_mul hff u hf h a hh⟩

end GlobalTheory.OffOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefUnfold

theorem isoPart_add' {D : D7} (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart
  rw [Matrix.add_mul]

private theorem symplOH_eq_zero_of_symplO_eq_zero {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem sum_translates_eq : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ y : Mx D W.rank r, Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖) → ∑' a : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = κ • ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y hs
  have hY' := hY
  obtain ⟨hμH, hYF, hY1⟩ := hY'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI : IsTopologicalAddGroup (Mx D W.rank r) := i1
  haveI : LocallyCompactSpace (Mx D W.rank r) := i2
  haveI : SecondCountableTopology (Mx D W.rank r) := i3
  haveI : T2Space (Mx D W.rank r) := i4
  haveI : DiscreteTopology (ratMx D W.rank r) := i5
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hsp := _root_.GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hiso0 : isoPart V W C' (0 : Mx D W.rank r) = 0 := by
    have e := isoPart_add' V W C' (0 : Mx D W.rank r) 0
    rw [add_zero] at e
    have e' : isoPart V W C' (0 : Mx D W.rank r) + isoPart V W C' 0 = isoPart V W C' 0 + 0 := by
      rw [add_zero]; exact e.symm
    exact add_left_cancel e'
  have hpt : ∀ (y' : Mx D W.rank r) (x : WO V' W),
      heisO ψ V W (isoPart V W C y) F (isoPart V W C y' + midPart V V' W B x) =
        F (isoPart V W C (y + y') + midPart V V' W B x) := by
    intro y' x
    have z1 : symplOH V W (isoPart V W C y') (isoPart V W C y) = 0 :=
      symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.1 y' y)
    have z2 : symplOH V W (midPart V V' W B x) (isoPart V W C y) = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.2.1 y x), neg_zero]
    show ψ (symplOH V W (isoPart V W C y' + midPart V V' W B x) (isoPart V W C y)) *
        F (isoPart V W C y' + midPart V V' W B x + isoPart V W C y) = _
    rw [(GlobalTheory.OrientedFormLaws.symplOH_laws D V W).1, z1, z2, add_zero, AddChar.map_zero_eq_one, one_mul,
      isoPart_add']
    congr 1
    abel
  have hP : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 _ _ hF
  let χ : Matrix (Fin W.rank) (Fin r) D.host.E → Mx D W.rank r → ℂ :=
    fun a t => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))
  let Φ : Mx D W.rank r → ℂ := fun t => κ • ∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ
  have hterm : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E,
      (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) =
        ∫ t in 𝓨, χ a t * Φ t ∂μ := fun a =>
    _root_.GlobalTheory.TwistCoefUnfold.pcoef D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y a
  obtain ⟨hχc, hχx, hχa, hχΓ, hχ0⟩ := _root_.GlobalTheory.IsoDualChars.chars D V V' W r C B hCB C' h1 h2 h3 ψ hψ
  obtain ⟨hΦc, hΦp⟩ := _root_.GlobalTheory.TwistThetaMean.mean_continuous_periodic D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hP hG
  have hsum : Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) := by
    have e : (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) =
        fun a => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖ :=
      funext fun a => by rw [hterm a]
    rw [e]
    exact hs
  have key := _root_.GlobalTheory.CompactQuotientFourier.inversion_at_zero (Mx D W.rank r) (ratMx D W.rank r) K hK hKc (Matrix (Fin W.rank) (Fin r) D.host.E) χ
    hχc (fun a t s => hχx a t s) (fun a b t => hχa a b t) (fun a t => hψ.1.2.1 _) hχΓ hχ0 μ 𝓨 hμH hYF hY1 Φ
    (hΦc.const_smul κ) (fun γ hγ t => congrArg (fun z : ℂ => κ • z) (hΦp γ hγ t)) hsum
  rw [tsum_congr hterm, ← key]
  show κ • (∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = _
  simp only [hiso0, zero_add]
  simp_rw [hpt]

private theorem symplOH_eq_zero_of_symplO_eq_zero' {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  intro D V V' W r C B hCB ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨C', h1, h2, h3⟩ := _root_.GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hCB
  obtain ⟨κ, hκ0, hκ⟩ := _root_.GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hCB C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  have hY' := hY
  obtain ⟨hμH, hYF, -⟩ := hY'
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := hμH
  have hc0 : ENNReal.ofReal κ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hκ0)).ne'
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, MeasureTheory.Measure.IsAddHaarMeasure.smul μ hc0 ENNReal.ofReal_ne_top, ?_⟩
  intro F G hF hG x
  have hsp := _root_.GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hF₁ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 (midPart V V' W B x) F hF
  have he : ∀ y : Mx D W.rank r, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) =
      heisO ψ V W (isoPart V W C y + midPart V V' W B x) F := by
    intro y
    rw [(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).2.1, symplOH_eq_zero_of_symplO_eq_zero' V W _ _ (hsp.2.1 y x),
      AddChar.map_zero_eq_one, one_smul]
  rw [← ((_root_.GlobalTheory.TowerRestrict.res_theta D V V' W r C B hCB ψ hψ μ 𝓨 hY).1 F hF).2.2.1 x,
    ← _root_.GlobalTheory.IsoMeanProd.mean_iso_mul_star D V V' W r C B hCB ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hF₁ hG]
  simp_rw [← he]
  obtain ⟨hsum, hint⟩ := GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates D W.rank r μ 𝓨 hμH hYF
    (fun y => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) w * star (G w) ∂μV)
    (_root_.GlobalTheory.CoefInteg.integrable_coef D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ hμH μV 𝓕V hμV hFV _ G hF₁ hG)
  beta_reduce at hsum hint
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 hκ0).le, hint,
    ← MeasureTheory.integral_smul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hsum] with y hy
  rw [sum_translates_eq D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ _ G hF₁ hG y hy,
    smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]

end GlobalTheory.CoefUnfold

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchurAdm

theorem schur_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.GlobalTheory.SchurAdmissibility.schur_admissible

end GlobalTheory.SchurAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothRepIntegratedOperatorNormalizedIndicatorFi
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem smoothOp_normInd_of_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → ∀ x : W, (∀ h ∈ H, ρ h x = x) → smoothOp ρ μ (normInd μ (H : Set G)) x = x := by
  intro G _ _ _ _ _ _ μ _ H ho hK W _ _ ρ hρ x hx
  have hf : IsLocallyConstant ((H : Set G).indicator (1 : G → ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
    by_cases hg : g ∈ (H : Set G)
    · exact ⟨H, ho, hg, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hg]⟩
    · exact ⟨(H : Set G)ᶜ, (H.isClosed_of_isOpen ho).isOpen_compl, hg, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((H : Set G).indicator (1 : G → ℂ)) :=
    HasCompactSupport.intro hK fun y hy => Set.indicator_of_notMem hy _
  have h0 : (μ.real H : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff hK.measure_lt_top.ne]
    exact (ho.measure_pos μ ⟨1, one_mem H⟩).ne'
  have hf' : IsLocallyConstant (normInd μ (H : Set G)) := by
    unfold normInd; exact hf.comp ((μ.real H : ℂ)⁻¹ • ·)
  have hc' : HasCompactSupport (normInd μ (H : Set G)) := by
    unfold normInd; exact hc.comp_left (g := ((μ.real H : ℂ)⁻¹ • ·)) (smul_zero _)
  refine eq_of_forall_dual fun l => ?_
  have h1 : (fun g => normInd μ (H : Set G) g • l (ρ g x)) =
      (H : Set G).indicator fun _ => (μ.real H : ℂ)⁻¹ * l x := by
    ext g
    by_cases hg : g ∈ (H : Set G)
    · have : ρ g x = x := hx g hg
      simp [normInd, Set.indicator_of_mem hg, this]
    · simp [normInd, Set.indicator_of_notMem hg]
  rw [hρ.map_smoothOp hf' hc', h1, integral_indicator_const _ ho.measurableSet]
  rw [Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitaryAlt
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaLeftW

theorem thetaKernel_leftInvariant_rationalUnitary : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i χS χT ω hW φ hφ h γ hγ g
  unfold Datum.thetaKO
  have e : (h, γ * g) = ((1 : GA D (Vc D i)), γ) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hφ)

end GlobalTheory.ThetaLeftW
end
end

