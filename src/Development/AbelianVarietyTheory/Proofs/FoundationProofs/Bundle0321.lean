module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMaps
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult.MultAssembly

open GlobalTheory.CuspMult

variable {D : D7} {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem continuous_of_mem_allMaps {T : MMap M} (hT : T ∈ allMaps θ M) (v : M.Vec) : Continuous (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact (hT.aut v).cont
  | zero => exact continuous_const
  | add T T' _ _ ih ih' => exact ih.add ih'
  | smul a T _ ih => exact ih.const_smul a

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def Represents (Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) (T : MMap M) : Prop :=
  ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v

variable {μ}

theorem eq_of_represents_cont {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M}
    (hT : ∀ v, Continuous (T v)) (hT' : ∀ v, Continuous (T' v)) (h : Represents μ Φ T) (h' : Represents μ Φ T') :
    T = T' :=
  MultilinearMap.ext fun v => (hT v).ae_eq_iff_eq μ (hT' v) |>.1 ((h v).symm.trans (h' v))

theorem represents_zero : Represents μ (0 : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) 0 := fun _ => by
  simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
  exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)

theorem Represents.add {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M} (h : Represents μ Φ T)
    (h' : Represents μ Φ' T') : Represents μ (Φ + Φ') (T + T') := fun v => by
  simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
  exact lift_add_ae (h v) (h' v)

theorem Represents.smul (c : ℂ) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M} (h : Represents μ Φ T) :
    Represents μ (c • Φ) (c • T) := fun v => by
  simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
  exact lift_smul_ae c (h v)

theorem Represents.translate (g : GfC V) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) :
    Represents μ (postRepPi M.H ((RG V μ).comp (GfC V).subtype) g Φ) (finRep M g T) := fun v =>
  (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))

theorem Represents.translate' (g : GfC V) {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) (h' : ∀ y, Φ' y = RG V μ (g : GA D V) (Φ y)) : Represents μ Φ' (finRep M g T) := fun v => by
  rw [h']
  exact (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))


variable (μ) in
def phiOf (T : MMap M) : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) :=
  open Classical in
  if h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T then h.choose else 0

theorem phiOf_spec (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M) :
    phiOf μ T ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ (phiOf μ T) T := by
  have h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T :=
    (GlobalTheory.CuspIntertwiner.existsUnique_intertwiner hP D θ hθ V S M μ T hT).exists
  rw [phiOf, dite_eq_left h]
  exact h.choose_spec

theorem phiOf_eq (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M)
    {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} (h : Represents μ Φ T) : phiOf μ T = Φ :=
  GlobalTheory.CuspIntertwiner.eq_of_represents (phiOf_spec hP hθ hT).2 h

variable {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}


variable (μ) in
def homOf (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M) (hf : ∀ w, f w ∈ allMaps θ M) :
    W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) where
  toFun w := phiOf μ (f w)
  map_add' w w' := by
    rw [map_add (f := _)]
    exact phiOf_eq hP hθ (add_mem (hf w) (hf w')) ((phiOf_spec hP hθ (hf w)).2.add (phiOf_spec hP hθ (hf w')).2)
  map_smul' c w := by
    rw [map_smul]
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (hf w)) ((phiOf_spec hP hθ (hf w)).2.smul c)

theorem homOf_apply (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M)
    (hf : ∀ w, f w ∈ allMaps θ M) (w : W) : homOf μ hP hθ f hf w = phiOf μ (f w) := rfl

open Classical in
theorem homOf_mem (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {f : W →ₗ[ℂ] MMap M}
    (hf : f ∈ homInto σ (finRep M) (allMaps θ M)) :
    homOf μ hP hθ f hf.1 ∈ homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := by
  unfold homFinDS
  rw [mem_homTensorPi]
  have hs := fun w => mem_homPi.1 (phiOf_spec (μ := μ) hP hθ (hf.1 w)).1
  refine ⟨fun w y => (hs w).1 y, fun g w y => ?_, fun i g w y => (hs w).2 i g y⟩
  rw [homOf_apply, homOf_apply, hf.2 g w]
  have hm : finRep M g (f w) ∈ allMaps θ M := by
    rw [← hf.2 g w]
    exact hf.1 _
  rw [phiOf_eq hP hθ hm ((phiOf_spec hP hθ (hf.1 w)).2.translate g)]
  rfl


variable (μ) in
def toHom (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    homInto σ (finRep M) (allMaps θ M) →ₗ[ℂ] homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) where
  toFun f := ⟨homOf μ hP hθ f.1 f.2.1, homOf_mem hP hθ f.2⟩
  map_add' f f' := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (add_mem (f.2.1 w) (f'.2.1 w))
      ((phiOf_spec hP hθ (f.2.1 w)).2.add (phiOf_spec hP hθ (f'.2.1 w)).2)
  map_smul' c f := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (f.2.1 w)) ((phiOf_spec hP hθ (f.2.1 w)).2.smul c)

theorem toHom_injective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    Function.Injective (toHom (σ := σ) (M := M) μ hP hθ) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext (LinearMap.ext fun w => ?_)
  have h0 : phiOf μ (f.1 w) = 0 := congrArg (fun Ψ : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) => Ψ.1 w) hf
  have hr := (phiOf_spec (μ := μ) hP hθ (f.2.1 w)).2
  rw [h0] at hr
  exact eq_of_represents_cont (continuous_of_mem_allMaps (f.2.1 w)) (fun _ => continuous_const) hr represents_zero


variable (σ) in
def stab (w : W) : Subgroup (GfC V) where
  carrier := {g | σ g w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

open Classical in
theorem toHom_surjective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hσ : GlobalTheory.PRep.IsSmooth σ) :
    Function.Surjective (toHom (σ := σ) (M := M) μ hP hθ) := by
  intro Ψ
  have hΨ := Ψ.2
  unfold homFinDS at hΨ
  rw [mem_homTensorPi] at hΨ
  obtain ⟨h1, h2, h3⟩ := hΨ
  have hΨ : ∀ w, Ψ.1 w ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := fun w => mem_homPi.2 ⟨h1 w, fun i g => h3 i g w⟩
  have hex : ∀ w, ∃ T ∈ allMaps θ M, Represents μ (Ψ.1 w) T := fun w =>
    GlobalTheory.CuspRepr.exists_allMaps D θ hθ V S M μ (Ψ.1 w) (hΨ w) (stab σ w) (hσ w) fun k hk y => by
      have hk' : σ k w = w := hk
      exact (h2 k w y).symm.trans (congrArg (fun u => Ψ.1 u y) hk')
  choose T hT hr using hex
  have hc : ∀ w v, Continuous (T w v) := fun w => continuous_of_mem_allMaps (hT w)
  let f : W →ₗ[ℂ] MMap M :=
    { toFun := T
      map_add' := fun w w' => eq_of_represents_cont (hc _) (fun v => (hc w v).add (hc w' v)) (hr (w + w'))
        (by rw [map_add (f := _)]; exact (hr w).add (hr w'))
      map_smul' := fun c w => eq_of_represents_cont (hc _) (fun v => (hc w v).const_smul c) (hr (c • w))
        (by rw [map_smul]; exact (hr w).smul c) }
  have hf : f ∈ homInto σ (finRep M) (allMaps θ M) :=
    ⟨hT, fun g w => eq_of_represents_cont (hc _) (fun v => (hc w v).comp (continuous_mul_const _)) (hr (σ g w))
      ((hr w).translate' g (h2 g w))⟩
  exact ⟨⟨f, hf⟩, Subtype.ext (LinearMap.ext fun w => phiOf_eq hP hθ (hT w) (hr w))⟩

end GlobalTheory.AutMult.MultAssembly

namespace GlobalTheory.AutMult


open GlobalTheory.AutMult.MultAssembly in
theorem cuspMult_eq_mCuspDS : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → GlobalTheory.CuspMult.cuspMult θ M σ = mCuspDS μ σ M := by
  intro hP _ _ D θ hθ V S M μ _ _ W _ _ σ hσ
  exact (LinearEquiv.ofBijective (toHom μ hP hθ) ⟨toHom_injective hP hθ, toHom_surjective hP hθ hσ⟩).rank_eq

end GlobalTheory.AutMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
section
open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd (D : D7) : GenusMassStd D :=
  GlobalTheory.DefiniteMass.mass_eq_massI D

theorem genusMassStd_of_landherrHasse :
    (∀ D : D7, LandherrHasse D) → ∀ D : D7, GenusMassStd D :=
  fun _ D => genusMassStd D

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuadCharOfOfIsNormChar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormChar

theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [hnorm w, hnorm (w.under (𝓞 K))]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem fixes_or {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosed Ω] [CharZero F] (h2 : Module.finrank F E = 2) (σ : G F Ω)
    (hσ : ∃ e : E, σ (algebraMap E Ω e) ≠ algebraMap E Ω e) (τ : G F Ω) :
    τ ∈ (res F Ω E).range ∨ σ⁻¹ * τ ∈ (res F Ω E).range := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ ρ : G F Ω, (∀ e : E, ρ (algebraMap E Ω e) = algebraMap E Ω e) → ρ ∈ (res F Ω E).range :=
    fun ρ hρ => ⟨AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρ, AlgEquiv.ext fun _ => rfl⟩
  let f : G F Ω → (E →ₐ[F] Ω) := fun ρ => (ρ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)
  have hf : ∀ ρ e, f ρ e = ρ (algebraMap E Ω e) := fun _ _ => rfl
  have hcard : Fintype.card (E →ₐ[F] Ω) = 2 := by rw [AlgHom.card, h2]
  obtain ⟨e₀, he₀⟩ := hσ
  have h01 : f 1 ≠ f σ := fun h => he₀ (by have := DFunLike.congr_fun h e₀; rw [hf, hf] at this; exact this.symm)
  by_cases h1 : f τ = f 1
  · left
    exact hfix τ fun e => by have := DFunLike.congr_fun h1 e; rw [hf, hf] at this; exact this
  · by_cases h2' : f τ = f σ
    · right
      refine hfix _ fun e => ?_
      have := DFunLike.congr_fun h2' e
      rw [hf, hf] at this
      rw [AlgEquiv.mul_apply, this]
      exact σ.symm_apply_apply _
    · exfalso
      have : 2 < Fintype.card (E →ₐ[F] Ω) :=
        Fintype.two_lt_card_iff.2 ⟨f 1, f σ, f τ, h01, Ne.symm h1, Ne.symm h2'⟩
      omega

end GlobalTheory.QuadNormChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubquotientPrinSeriesOfHasVec
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

theorem subquotient_prinSeries_of_hasVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → HasVec ψ π → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Agree ψ ω ∧ IsSubquotient π (prinSeries ω) := by
  intro hBZ k _ _ _ _ n ψ V _ _ π hπ hirr hψ hord hvec
  obtain ⟨v, hv0, hv⟩ := hvec
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  have hx0 : (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) ≠ 0 := by
    intro h
    exact hv0 (_root_.GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB k n ψ V π hπ hψ hord v ((Submodule.Quotient.mk_eq_zero _).1 h) hv)
  have hact : ∀ t ∈ torusO k (Fin n), jacB π t (Submodule.Quotient.mk v) =
      (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) := by
    intro t ht
    have hgrp : diagT k (Fin n) t ∈ grp ψ := by
      refine ⟨iwahori_le_KO k _ (diagT_mem_iwahori ht), fun i j hij => ?_⟩
      rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne]
      exact (_root_.GlobalTheory.PsType.triv_ev_props k).2.2.1 _
    have hth : theta ψ (diagT k (Fin n) t) = (torusChar ψ t : ℂ) := by
      rw [_root_.GlobalTheory.PsType.theta_of_triangular k n ψ (diagT k (Fin n) t) t ht (fun i => by rw [val_diagT, Matrix.diagonal_apply_eq])
        (Or.inr fun i j hij => by rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne'])]
      simp
    rw [UnramFixed.jacB_apply, jacBU_mk, hv _ hgrp, hth]
    have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
      UnramFixed.deltaHalf_torusO k ht
    rw [this]
    simp
  obtain ⟨ω, l, hl0, hω, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) (Submodule.Quotient.mk v) ψ
    (isSmooth_jacB hπ) hl hψ hx0 hact
  exact ⟨ω, fun i => GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hψ i) (hu i),
    fun i u hu' => (hu i u hu').symm,
    SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hω⟩

end GlobalTheory.PsType
end
end

