module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruence
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongOpen

section Lemmas

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem kappa_one_tmul (F : FinIso L n) (a : AFplus L) :
    F.κ (1 ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  refine FiniteAdeleRing.ext _ fun w ↦ ?_
  obtain ⟨i, hi, hia⟩ := F.right w (w.under (𝓞 (maximalRealSubfield L))) rfl
  rw [hia]
  change i (a (w.under (𝓞 (maximalRealSubfield L)))) =
    GlobalTheory.LFun.complMap rfl (a (w.under (𝓞 (maximalRealSubfield L))))
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
    (w.under (𝓞 (maximalRealSubfield L)))).equalizer hi
    (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k ↦ ?_)) _
  change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap]
  have h1 : (algebraMap (maximalRealSubfield L) (AFplus L) k) (w.under (𝓞 (maximalRealSubfield L))) =
      algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (w.under (𝓞 (maximalRealSubfield L)))) k := rfl
  rw [← h1, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
  rfl

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ (x ⊗ₜ a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  rw [← kappa_one_tmul, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem mem_ALint_of_kappa (F : FinIso L n) {y : AL L} (hy : F.κ y ∈ Formalism.UG.intAd L) :
    y ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (F := maximalRealSubfield L) (E := L)
    (ι := F.κ.toRingHom) (fun x a ↦ kappa_tmul F x a) hy
  refine (Subring.closure_le.2 ?_) h
  rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
  · obtain ⟨r, hr⟩ := x.2
    exact Subring.subset_closure (Or.inl ⟨r, by show (x : L) ⊗ₜ _ = _; rw [← hr]⟩)
  · exact Subring.subset_closure (Or.inr ⟨a.1, a.2, rfl⟩)

end Lemmas

theorem exists_open_cong : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ),
    0 < N → ∃ O : Set (finU (E := L) (n := n)), IsOpen O ∧ (1 : finU (E := L) (n := n)) ∈ O ∧
      ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  intro L _ _ _ n F N hN
  set c : Af L := algebraMap L (Af L) (N : L)⁻¹ with hc
  let S : Set (Af L) := {z | z * c ∈ Formalism.UG.intAd L}
  have hI : IsOpen ((Formalism.UG.intAd L : Subring (Af L)) : Set (Af L)) :=
    RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring _)
  have hS : IsOpen S := hI.preimage (continuous_id.mul continuous_const)
  let f : Fin n → Fin n → finU (E := L) (n := n) → Af L := fun s t k ↦
    pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) -
      pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t)
  have hm : Continuous (fun k : finU (E := L) (n := n) ↦ (((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hp : Continuous (pFin L) := continuous_snd
  have hf : ∀ s t, Continuous (f s t) := fun s t ↦
    (hp.comp (hm.matrix_elem s t)).sub continuous_const
  refine ⟨{k | ∀ s t, f s t k ∈ S}, ?_, ?_, ?_⟩
  · have e : {k | ∀ s t, f s t k ∈ S} = ⋂ s, ⋂ t, (f s t) ⁻¹' S := by ext; simp
    rw [e]
    exact isOpen_iInter_of_finite fun s ↦ isOpen_iInter_of_finite fun t ↦ hS.preimage (hf s t)
  · intro s t
    have e : f s t 1 = 0 := by simp [f]
    show f s t 1 * c ∈ Formalism.UG.intAd L
    rw [e, zero_mul]
    exact zero_mem _
  · intro k hk x hx
    have hloc : ∀ s t, F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      refine FiniteAdeleRing.ext _ fun w ↦ ?_
      rw [← F.loc x w s t, hx]
      rfl
    have hone : ∀ s t, F.κ ((1 : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      by_cases h : s = t <;> simp [Matrix.one_apply, h]
    have key : ∀ s t, ∃ y ∈ ALint L, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
        (1 : Matrix (Fin n) (Fin n) (AL L)) s t = (N : AL L) * y := by
      intro s t
      have h1 : f s t k * c ∈ Formalism.UG.intAd L := hk s t
      have hz : F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
          (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = f s t k := by
        simp only [f, map_sub, hloc, hone]
      refine ⟨F.κ.symm (f s t k * c), mem_ALint_of_kappa F (by rw [RingEquiv.apply_symm_apply]; exact h1), ?_⟩
      apply F.κ.injective
      rw [hz, map_mul, RingEquiv.apply_symm_apply, map_natCast, mul_comm (f s t k), ← mul_assoc, hc,
        ← map_natCast (algebraMap L (Af L)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'),
        map_one, one_mul]
    have hU : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t ∈ ALint L := by
      intro s t
      obtain ⟨y, hy, e⟩ := key s t
      rw [sub_eq_iff_eq_add] at e
      rw [e]
      refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
      by_cases h : s = t
      · simp [Matrix.one_apply, h, one_mem]
      · simp [Matrix.one_apply, h, zero_mem]
    exact ⟨hU, key⟩

end GlobalTheory.CongOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Hk3

namespace GlobalTheory.DownLift.Params

variable {D : D7}

theorem mem_bddAut_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {f : GA D V → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : f ∈ GlobalTheory.FinZeta.bddAut V := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V hpos
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨hc, hl, b, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hcC, rfl⟩ := hcov g
  rw [hl γ hγ]
  exact hb c hcC

theorem level_abs {Γ Gf W : Type} [Group Γ] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gf}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gf} {χ : J →* ℂˣ} {f : Gf → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    {k : Gf} (hk : k ∈ J) (h : Gf) : f (h * k) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • f h := by
  have h3 := hf 1 h ⟨k, hk⟩
  rw [map_one, map_one, one_mul] at h3
  exact h3

theorem ext_level {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ)
    {k : GA D V} (hk : k ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * k) = levChi V β (flag1L L) k • c.ext f h := by
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := hk.2
  exact (GlobalTheory.DefLiftHecke.ext_mul c hc f hk.1 h).trans ((congrArg (c.ρ h⁻¹) (level_abs hf hJ _)).trans (map_smul _ _ _))

theorem exists_coord_ne {V : HSp D} (c : CoefA V) {f : Bridge.Gf V → c.W} (h0 : f ≠ 0) :
    ∃ ℓ : c.W →ₗ[ℂ] ℂ, (fun h => ℓ (c.ext f h)) ≠ 0 := by
  obtain ⟨u, hu⟩ := Function.ne_iff.1 h0
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective u
  have h1 : c.ext f g ≠ 0 := fun e => hu (by
    have e' : c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)) = 0 := e
    have := congrArg (c.ρ g) e'
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this)
  refine ⟨innerₛₗ ℂ (c.ext f g), Function.ne_iff.2 ⟨g, fun e => h1 ?_⟩⟩
  exact inner_self_eq_zero.1 e


set_option maxHeartbeats 1000000 in
theorem exists_param_definite {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (h0 : f ≠ 0) (s : Sys D)
    (he : ∀ P d, P.under (𝓞 D.host.F) ∉ S → IsLab V P d → hkF V P (Finsupp.single d 1) f = s P d • f) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  obtain ⟨ℓ, hℓ⟩ := exists_coord_ne c h0
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ (flag1L L) S hB hS).1
  have hbd : (fun h => ℓ (c.ext f h)) ∈ GlobalTheory.FinZeta.bddAut V :=
    mem_bddAut_of_posDef hs hp (ℓ.continuous_of_finiteDimensional.comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf))
      fun γ hγ g => congrArg ℓ (GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ g)
  have hlev : ∀ k ∈ (levG V β (flag1L L) : Set (GA D V)), ∀ g,
      (fun h => ℓ (c.ext f h)) (g * k) = levChi V β (flag1L L) k * (fun h => ℓ (c.ext f h)) g := fun k hk g =>
    (congrArg ℓ (ext_level c hc hf hk g)).trans (map_smul _ _ _)
  have heig : ∀ w d R, Hecke₂ V (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) S w d R →
      heckeLin V R (fun h => ℓ (c.ext f h)) = s w d • fun h => ℓ (c.ext f h) := fun w d R hR => by
    have hw : w.under (𝓞 D.host.F) ∉ S := by
      obtain ⟨_, _, _, _, h, -⟩ := hR
      exact (GlobalTheory.GoodPrimes.offS_iff S w).1 h
    have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
    obtain ⟨hk, hop, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 fun PP hPP =>
      ⟨fun e => hw (e ▸ hS PP hPP), fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ hS PP hPP)⟩
    have hR' : SphOp V w d R := ((hop S d R).1 hR).2
    have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR').2 _ (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ)
      (fun h => ℓ (c.ext f h)) fun k hkk => funext fun g => by
        have := hlev k (hk k hkk).1 g
        rwa [(hk k hkk).2, one_mul] at this
    funext g
    have h3 := congrFun h2 g
    have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
    rw [he w d hw ⟨R, hR'⟩, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_smul] at h4
    rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
      Finset.sum_apply] at h3
    have h5 := congrArg ℓ h4
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Pi.smul_apply, map_smul] at h5
    exact h3.trans h5.symm
  obtain ⟨B, hB', -⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D V _ _ S hsph _ hbd hℓ hlev s heig
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph hℓ hlev heig B).1 hB'⟩

theorem exists_param_part (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : InfFam D}
    (hθ : IsInfFam θ) {M : DSModel V Sp}
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) {s : Sys D}
    (h : partFull θ M (levS V β L) (levChi V β L) S s ≠ ⊥) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ S →
      ∀ a ∈ B w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ L S hB hS).1
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨v, hv⟩ : ∃ v, U v ≠ 0 := by
    by_contra h
    push Not at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨h1, h2⟩ := (mem_partFull θ M _ _ S s U).1 hU
  have h3 := (GlobalTheory.MultMem.mem_mult_iff ..).1 h1
  obtain ⟨B, hB', hb⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D V _ _ S hsph (U v)
    ⟨(h3.aut v).cont, (h3.aut v).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h3.aut v) (h3.cusp v)⟩ hv (h3.lev v) s
    fun P d R hR => h2 P d R hR v
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_of_mem_partFull hsph hU hv B).1 hB', fun w hw => (hb w hw).2⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem under_mem_badPl (t : T) {PP : Pl D.host.E} (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) :
    (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 h, rfl⟩

theorem good_iff (t : T) (P : Pl D.host.E) : Good R t P ↔ P.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  constructor
  · intro h hm
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2⟩ := h PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h3 | h3
    · exact h1 h3.symm
    · exact h2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h3)
  · intro hw PP hPP
    exact ⟨fun e => hw (e ▸ under_mem_badPl R t hPP),
      fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ under_mem_badPl R t hPP)⟩

theorem paramsV {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (h) (hh : IsOpsV R i t h) (s y)
    (hy : IsEigV R i t h s y) (h0 : y ≠ 0) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B :=
  exists_param_definite (D.sp.V_sig _) (hC.models.vpos i) (R.cV i) (hC.models.cV i) (hC.lev.βV i) (L := R.datVt i t)
    (fun _ hPP => under_mem_badPl R t hPP) ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y))
    (fun e => h0 ((hC.models.HV i t).1 (e.trans (map_zero _).symm))) s fun P d hP hd =>
      (hh P ((good_iff R t P).2 hP) _ y).symm.trans
        ((congrArg (R.HV i t).e (hy P d ((good_iff R t P).2 hP) hd)).trans (map_smul _ _ _))

theorem paramsW (hP : GlobalTheory.Published.CuspRapidDecay) {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (c : Sys D)
    (hc : partW R i t c ≠ ⊥) : ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  obtain ⟨B, h1, h2⟩ := exists_param_part hP hC.models.inf (hC.lev.βW i) (L := R.datWp i R.triv)
    (fun PP hPP => under_mem_badPl R t (hPP.imp_right fun h => absurd h (Finset.notMem_empty _))) hc
  rw [rW] at h1 h2
  exact ⟨B, h1, fun w hw => h2 w ((good_iff R t w).1 hw)⟩

theorem paramsEx : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, ParamsEx R i t :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ R _ hG _ i t => ⟨paramsV R hG.core i t, paramsW R hP hG.core i t⟩

end GlobalTheory.DownLift.Params

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL (k := k)} (h : Toral x) : Good x := by
  obtain ⟨s, hs, h1⟩ := h
  exact ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

theorem fixed_ne_bot_of_mem_support {x : IrrGL (k := k)} (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥)
    {s : Multiset (IrrGL (k := k))} (hs : HasSupport x.rep s) {y : IrrGL (k := k)} (hy : y ∈ s) :
    fixed y.rep (KOne k (Fin y.1)) ≠ ⊥ := by
  obtain ⟨h, z, rfl, -, -, e, he⟩ := hs
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hx
  obtain ⟨w, hw, hw0⟩ := DepthZero.fixed_of_isSubquotient e (fun a => (z a).rep) he ⟨v, hv, hv0⟩ a
  exact (Submodule.ne_bot_iff _).2 ⟨w, hw, hw0⟩

theorem good_of_fixed_KOne (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hk : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) (x : IrrGL (k := k))
    (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ x
  exact ⟨s, hs, fun y hy => Or.inr ⟨hk, y, 1, isSmoothChar_one, fixed_ne_bot_of_mem_support hx hs hy,
    (IrrGL.tw_one y _).symm⟩⟩

theorem good_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL (k := k)) (hx : IsSpherical x.rep) :
    Good x :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical hBZ k x hx).2

end Local

def TameAtG (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.w = D.naut.plGw k v →
    NG.IsCompAt (tup (D.nd.mu i) j) s ξ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1

end GlobalTheory.AVGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.StepGlobalPf

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chi_one_eq_one (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  have h1 : mapM (toK D.nd i) (rO D.nd i r π) γ = 1 := by
    simp [mapM, rO, hγ]
  simp only [h1, Matrix.one_mulVec, hu, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

theorem noChiOff (Xs : Set (D.nd.X i)) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : GlobalTheory.Cut.NoChiOff i r Xs := by
  intro x _ hxZ u hu
  by_contra hu0
  refine hxZ (hG6 x ⟨u, hu0, fun g => ?_⟩)
  have h := hu g
  rw [rTwO, mapM_twistM, Matrix.smul_mulVec] at h
  conv_rhs => rw [← h]
  rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    one_smul]

theorem unrOut (Xs : Set (D.nd.X i)) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    GlobalTheory.Cut.UnrOut i r Xs := by
  intro v hvl hvS hvQ x _ γ hγ
  have hχ := chi_one_eq_one i r ρ π hD (hG4 π v hvl hvS hvQ γ hγ)
  have hx : rO D.nd i r x γ = 1 := by simp [rO, hG4 x v hvl hvS hvQ γ hγ]
  rw [rTwO, twistM]
  simp [hx, hχ]

theorem atS (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.S i, (GlobalTheory.Cut.QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ GlobalTheory.Cut.PolyAt i r Xs π v := by
  intro v hv
  have hS := ((D.nd.S_def i v).1 hv).1
  have hv5 := hG5 v (Or.inl hv)
  have hv5x := hG5x v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hv5.2 hk hv hv5x.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hv5.1 (Or.inr hp)) x).1 γ hγ, hv5x.2.2.2 hv hp⟩

theorem atQ (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.Q i, GlobalTheory.Cut.QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1 := fun v hv =>
  ⟨fun x _ γ hγ => ((hG5 v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ, (hG5x v (Or.inr hv)).2.2.1 hv⟩


end GlobalTheory.StepGlobalPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupportStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  first
  | exact @GlobalTheory.JSW.lastRow_finite_compact
  | exact GlobalTheory.JSW.lastRow_finite_compact
  | (intros; apply GlobalTheory.JSW.lastRow_finite_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerUnipotentConjBlockFormulas
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_conj_block_formulas : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  first | (exact @GlobalTheory.SchurExt.schur_mul_conjLowUni) | (exact GlobalTheory.SchurExt.schur_mul_conjLowUni) | (intros; apply GlobalTheory.SchurExt.schur_mul_conjLowUni  <;> assumption)
end

