module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHalfData
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_half (v : HeightOneSpectrum (𝓞 F)) (x c : E) :
    compFin F E v (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] c) = (1 : Fv F v) ⊗ₜ[F] x := by
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    change evalV F v (1 : Af F) = 1; exact map_one _
  have h0 : evFin F v (pairA F 1 0) = 0 := by
    change evalV F v (0 : Af F) = 0; exact map_zero _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, add_zero]

theorem compInf_half (w : InfinitePlace F) (x : E) :
    compInf F E w (2 * (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E))) = 1 := by
  have h1 : evInf F w (pairA F 0 1) = 0 := by
    change GlobalTheory.AutFunCompare.evW w (0 : Ainf F) = 0; exact map_zero _
  have h0 : evInf F w (pairA F 1 0) = 1 := by
    change GlobalTheory.AutFunCompare.evW w (1 : Ainf F) = 1; exact map_one _
  rw [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, two_mul, map_add (f := _), map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, zero_add,
    ← TensorProduct.tmul_add, add_halves, ← Algebra.TensorProduct.one_def]

theorem sigR_half (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] σ x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E) := by
  have h2 : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h2]

theorem half_add (x y : E) (h : x + y = 1) :
    (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      (1 : AF F ⊗[F] E) := by
  have hae : pairA F 0 1 + pairA F 1 0 = (1 : AF F) := Prod.ext (zero_add 1) (add_zero 1)
  rw [show (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] (x + y) + pairA F 1 0 ⊗ₜ[F] (1 / 2 + 1 / 2 : E) by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel,
    h, add_halves, ← TensorProduct.add_tmul, hae, Algebra.TensorProduct.one_def]

end General

theorem exists_halfData : ∀ D : D7, ∃ t : AE D, HalfData t := by
  intro D
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram D.host.E D.sp.cm.cmUnram
  refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t₀ : D.host.E) + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 / 2 : D.host.E),
    ?_, fun v => ?_, fun w => compInf_half w _⟩
  · exact (congrArg _ (sigR_half D.sp.cm.sig _)).trans (half_add _ _ ht₀)
  · rw [compFin_half]
    exact tmul_mem_intLoc (one_mem _) t₀

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponents
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem tmulOne_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem scal_gen (σ : E →ₐ[F] E) (μ : E) (hμ : μ ≠ 0)
    (r : ∀ w : InfinitePlace F, w.Completion) (hr : ∀ w, r w ≠ 0)
    (hN : ∀ w, ((1 : w.Completion) ⊗ₜ[F] (μ * σ μ) : w.Completion ⊗[F] E) = 4 * (r w ⊗ₜ[F] (1 : E)) ^ 4)
    (u₀ : (AF F ⊗[F] E)ˣ) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * (u : AF F ⊗[F] E) * sigR (AF F) σ (u : AF F ⊗[F] E) = inclR (AF F) μ ∧
      (∀ v, compFin F E v u = compFin F E v u₀) ∧
      ∀ w, compInf F E w ((ε : AF F ⊗[F] E) * sigR (AF F) σ (ε : AF F ⊗[F] E)) = 4 := by
  set c := sigR (AF F) σ with hc
  set e : AF F ⊗[F] E := pairA F 1 0 ⊗ₜ[F] (1 : E) with he
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have hee : e * e = e := by rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  have hce : c e = e := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hfe : ∀ v, compFin F E v e = 0 := by
    intro v
    refine (tmulOne_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, show sndA F (pairA F 1 0) = 0 from rfl, map_zero, TensorProduct.zero_tmul]
  have hie : ∀ w, compInf F E w e = 1 := by
    intro w
    refine (tmulOne_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, show fstA F (pairA F 1 0) = 1 from rfl, map_one, Algebra.TensorProduct.one_def]
  let R : AF F := pairA F (fun w => r w) 1
  let R' : AF F := pairA F (fun w => (r w)⁻¹) 1
  have hRR : R * R' = 1 := Prod.ext (funext fun w => mul_inv_cancel₀ (hr w)) (mul_one (1 : Af F))
  set a : AF F ⊗[F] E := R ⊗ₜ[F] (1 : E) with ha
  set a' : AF F ⊗[F] E := R' ⊗ₜ[F] (1 : E) with ha'
  have haa : a * a' = 1 := by
    rw [ha, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hRR, Algebra.TensorProduct.one_def]
  have hca : c a = a := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hia : ∀ w, compInf F E w a = r w ⊗ₜ[F] (1 : E) := fun w =>
    tmulOne_map F E (evInf F w) (AlgHom.id F E) _
  have hu0 : (u₀ : AF F ⊗[F] E) * ↑u₀⁻¹ = 1 := Units.mul_inv u₀
  set x : AF F ⊗[F] E := e * a + (1 - e) * u₀ with hx
  set x' : AF F ⊗[F] E := e * a' + (1 - e) * ↑u₀⁻¹ with hx'
  have hxx : x * x' = 1 := by
    rw [hx, hx']
    linear_combination (2 - a * ↑u₀⁻¹ - (u₀ : AF F ⊗[F] E) * a') * hee + e * e * haa + (1 - e) * (1 - e) * hu0
  let U : (AF F ⊗[F] E)ˣ := ⟨x, x', hxx, by rw [mul_comm]; exact hxx⟩

  have hshape : ∀ y, c (e * a + (1 - e) * y) = e * a + (1 - e) * c y := by
    intro y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hce, hca]
  have hread : ∀ w y, compInf F E w (e * a + (1 - e) * y) = r w ⊗ₜ[F] (1 : E) := by
    intro w y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hie, hia]; ring
  let M : (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F) : E →+* AF F ⊗[F] E).toMonoidHom (Units.mk0 μ hμ)
  let P : (AF F ⊗[F] E)ˣ := U * Units.map c.toMonoidHom U
  refine ⟨U, M * P⁻¹, ?_, ?_, ?_⟩
  · have h1 : ((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U) = 1 := by
      have := Units.inv_mul P
      simpa [P] using this
    calc ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * U * c U
        = (M : AF F ⊗[F] E) * (((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U)) := by
          rw [Units.val_mul]; ring
      _ = inclR (AF F) μ := by rw [h1, mul_one]; rfl
  · intro v
    change compFin F E v x = _
    rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, hfe]; ring
  · intro w
    set φ := compInf F E w with hφ
    set ρ : w.Completion ⊗[F] E := r w ⊗ₜ[F] (1 : E) with hρdef
    have hρ : ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
      rw [hρdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ (hr w), Algebra.TensorProduct.one_def]
    have hP : (P : AF F ⊗[F] E) = x * c x := rfl
    have hM : (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] μ := rfl
    have hε : ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (x * c x) = M := by
      rw [← hP, ← Units.val_mul, inv_mul_cancel_right]
    have hε' := congrArg c hε
    rw [map_mul, map_mul] at hε'
    have hall : (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *
        ((x * c x) * (c x * c (c x))) = (M : AF F ⊗[F] E) * c M := by
      rw [← hε', ← hε]; ring
    have hφx : φ x = ρ := hread w _
    have hφcx : φ (c x) = ρ := by rw [hx, hshape, hread]
    have hφccx : φ (c (c x)) = ρ := by rw [hx, hshape, hshape, hread]
    have hcM : c (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] σ μ := by
      rw [hM, hc]
      change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] μ) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hφ1 : ∀ z : E, φ ((1 : AF F) ⊗ₜ[F] z) = (1 : w.Completion) ⊗ₜ[F] z := by
      intro z
      rw [hφ]
      change Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] z) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have hrhs : φ ((M : AF F ⊗[F] E) * c M) = 4 * ρ ^ 4 := by
      rw [map_mul, hcM, hM, hφ1, hφ1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hN w]
    have key := congrArg φ hall
    have hB : φ ((x * c x) * (c x * c (c x))) = ρ * ρ * (ρ * ρ) := by
      rw [map_mul, map_mul, map_mul, hφx, hφcx, hφccx]
    rw [map_mul φ _ ((x * c x) * (c x * c (c x))), hB, hrhs] at key
    linear_combination ((r w)⁻¹ ⊗ₜ[F] (1 : E)) ^ 4 * key -
      (φ (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) - 4) *
        (1 + ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 2 + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 3) * hρ
end

private theorem scal_pos (D : D7) (μ : D.host.E) (hμ : μ ≠ 0) (w : InfinitePlace D.host.F) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)
      (algebraMap D.host.F w.Completion ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩) := by
  set hw := NumberField.IsTotallyReal.isReal w
  set n : D.host.F := ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩ with hn
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  let φ : D.host.E →ₐ[D.host.F] ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in exact IsAlgClosed.lift
  have h1 : φ (algebraMap D.host.F D.host.E n) = w.embedding n := φ.commutes n
  have h2 : (algebraMap D.host.F D.host.E n) = μ * star μ := rfl
  have h3 : φ (star μ) = starRingEnd ℂ (φ μ) :=
    IsCMField.complexEmbedding_complexConj D.host.E (φ : D.host.E →+* ℂ) μ
  rw [h2, map_mul, h3, Complex.mul_conj] at h1
  have h4 : ((InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) : ℂ) = w.embedding n := by
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  have h5 : 0 < Complex.normSq (φ μ) := Complex.normSq_pos.2 (by simpa using hμ)
  have h6 := h4.trans h1.symm
  have h7 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) = Complex.normSq (φ μ) := by
    exact_mod_cast h6
  rw [h7]; exact h5

private theorem scal_root (F E : Type) [Field F] [Field E] [Algebra F E] (w : InfinitePlace F) (hw : w.IsReal) (n : F)
    (hn : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion n)) :
    ∃ r : w.Completion, r ≠ 0 ∧
      ((1 : w.Completion) ⊗ₜ[F] (algebraMap F E n) : w.Completion ⊗[F] E) = 4 * (r ⊗ₜ[F] (1 : E)) ^ 4 := by
  set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set t := f (algebraMap F w.Completion n) with ht
  have h0 : 0 < √(√(t / 4)) := by positivity
  have h4 : 4 * (f.symm √(√(t / 4))) ^ 4 = algebraMap F w.Completion n := by
    apply f.injective
    rw [map_mul, map_pow, map_ofNat, RingEquiv.apply_symm_apply, ← ht, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    ring
  refine ⟨f.symm √(√(t / 4)), (map_ne_zero f.symm).2 h0.ne', ?_⟩
  have h5 := congrArg (Algebra.TensorProduct.includeLeftRingHom : w.Completion →+* w.Completion ⊗[F] E) h4
  rw [map_mul, map_pow, map_ofNat, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply] at h5
  rw [h5, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_scal_real : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  intro D μ hμ u₀
  choose r hr hN using fun w : InfinitePlace D.host.F =>
    scal_root D.host.F D.host.E w _ _ (scal_pos D μ hμ.1 w)
  exact scal_gen D.host.F D.host.E D.sp.cm.sig μ hμ.1 r hr hN u₀

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalComplementPreimageOfFixLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

namespace GlobalTheory.LineFix


set_option maxHeartbeats 1000000 in
theorem exists_emb_of_fix_line : ∀ {D : D7} {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E),
    IsLineVec L ζ → ∀ (b : GA D S₀), (mt S₀ b *ᵥ (fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k)) →
      ∃ a : GA D A, o.emb (a, 1) = b := by
  intro D S₀ A L o ζ hζ b hb
  have hv : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ (fun k => incA D (ζ k)) := by
    funext k
    exact RingHom.map_mulVec (incA D) o.iB ζ k
  have hr := hζ.1
  obtain ⟨k0, hk0⟩ : ∃ k0 : Fin L.rank, ∀ k, k = k0 :=
    ⟨⟨0, by omega⟩, fun k => Fin.ext (by have := k.2; simp only; omega)⟩
  have hz : ζ k0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun k => by rw [hk0 k, h0]; rfl
    rw [this]; simp
  have hu : IsUnit (incA D (ζ k0)) := (isUnit_iff_ne_zero.2 hz).map (incA D)
  have h1 : mt S₀ b * o.jB = o.jB := by
    have e := hb
    rw [hv, Matrix.mulVec_mulVec] at e
    funext i k
    rw [hk0 k]
    have ei := congrFun e i
    simp only [Matrix.mulVec, dotProduct] at ei
    rw [Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk),
      Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk)] at ei
    exact hu.mul_right_cancel ei
  have hu2 : GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * mt S₀ b) = gA S₀ := GlobalTheory.MixModel.mt_unitary S₀ b
  have h2' : GlobalTheory.MixModel.adj o.jB * (gA S₀ * (mt S₀ b * o.jA)) = 0 := by
    calc GlobalTheory.MixModel.adj o.jB * (gA S₀ * (mt S₀ b * o.jA))
        = GlobalTheory.MixModel.adj (mt S₀ b * o.jB) * (gA S₀ * (mt S₀ b * o.jA)) := by rw [h1]
      _ = GlobalTheory.MixModel.adj o.jB * (GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * (mt S₀ b * o.jA))) := by
          rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc]
      _ = 0 := by rw [GlobalTheory.MixModel.cancel₃ hu2, o.gram_BA]
  have h2 : o.pB * (mt S₀ b * o.jA) = 0 := by
    rw [o.pB_eq]; simp only [Matrix.mul_assoc]; rw [h2', Matrix.mul_zero]
  have h3 : mt S₀ b * o.jA = o.jA * (o.pA * (mt S₀ b * o.jA)) := by
    calc mt S₀ b * o.jA = (o.jA * o.pA + o.jB * o.pB) * (mt S₀ b * o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA * (o.pA * (mt S₀ b * o.jA)) := by
          rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc o.jB, h2, Matrix.mul_zero, add_zero]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Mx D A.rank A.rank, mt S₀ b * o.jA = o.jA * a₀ := ⟨_, h3⟩
  have h4 : GlobalTheory.MixModel.adj a₀ * (gA A * a₀) = gA A := by
    have e : GlobalTheory.MixModel.adj (mt S₀ b * o.jA) * (gA S₀ * (mt S₀ b * o.jA)) = gA A := by
      rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu2, o.gram_AA]
    rw [ha₀, GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA] at e
    exact e
  have e3 : mt S₀ b * o.jA * o.pA + mt S₀ b * o.jB * o.pB = mt S₀ b * (o.jA * o.pA + o.jB * o.pB) := by
    rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have e4 : mt S₀ b * (o.jA * o.pA + o.jB * o.pB) = mt S₀ b := by
    rw [o.sum_eq_one]; exact Matrix.mul_one _
  refine ⟨GlobalTheory.MixModel.ofMat A a₀ h4, GlobalTheory.MixModel.mt_injective S₀ ?_⟩
  have e1 : mt S₀ (o.emb (GlobalTheory.MixModel.ofMat A a₀ h4, 1)) = o.jA * a₀ * o.pA + o.jB * o.pB := by
    rw [OrthDec.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e2 : o.jA * a₀ * o.pA + o.jB * o.pB = mt S₀ b * o.jA * o.pA + mt S₀ b * o.jB * o.pB := by
    rw [← ha₀, h1]
  rw [e1, e2, e3, e4]

end GlobalTheory.LineFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_GQ_of_unitary {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (γ : GL (Fin n) D.host.E)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Matrix.reindex (finCongr hn) (finCongr hn) (HSpace.gram V))) :
    ∃ a : GA D V, a ∈ GQ V ∧
      GlobalTheory.AdForm.finM V hn a =
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧
      ∀ τ, GlobalTheory.AdForm.infM θ V hn a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  subst hn
  have hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V := hγ
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ ∈
      HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by
    change Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) *
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) =
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))
    have e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j
      rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩
  · ext i j
    rfl
  · ext i j
    exact (hθ τ).1 (γ.1 i j)

theorem exists_GQ_of_unitary0 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ :=
  fun D θ hθ γ hγ => exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

open scoped ComplexOrder

namespace GlobalTheory.CenterVac

variable {D : D7}

theorem lintegral_enorm_sq_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℂ}
    (h : ∫ w in s, ‖f w‖ ^ 2 ∂μ = 1) : ∫⁻ w in s, ‖f w‖ₑ ^ 2 ∂μ = 1 := by
  have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict s) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
  have e := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)
  rw [h, ENNReal.ofReal_one] at e
  rw [e]
  refine lintegral_congr fun w => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem om_vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S}
    {y : DefSp T} (hx : x.Is) (hy : y.Is) {k : KerDat S T} (hk : k.Is ψ θ x y) {z : GA D S} (hz : z ∈ GinfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := by
  obtain ⟨χS, χT, hom⟩ := hk.weil
  obtain ⟨hψ, hv⟩ := hk.vac
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hdet : ∀ τ, (gramAt D S τ).det ≠ 0 := fun τ h0 => by
    have := (hx.cart τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S hdet z hz
  have hy1 : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  obtain ⟨a, ha⟩ : ∃ a : ℂ, k.om (z, 1) k.vac = a • k.vac :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT k.om η hη hom x.s y.s hx.cart hy.cart z hz 1 (one_mem _)
      (fun τ => by rcases hx.pm τ with h | h <;> rw [h] <;> simp) (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1
      k.vac hv.theta hv.fock⟩
  refine ⟨a, ?_, ha⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hv.norm
  have n1 : nrm2 p.1 p.2 k.vac = 1 := hn p hp
  obtain ⟨hH, hF, -⟩ := hp
  have hu := hom.om_unit p.1 p.2 hH hF (z, 1) k.vac hv.theta
  have hL := lintegral_enorm_sq_eq_one (μ := p.1) (s := p.2) (f := k.vac) n1
  rw [ha] at hu
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hu
  rw [lintegral_const_mul' _ _ (by simp), hL, mul_one] at hu
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hu
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 hu

theorem exists_center_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  intro D ψ θ hθ S T x y hx hy k hk
  have h : ∀ z : GA D S, ∃ c : ℂ, z ∈ GinfC S → ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := fun z => by
    by_cases hz : z ∈ GinfC S
    · obtain ⟨c, hc⟩ := om_vac_eq_smul hθ hx hy hk hz
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose c hc using h
  exact ⟨c, fun z hz _ => hc z hz⟩

end GlobalTheory.CenterVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem finite_monomials_of_placeDegree : ∀ (D : D7) (m n : ℕ) (d : D.what₂.Tau → ℕ), {α : FVar D m n →₀ ℕ | ∀ τ, (∑ v ∈ α.support with v.1 = τ, α v) = d τ}.Finite := by
  intro D m n d
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : FVar D m n => d v.1))).subset ?_
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  rw [Set.mem_Iic, Finsupp.le_def]
  intro v
  rw [Finsupp.coe_equivFunOnFinite_symm]
  by_cases hv : v ∈ α.support
  · rw [← hα v.1]
    exact Finset.single_le_sum (f := fun w => α w) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, rfl⟩)
  · rw [Finsupp.notMem_support_iff.1 hv]
    exact Nat.zero_le _

end GlobalTheory
end

