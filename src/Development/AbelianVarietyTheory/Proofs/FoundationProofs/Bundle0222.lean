module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0007
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0002
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HomDual

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← h, ← h, star_star]

theorem pairing_mem (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L)
    {u x : Fin N → D.host.E} (hu : u ∈ L) (hx : x ∈ L) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = ∑ b, D.host.conj (u b) * x b := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨c, hc⟩ := (hL.2.2 x).1 hx u hu
  refine ⟨c, hc.trans ?_⟩
  simp only [stdH, h]

theorem exists_resolution (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : SD D L) : ∃ (m : ℕ) (v w : Fin m → Fin N → D.host.E), (∀ i, v i ∈ L) ∧ (∀ i, w i ∈ L) ∧
      ∀ (u : Fin N → D.host.E) (a : Fin N),
        u a = ∑ i, (∑ b, u b * D.host.conj (w i b)) * v i a := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x := h
  have hh : ∀ x y : Fin N → D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y := by
    intro x y
    rw [GlobalTheory.DualFamily.herm_one_eq]
    simp only [stdH, h, h', mul_comm]
  have hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z :=
    fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨-, m, v, w, hv, hw, he⟩ := GlobalTheory.exists_dual_family L hL.1
    (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy)
    (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)
  refine ⟨m, v, w, hv, hw, fun u a => ?_⟩
  have := congrFun (he u) a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']
    using this

theorem rank_one_mem (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) {c : D.host.E}
    (hc : c ∈ D.host.AA0) {u : Fin N → D.host.E} (hu : u ∈ L) {v : Fin N' → D.host.E}
    (hv : v ∈ L') :
    c • (Matrix.of fun a b => v a * D.host.conj (u b)) ∈ YYl D L L' := by
  refine Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩
  obtain ⟨e, he⟩ := pairing_mem D hL hu hx
  have : (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v := by
    funext a
    change ∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a
    rw [he, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact L'.smul_mem e hv

theorem exists_dual_family_hom : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  rintro D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'
  obtain ⟨m, u, u', hu, hu', eu⟩ := exists_resolution D hL
  obtain ⟨m', v, v', hv, hv', ev⟩ := exists_resolution D hL'
  let Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)
  let Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)
  let e := (Fintype.equivFin (Fin m' × Fin m × Fin r)).symm
  refine ⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _),
    fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩
  refine Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm
  refine Matrix.ext fun s t => ?_
  have eu' : ∀ (z : Fin N → D.host.E) (t : Fin N),
      z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t) := by
    intro z t
    have := congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, conj_conj] using this
  have hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E
      ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k)) := by
    intro j i k
    unfold hYY
    congr 1
    simp only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT]
  simp only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]
  congr 1
  ring

end GlobalTheory.HomDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

namespace TraceDualFamily

open scoped nonZeroDivisors

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

lemma conj_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (x : E) : c (c x) = x := by
  apply φ₀.injective
  rw [hc, hc, Complex.conj_conj]

lemma mem_range_iff (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

lemma isIntegral_trace_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (z : E)
    (hz : IsIntegral ℤ (Algebra.trace K E z)) : IsIntegral ℤ (Algebra.trace K E (c z)) := by
  letI : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have h1 : algebraMap K ℂ (Algebra.trace K E (c z)) =
      starRingEnd ℂ (algebraMap K ℂ (Algebra.trace K E z)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [trace_eq_sum_embeddings ℂ, trace_eq_sum_embeddings ℂ, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc (σ : E →+* ℂ) z
  have h2 : IsIntegral ℤ (algebraMap K ℂ (Algebra.trace K E (c z))) := by
    rw [h1]
    exact (hz.map (algebraMap K ℂ).toIntAlgHom).map (starRingEnd ℂ).toIntAlgHom
  exact (isIntegral_algHom_iff (algebraMap K ℂ).toIntAlgHom (algebraMap K ℂ).injective).mp h2

lemma isLocalizedModule_subtype (Λ : Submodule (𝓞 K) E)
    (h : Submodule.span K (Λ : Set E) = ⊤) : IsLocalizedModule (𝓞 K)⁰ Λ.subtype := by
  refine {
    map_units := (isLocalizedModule_id (𝓞 K)⁰ E K).map_units
    surj := ?_
    exists_of_eq := ?_ }
  · intro y
    have hy : y ∈ Submodule.span K (Λ : Set E) := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 K)⁰ K _ y hy
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨_, ht⟩, t), rfl⟩
  · intro x₁ x₂ hxy
    exact ⟨1, by simpa using hxy⟩

theorem exists_family (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x))
    (I : FractionalIdeal (𝓞 E)⁰ E)
    (hI : ∀ x : E, x ∈ I ↔ ∀ y ∈ I, Algebra.trace K E (x * c y) ∈ (algebraMap (𝓞 K) K).range) :
    ∃ (r : ℕ) (a a' : Fin r → E), (∀ k, a k ∈ I) ∧ (∀ k, a' k ∈ I) ∧
      ∀ t : E, t = ∑ k, (Algebra.trace K E (t * c (a' k))) • a k := by
  have hI0 : I ≠ 0 := by
    rintro rfl
    have := (hI 1).mpr (by
      intro y hy
      rw [FractionalIdeal.mem_zero_iff] at hy
      subst hy
      simp)
    rw [FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  let Λ : Submodule (𝓞 K) E := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have hsp : Submodule.span K (Λ : Set E) = ⊤ := by
    obtain ⟨x, hx, hx0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI0
    rw [eq_top_iff]
    intro t _
    have hx' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx
    have halg : IsAlgebraic ℤ (t / algebraMap (𝓞 E) E x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hmem : (n : E) * t ∈ Λ := by
      have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hn⟩ : 𝓞 E) hx0
      convert this using 1
      change _ ↔ (n • (t / algebraMap (𝓞 E) E x)) * algebraMap (𝓞 E) E x ∈ _
      rw [zsmul_eq_mul, mul_assoc, div_mul_cancel₀ _ hx']
      rfl
    have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
    have : t = (n : K)⁻¹ • ((n : E) * t) := by
      have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
      rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel_left₀ hnE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.mpr
    (Submodule.FG.restrictScalars (FractionalIdeal.fg_of_isNoetherianRing le_rfl I))
  have : Module.FinitePresentation (𝓞 K) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg'⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) Λ
  have := isLocalizedModule_subtype Λ hsp
  have hext : ∀ i : Fin m, ∃ w : E, ∀ y : Λ, Algebra.trace K E ((y : E) * c w) = (g y i : K) := by
    intro i
    let φ : Λ →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K ∘ₗ LinearMap.proj i ∘ₗ g
    let ψ : E →ₗ[𝓞 K] K := IsLocalizedModule.lift (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K))
    obtain ⟨u, hu⟩ := ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).surjective
      (ψ.extendScalarsOfIsLocalization (𝓞 K)⁰ K)
    refine ⟨c.symm u, fun y => ?_⟩
    have h1 := LinearMap.congr_fun hu (y : E)
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    rw [AlgEquiv.apply_symm_apply, mul_comm, h1]
    exact IsLocalizedModule.lift_apply (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K)) y
  choose w hw using hext
  refine ⟨m, fun i => (f (Pi.single i 1) : E), w, fun i => Subtype.prop (f (Pi.single i 1)),
    fun i => ?_, ?_⟩
  · refine (hI _).mpr fun y hy => (mem_range_iff _).mpr ?_
    have e : w i * c y = c (y * c (w i)) := by rw [map_mul, conj_conj c φ₀ hc, mul_comm]
    rw [e]
    refine isIntegral_trace_conj c φ₀ hc _ ?_
    rw [hw i ⟨y, hy⟩]
    exact RingOfIntegers.isIntegral_coe _
  · intro u
    have hu : u ∈ Submodule.span K (Λ : Set E) := hsp ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      have h1 : f (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hfg' _
      have h2 : g ⟨y, hy⟩ = ∑ i, g ⟨y, hy⟩ i • (Pi.single i 1 : Fin m → 𝓞 K) := by
        ext j; simp [Pi.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h2, map_sum] at h1
      have h3 := congrArg Subtype.val h1
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hw i ⟨y, hy⟩]
      exact (algebraMap_smul K _ _).symm
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      simp [add_mul, Finset.sum_add_distrib, add_smul]
    | smul a x _ hx =>
      conv_lhs => rw [hx]
      simp [Finset.smul_sum, mul_smul]

end TraceDualFamily

theorem exists_trace_dual_family_halfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k :=
  fun D => TraceDualFamily.exists_family D.host.conj D.host.φ₀
    (fun φ x => D.host.conjE_apply φ x) D.host.AA0
    (factMMUnimodular D.R D.host)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.UnramHecke

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [div_mul_div_comm]

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

theorem phase_of_norm (z : ℂˣ) (h : ‖(z : ℂ)‖ = 1) : phase z = z := by
  ext; rw [phase_val, h]; simp

theorem exists_unitary_extension {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (χ : A →* ℂˣ)
    (hk : ∀ a, Φ a = 1 → χ a = 1) (hu : ∀ a, ‖((χ a : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : M →* ℂˣ, (∀ x, κ (Φ x) = χ x) ∧ ∀ y, ‖((κ y : ℂˣ) : ℂ)‖ = 1 := by
  let _ : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  let _ : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift Φ)) (QuotientGroup.kerLift_injective Φ)
    (MonoidHom.toAdditive (QuotientGroup.lift Φ.ker χ fun a ha => hk a ha))
  refine ⟨phase.comp (MonoidHom.toAdditive.symm ρ), fun x => ?_, fun y => norm_phase _⟩
  have h : (MonoidHom.toAdditive.symm ρ) (Φ x) = χ x :=
    DFunLike.congr_fun hρ (Additive.ofMul (QuotientGroup.mk x))
  rw [MonoidHom.comp_apply, h, phase_of_norm _ (hu x)]

variable (D : D7)

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = starRingEnd ℂ (σ z) :=
  D.host.conjE_apply σ z

theorem conj_conj (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem sgA_sgA (x : AE D) : sgA D (sgA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]

theorem sgU_sgU (x : (AE D)ˣ) : sgU D (sgU D x) = x := Units.ext (sgA_sgA D x)

theorem sgA_mem {x : AE D} (hx : x ∈ OhE D) : sgA D x ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hx

def intUnits : Subgroup (AE D)ˣ where
  carrier := {u | IntU D u}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul]; exact mul_mem ha.1 hb.1,
    by rw [mul_inv, Units.val_mul]; exact mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem sgU_mem {u : (AE D)ˣ} (hu : u ∈ intUnits D) : sgU D u ∈ intUnits D :=
  ⟨sgA_mem D hu.1, by rw [← map_inv]; exact sgA_mem D hu.2⟩

def ratio : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / sgU D

theorem ratio_apply (x : (AE D)ˣ) : ratio D x = x / sgU D x := rfl

abbrev incU : D.host.Eˣ →* (AE D)ˣ := Units.map (inc D).toMonoidHom

def infChar (c : ℤ) : D.host.Eˣ →* ℂˣ :=
  ∏ τ : D.what₂.Tau, (zpowGroupHom (2 * c)).comp (phase.comp (Units.map (embT D τ).toMonoidHom))

theorem infChar_val (c : ℤ) (a : D.host.Eˣ) : ((infChar D c a : ℂˣ) : ℂ) =
    ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) := by
  simp [infChar, phase_val]

theorem norm_infChar (c : ℤ) (a : D.host.Eˣ) : ‖((infChar D c a : ℂˣ) : ℂ)‖ = 1 := by
  rw [infChar_val, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (by simpa using h), one_zpow]

theorem ratio_eq_pm (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) :
    ∃ m : ℕ, 0 < m ∧ ((a : D.host.E) / D.host.conj a) ^ m = 1 := by
  have hc : D.host.conj (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hval : ((ratio D (incU D a) : (AE D)ˣ) : AE D) = inc D ((a : D.host.E) / D.host.conj a) := by
    have h1 : ((sgU D (incU D a) : (AE D)ˣ) : AE D) = inc D (D.host.conj a) :=
      Formalism.UG.P.csDual_sig_incl _ _
    rw [ratio_apply, div_eq_mul_inv, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, h1, ← map_mul,
      div_mul_cancel₀ _ hc]
    rfl
  have hint : IsIntegral ℤ ((a : D.host.E) / D.host.conj a) :=
    Formalism.UG.P.csGlob_int (F := ℚ) _ (by have := h.1; rw [hval] at this; exact this)
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint (fun φ => by
    rw [map_div₀, emb_conj, norm_div, Complex.norm_conj, div_self]
    simpa using a.ne_zero)
  exact ⟨n, hn, hpow⟩

theorem infChar_eq_one (c : ℤ) (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) : infChar D c a = 1 := by
  apply Units.ext
  rw [infChar_val, Units.val_one]
  have key : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) =
      embT D τ ((a : D.host.E) / D.host.conj a) ^ c := by
    intro τ
    have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [zpow_mul, map_div₀, emb_conj, zpow_two, div_mul_div_comm, ← sq (‖_‖ : ℂ), ← Complex.mul_conj',
      mul_div_mul_left _ _ h]
  simp only [key]
  exact UpperTheory.Mu.prod_emb_zpow D.host D.eTau (ratio_eq_pm D a h) c

end GlobalTheory.NormSum.UnramHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeight
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

theorem weight_eq_wtK (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (μ : Ix p q → ℚ) (P : Pol p q n 0) (h1 : IsHW (fockAct1 p q n 0) μ P)
    (h2 : P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am))
    (h3 : KilledByLower (fockAct1 p q n 0) P) : μ = wtK n ap am := by
  have hj : P ∈ jointHW μ (wtH n ap am) := by
    refine ⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩
    have := h3 a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
    exact this
  obtain ⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩ :=
    four_of_joint h1.1 hj
  funext x
  rcases x with i | j
  · have hi := i.2
    have u := e1 i
    have v := e3 ⟨i.1, by omega⟩
    rw [b1 _ (by simp)] at u
    rw [d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))] at v
    simp only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith
  · have hj := j.2
    have hr := j.rev.2
    have u := e2 j
    have v := e3 (Fin.rev ⟨j.rev.1, by omega⟩)
    have hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p := by
      rw [Fin.val_rev]; dsimp only; omega
    rw [c1 _ (by simp)] at u
    rw [a1 _ ((min_le_left _ _).trans (not_lt.1 hp))] at v
    simp only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith

end GlobalTheory.HarmonicShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaMemSum
section
namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
end

