module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSum
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.KForm

section Embeddings

variable {E : Type} [Field E] [NumberField E]


open Classical in
theorem sum_dual_mul (σ τ : E →+* ℂ) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End ℂ ℂ :=
    (Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : ℂ) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

theorem trace_cast (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ z := by
  have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  simpa using this

end Embeddings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem kappa_form {ε : ℤˣ} {h : D.La → D.La → OK H} {σ : E →+* ℂ} {κ : OK H →+* ℂ}
    (hh : IsKForm D ε h) (hκ : κ (wK H) = σ (H.w0 : E)) (X Y : D.La) :
    κ (h X Y) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) := by
  obtain ⟨hT, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum E H D
  have e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) +
      (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H := by
    apply Subtype.ext
    simpa [wK] using hh X Y
  have t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)
    simp only [trace_cast, map_mul] at this
    rw [this]
    simp
  have t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) := by
    have h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ) := by simpa using hT 1 X Y
    rw [← trace_cast, h1]
    simp
  have hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) +
        (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_add κ, map_mul, map_intCast, map_intCast, hκ, hs]
  push_cast
  rw [t1, t0]
  ring

theorem sigma_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  classical
  intro E _ _ _ H D ε h σ κ n e x y hh hκ
  obtain ⟨-, -, -, hL, hR, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum E H D

  have hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) *
        (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E))) := by
    intro a c
    rw [kappa_form hh hκ]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E)) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)
    rw [hL, hR, map_mul, map_mul, hc]
    ring

  set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef
  have hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0 := by
    intro τ
    have := sum_dual_mul σ (τ : E →+* ℂ)
    rw [← Equiv.sum_comp e] at this
    exact this
  set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef
  have hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) *
        κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) *
        starRingEnd ℂ (σ (HT.dualInt E (e k'))) =
      ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, Finset.sum_eq_single σ.toRatAlgHom]
  · have h1 : S σ.toRatAlgHom = 1 := by
      rw [hS]
      exact if_pos (RingHom.ext fun _ => rfl)
    have h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1 := by
      have h3 := congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at h3
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
      linear_combination -h3
    rw [h1, map_one, map_mul, h2]
    simp only [hcdef]
    change _ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _
    ring
  · intro τ _ hτ
    have h0 : S τ = 0 := by
      rw [hS]
      refine if_neg fun hc => hτ (AlgHom.ext fun z => ?_)
      exact congrArg (fun f : E →+* ℂ => f z) hc
    rw [h0]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end GlobalTheory.CompanionTheory.Ar.Fl.KForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResidueEval
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClosedPt

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts TopologicalSpace

theorem exists_residue_eval : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ),
    LocallyOfFiniteType p → ∀ (B : LB Y), B.IsLB → ∀ z : Y, IsClosed ({z} : Set Y) →
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (e : B.Sec →+ K),
      (∀ (a : F) (s : B.Sec), e (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a • s) = algebraMap F K a * e s) ∧
      (∀ s : B.Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → e s ≠ 0) ∧
      ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∃ (y : GlobalTheory.CxPts p σ) (i : B.ι),
        y.1 (IsLocalRing.closedPoint ℂ) = z ∧ ∀ s : B.Sec, GlobalTheory.CxPts.secVal p σ s i y = τ (e s) := by
  intro F _ Y p σ hp B hB z hz
  obtain ⟨i, hzi⟩ : ∃ i, z ∈ B.U i := Opens.mem_iSup.1 (by rw [hB.cover]; trivial)
  obtain ⟨U, hU, hzU, hUi⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hzi
  replace hU : IsAffineOpen U := hU
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hftA : Algebra.FiniteType F Γ(Y, U) := hft
  set x0 := hU.primeIdealOf ⟨z, hzU⟩ with hx0
  have hfx : hU.fromSpec x0 = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hcl : IsClosed ({x0} : Set (PrimeSpectrum Γ(Y, U))) := by
    have h1 : IsClosed (hU.fromSpec.base ⁻¹' {z}) := hz.preimage hU.fromSpec.base.hom.continuous
    have h2 : hU.fromSpec.base ⁻¹' {z} = {x0} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hq
        exact hU.fromSpec.isOpenEmbedding.injective (hq.trans hfx.symm)
      · rintro rfl; exact hfx
    rw [h2] at h1
    exact h1
  have hmax : x0.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hcl
  let P := x0.asIdeal
  letI : Field (Γ(Y, U) ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType F (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  have hfin : Module.Finite F (Γ(Y, U) ⧸ P) := finite_of_finite_type_of_isJacobsonRing F _
  have hmem : ∀ f : Γ(Y, U), z ∈ Y.basicOpen f ↔ f ∉ P := by
    intro f
    have h1 : x0 ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen f ↔ hU.fromSpec x0 ∈ Y.basicOpen f := Iff.rfl
    rw [hfx, hU.fromSpec_preimage_basicOpen] at h1
    exact h1.symm.trans (PrimeSpectrum.mem_basicOpen _ _)
  let e : B.Sec →+ Γ(Y, U) ⧸ P :=
    { toFun := fun s => Ideal.Quotient.mk P (resG Y hUi (s.f i))
      map_zero' := by simp
      map_add' := fun s t => by simp only [GlobalTheory.LB.add_f, map_add (f := _)] }
  refine ⟨Γ(Y, U) ⧸ P, inferInstance, inferInstance, hfin, e, ?_, ?_, ?_⟩
  · intro a s
    change Ideal.Quotient.mk P (resG Y hUi ((algX p ⊤ a • s).f i)) = _ * Ideal.Quotient.mk P _
    have hres : resG Y (hUi.trans le_top) (algX p ⊤ a) = algX p U a :=
      RingHom.congr_fun (GlobalTheory.TopForm.resG_comp_algX p (hUi.trans le_top)) a
    rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LB.resG_resG, hres]
    rfl
  · intro s hs
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hs
    have hki : z ∈ B.U i ⊓ B.U k := ⟨hzi, Y.basicOpen_le _ hk⟩
    have hrel := GlobalTheory.LB.sec_rel s i k (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) inf_le_right le_rfl
    have h1 : z ∈ Y.basicOpen (resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i)) := by
      rw [hrel, Scheme.basicOpen_mul, Y.basicOpen_of_isUnit
        ((B.g i k).isUnit.map (resG Y le_rfl))]
      refine ⟨hki, ?_⟩
      have : resG Y (inf_le_right : B.U i ⊓ B.U k ≤ B.U k) (s.f k) =
          Y.presheaf.map (homOfLE (inf_le_right : B.U i ⊓ B.U k ≤ B.U k)).op (s.f k) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hki, hk⟩
    have h2 : z ∈ Y.basicOpen (s.f i) := by
      have : resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i) =
          Y.presheaf.map (homOfLE (inf_le_left : B.U i ⊓ B.U k ≤ B.U i)).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res] at h1
      exact h1.2
    have h3 : z ∈ Y.basicOpen (resG Y hUi (s.f i)) := by
      have : resG Y hUi (s.f i) = Y.presheaf.map (homOfLE hUi).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hzU, h2⟩
    change Ideal.Quotient.mk P _ ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact (hmem _).1 h3
  · intro τ hτ
    let φ : Γ(Y, U) →+* ℂ := τ.comp (Ideal.Quotient.mk P)
    have hφ : ∀ a, φ (algX p U a) = σ a := fun a => by
      rw [← hτ]; rfl
    refine ⟨ofHom hU φ hφ, i, ?_, fun s => ?_⟩
    · have hker : RingHom.ker φ = P := by
        rw [RingHom.ker_comp_of_injective _ τ.injective]
        exact Ideal.mk_ker
      have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = x0 := by
        apply PrimeSpectrum.ext
        change Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = P
        rw [IsLocalRing.maximalIdeal_eq_bot]
        exact hker
      change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ)) = z
      rw [hpt, hfx]
    · rw [secVal_apply, ← ev_res hUi (ofHom_mem hU φ hφ), ev_ofHom]
      rfl

end GlobalTheory.CompanionTheory.Ar.ClosedPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br.FinPlace

section Valued

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {N : Type*} [NormedField N]

theorem val_lt_one_iff (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) (a : F) :
    v a < 1 ↔ ‖κ a‖ < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hv : 0 < v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha)
  have hn : 0 < ‖κ a‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr ha)
  have e := h a⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv, inv_le_one₀ hn] at e
  rw [← not_le, ← not_le, e]

theorem norm_le_of_val_le (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a ≤ v b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have hv : 0 < v b := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hb)
  have hn : 0 < ‖κ b‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr hb)
  have e := (h (a / b)).mp (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le)
  rw [map_div₀, norm_div] at e
  exact (div_le_one hn).mp e

theorem norm_eq_of_val_eq (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a = v b) : ‖κ a‖ = ‖κ b‖ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact (Valuation.ne_zero_iff v).mpr hb hab.symm
  exact le_antisymm (norm_le_of_val_le v κ h hb hab.le) (norm_le_of_val_le v κ h ha hab.ge)

end Valued

theorem norm_natCast_lt_one_iff (q : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[q])‖ < 1 ↔ (q : ℕ) ∣ n := by
  have e : ‖(n : ℂ_[q])‖ = ‖(n : ℚ_[q])‖ := by
    have h1 := PadicComplex.norm_extends (q : ℕ) ((n : ℚ_[q]) : PadicAlgCl q)
    have h2 := PadicAlgCl.norm_extends (q : ℕ) (n : ℚ_[q])
    simpa using h1.trans h2
  rw [e]
  exact Padic.norm_natCast_lt_one_iff

theorem prime_eq {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {p q : Nat.Primes} (κ : F →+* ℂ_[p]) (κ₀ : F →+* ℂ_[q]) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h₀ : ∀ a, v a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) : p = q := by
  have h1 : ‖κ ((p : ℕ) : F)‖ < 1 := by
    rw [map_natCast, norm_natCast_lt_one_iff]
  have h2 : ‖κ₀ ((p : ℕ) : F)‖ < 1 := (val_lt_one_iff v κ₀ h₀ _).mp ((val_lt_one_iff v κ h _).mpr h1)
  rw [map_natCast, norm_natCast_lt_one_iff] at h2
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h2).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem hasFinNorm_of_isometry {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {p : Nat.Primes}
    {κ κ' : c.F →+* ℂ_[p]} {t : ℝ} (g : ℂ_[p] ≃+* ℂ_[p]) (hg : ∀ z, ‖g z‖ = ‖z‖) (hκ : ∀ a, g (κ a) = κ' a)
    (h : HasFinNorm U τ φ p κ t) : HasFinNorm U τ φ p κ' t := by
  have hs : ∀ z, ‖g.symm z‖ = ‖z‖ := fun z => by
    rw [← hg (g.symm z), RingEquiv.apply_symm_apply]
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hF hv hw
  have e := h V K ((g.symm : ℂ_[p] →+* ℂ_[p]).comp j) β y v w T tK m m'
    (fun a => by
      rw [← hj a]
      simp only [RingHom.comp_apply, RingHom.coe_coe, hs])
    (by
      ext a
      have h1 : j (β a) = κ' a := by rw [← hjβ]; rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ← hκ, RingEquiv.symm_apply_apply]) hF hv hw
  simpa only [RingHom.comp_apply, RingHom.coe_coe, hs] using e

theorem exists_rho_at (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F]
    (hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t)
    (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ r : ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (π : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) →
      HasFinNorm U τ φ p κ (r * Real.log ‖κ π‖) := by
  by_cases hex : ∃ (p₀ : Nat.Primes) (κ₀ : c.F →+* ℂ_[p₀]) (π₀ : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) ∧ la.valuation c.F π₀ = WithZero.exp (-1 : ℤ)
  · obtain ⟨p₀, κ₀, π₀, hκ₀, hπ₀⟩ := hex
    obtain ⟨t₀, ht₀⟩ := hfin p₀ κ₀
    have hne : π₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ₀
      exact WithZero.exp_ne_zero hπ₀.symm
    have hlt : ‖κ₀ π₀‖ < 1 := (val_lt_one_iff _ κ₀ hκ₀ π₀).mp (by
      rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have hpos : 0 < ‖κ₀ π₀‖ := norm_pos_iff.mpr ((map_ne_zero κ₀).mpr hne)
    have hlog : Real.log ‖κ₀ π₀‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
    refine ⟨t₀ / Real.log ‖κ₀ π₀‖, fun p κ π hκ hπ => ?_⟩
    have hp : p = p₀ := prime_eq (la.valuation c.F) κ κ₀ hκ hκ₀
    subst hp
    obtain ⟨g, hg, hgκ⟩ := GlobalTheory.T.padic_embeddings_conjugate_of_units c.F p κ₀ κ (fun a => (hκ₀ a).symm.trans (hκ a))
    have e : ‖κ π‖ = ‖κ₀ π₀‖ := by
      rw [norm_eq_of_val_eq _ κ hκ hne (hπ.trans hπ₀.symm), ← hgκ, hg]
    rw [e, div_mul_cancel₀ _ hlog]
    exact hasFinNorm_of_isometry g hg hgκ ht₀
  · exact ⟨0, fun p κ π h1 h2 => (hex ⟨p, κ, π, h1, h2⟩).elim⟩

theorem exists_rho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  intro E _ _ _ H D l Xo c _ U τ φ hfin
  choose ρ hρ using exists_rho_at U τ φ hfin
  exact ⟨ρ, fun p κ la π h1 h2 => hρ la p κ π h1 h2⟩

end GlobalTheory.CompanionTheory.Ar.Br.FinPlace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_fieldMap_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) (z : X) (hz : ξ (IsLocalRing.closedPoint Ω) = z) :
    ∃ i : Ω →+* X.residueField z, spMap i ≫ ξ = X.fromSpecResidueField z := by
  subst hz
  let g := X.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ)
  have hsurj : Function.Surjective g.hom := by
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨(X.residue _).hom b, ?_⟩
    have e := congrArg CommRingCat.Hom.hom
      (X.residue_descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ))
    exact (congrArg (fun φ => φ b) e).trans hb
  let e : X.residueField (ξ (IsLocalRing.closedPoint Ω)) ≃+* Ω :=
    RingEquiv.ofBijective g.hom ⟨g.hom.injective, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  have h1 : Spec.map g ≫ X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω)) = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  have h2 : spMap e.symm.toRingHom ≫ Spec.map g = 𝟙 _ := by
    have h3 : g ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h3).trans (Spec.map_id _))
  refine (congrArg (spMap e.symm.toRingHom ≫ ·) h1).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.fromSpecResidueField _) h2).trans (Category.id_comp _))

theorem isGeom_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' _ hc x ⟨f, hf0, hf⟩
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z'.ξ₀).hom := by
    have h := Z'.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgp : genPt Z'.ξ₀ = Formalism.L2.Pj.genPt Z := by
    have hg := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    have h2 : Formalism.L2.Pj.genPt Z ⤳ genPt Z'.ξ₀ := hg.specializes Z'.genPt_mem
    have h3 : genPt Z'.ξ₀ ⤳ Formalism.L2.Pj.genPt Z := (Z'.closure _).1 hg.mem
    exact (h3.antisymm h2).eq
  obtain ⟨i, hi⟩ := exists_fieldMap_of_surjective Z'.ξ₀ hsurj _ hgp
  have hcomp : i.comp Z'.inc = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (i.comp Z'.inc) = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) := by
      rw [← h1]
      have e : spMap (i.comp Z'.inc) = spMap i ≫ spMap Z'.inc := by
        rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
      rw [e, ← Z'.over_inc, ← Category.assoc, hi]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i x)) := by
    refine ⟨f, hf0, ?_⟩
    have h3 := Polynomial.hom_eval₂ f Z'.inc ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) x
    rw [hf, map_zero] at h3
    rw [Polynomial.aeval_def]
    refine Eq.trans ?_ h3.symm
    have e : algebraMap c.F (Formalism.L2.Pj.Om Z) =
        ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i).comp Z'.inc := by
      rw [RingHom.comp_assoc, hcomp]
      exact IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    rfl
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i x := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictInt
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem isProjOver_comp_spMap_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o),
    IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  intro o _ _ X s hs
  have hfin : IsFinite (spMap (Int.castRingHom o)) := by
    have he : Int.castRingHom o = algebraMap ℤ o := RingHom.ext_int _ _
    rw [he]
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ o)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact GlobalTheory.QuotModel.isProjOver_comp_spMap _ s hfin hs

end GlobalTheory.CompanionTheory.Ar.XR
end

