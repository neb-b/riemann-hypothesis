module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LLineiso
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeChartSpan
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_twist_globally_generated : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) :=
  PositivityTheory.HtPt.Ma.serre

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticeQuotientForms
section
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.LineIso

theorem lineIso_of_two_degrees : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (a a' : K → ℤ) (e₀ : E) (ρ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → L.IsDegOn Set.univ y a e₀ → L.IsDegOn Set.univ y a' (ρ • e₀) → ∃ f g : MRing ι, IsLineIso (mCoordIdeal y) a a' f g ∧ aeval y f = ρ * aeval y g :=
  @PositivityTheory.UnitarySelfGeneration.l_lineiso

end GlobalTheory.CompanionTheory.Ar.LineIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open scoped nonZeroDivisors

theorem differentIdeal_principal_in_localSubring :
    ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω)
      [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) →
      ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧
        ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  intro F _ _ Ω _ _ R _ σ hσ
  have hinj : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  set I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  let J : FractionalIdeal (𝓞 F)⁰ F := (I : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := by
    simpa [J] using hI0
  have hJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ0
  let σ' : 𝓞 F →+* R := σ.codRestrict R hσ
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal R).comap σ'
  have hP1 : (1 : 𝓞 F) ∉ P := by
    intro h
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa [P] using h
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

  have hex : ∃ x ∈ I, ∃ y ∈ J⁻¹, ∃ u : 𝓞 F, algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F x * y ∧
      u ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hle : J * J⁻¹ ≤ (P : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      have hab : algebraMap (𝓞 F) F x * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← hJ]
        exact FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 hab
      rw [← hu]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨u, hcon x hx b hb u hu, rfl⟩
    have h1 : (1 : F) ∈ (P : FractionalIdeal (𝓞 F)⁰ F) :=
      hle (by rw [hJ]; exact FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw, hw1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : w = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hw1
    exact hP1 (this ▸ hw)
  obtain ⟨x, hx, y, hy, u, hu, huP⟩ := hex
  have hunit : IsUnit (σ' u) := by
    by_contra hnu
    exact huP ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hσu : σ u ≠ 0 := by
    intro h0
    have : σ' u = 0 := Subtype.ext h0
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : u = 0 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hu
    exact hσu (by simp [this])
  refine ⟨x, hx, fun h => hx0 (hinj (by simpa using h)), fun d hd => ?_⟩
  have hdJ : algebraMap (𝓞 F) F d ∈ J := (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have hdy : algebraMap (𝓞 F) F d * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← hJ]
    exact FractionalIdeal.mul_mem_mul hdJ hy
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).1 hdy
  have hrel : d * u = x * v := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_mul, hu, hv]
    ring
  have hrel' : σ d * σ u = σ x * σ v := by rw [← map_mul, ← map_mul, hrel]
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by simpa using h))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : σ u * (w : Ω) = 1 := congrArg Subtype.val hw
  have key : σ d / σ x = σ v * (w : Ω) := by
    rw [div_eq_iff hσx]
    calc σ d = σ d * (σ u * (w : Ω)) := by rw [hw', _root_.mul_one]
      _ = (σ d * σ u) * (w : Ω) := by ring
      _ = σ v * (w : Ω) * σ x := by rw [hrel']; ring
  rw [key]
  exact R.mul_mem (hσ v) w.2

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem scale_pull_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j W W' O _ σ 𝔡 d₀ D D' hsemi hR hW' hd₀ hσd₀ hdiv hDW hD'
  have hj : ∀ (a : Ω) (v : V), j (a • v) = i a • j v := hsemi.1
  subst hW' hD'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro e ⟨-, he⟩
    have hu : i (σ d₀) ≠ 0 := (map_ne_zero i).mpr hσd₀
    have key : ∀ y ∈ Submodule.span R' (j '' (D : Set V)),
        (i (σ d₀))⁻¹ • y ∈ Submodule.span R'
          (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(σ d₀)⁻¹ • x, Submodule.subset_span ⟨W.smul_mem (σ d₀)⁻¹ (hDW x hx), fun d hd => ?_⟩, ?_⟩
        · rw [smul_smul, ← div_eq_mul_inv]
          exact D.smul_mem ⟨σ d / σ d₀, hdiv d hd⟩ hx
        · rw [hj, map_inv₀]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        have e1 : (i (σ d₀))⁻¹ • (a • y) = a • ((i (σ d₀))⁻¹ • y) :=
          show (i (σ d₀))⁻¹ • ((a : Ω') • y) = (a : Ω') • ((i (σ d₀))⁻¹ • y) by
            rw [smul_smul, smul_smul, mul_comm]
        rw [e1]
        exact Submodule.smul_mem _ a hy
    have h1 := key _ (he d₀ hd₀)
    rwa [RingHom.comp_apply, inv_smul_smul₀ hu] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      refine ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, fun d hd => ?_⟩
      rw [RingHom.comp_apply, ← hj]
      exact Submodule.subset_span ⟨_, hv.2 d hd, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      show j ((a : Ω) • x) ∈ _
      rw [hj]
      exact Submodule.smul_mem _ ⟨i a, hR a a.2⟩ hx

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ScaledCasimir

section General

variable {J A : Type*} [Fintype J] [DecidableEq J] [CommRing A] (a : Module.Basis J ℤ A)

noncomputable def dualScaled (m : J) : A :=
  ∑ n, (Algebra.traceMatrix ℤ a).adjugate m n • a n

theorem trace_dualScaled_mul_basis (m p : J) :
    Algebra.trace ℤ A (dualScaled a m * a p) =
      if m = p then (Algebra.traceMatrix ℤ a).det else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (Algebra.traceMatrix ℤ a)) m) p
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one,
    mul_zero] at h
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dualScaled, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem trace_dualScaled_mul (m : J) (y : A) :
    Algebra.trace ℤ A (dualScaled a m * y) = a.repr y m * (Algebra.traceMatrix ℤ a).det := by
  conv_lhs => rw [← a.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, trace_dualScaled_mul_basis,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem eq_of_trace_mul_basis (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) {x y : A}
    (H : ∀ p, Algebra.trace ℤ A (x * a p) = Algebra.trace ℤ A (y * a p)) : x = y := by
  have hz : (fun q => a.repr (x - y) q) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hd
    funext p
    have h1 : Algebra.trace ℤ A ((x - y) * a p) = 0 := by
      rw [sub_mul, map_sub, H p, sub_self]
    conv at h1 => lhs; rw [← a.sum_repr (x - y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply] using h1
  have : x - y = 0 := by
    apply a.repr.injective
    ext q
    simpa using congrFun hz q
  exact sub_eq_zero.mp this

theorem mul_dualScaled (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) (b : A) (n : J) :
    b * dualScaled a n = ∑ m, a.repr (b * a m) n • dualScaled a m := by
  apply eq_of_trace_mul_basis a hd
  intro p
  have h1 : b * dualScaled a n * a p = dualScaled a n * (b * a p) := by ring
  rw [h1, trace_dualScaled_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, trace_dualScaled_mul,
    Module.Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem sum_dualScaled_mul (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) :
    ∑ m, dualScaled a m * a m = (((Algebra.traceMatrix ℤ a).det : ℤ) : A) := by
  apply eq_of_trace_mul_basis a hd
  intro k
  have h1 : ∀ m, dualScaled a m * a m * a k = dualScaled a m * (a k * a m) := fun m => by ring
  have h2 : (((Algebra.traceMatrix ℤ a).det : ℤ) : A) * a k =
      (Algebra.traceMatrix ℤ a).det • a k := by rw [zsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, h2, map_zsmul, Algebra.trace_eq_matrix_trace a (a k)]
  simp only [h1, trace_dualScaled_mul, Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem equivariant (hd : (Algebra.traceMatrix ℤ a).det ≠ 0)
    {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : A →+* Module.End Ω V) (σ : A →+* Ω) (b : A) (v : V) :
    ρ b (∑ m, σ (dualScaled a m) • ρ (a m) v) =
      σ b • ∑ m, σ (dualScaled a m) • ρ (a m) v := by
  have hmul : ∀ m, ρ b (ρ (a m) v) = ∑ n, ((a.repr (b * a m) n : ℤ) : Ω) • ρ (a n) v := by
    intro m
    have h0 : ρ b (ρ (a m) v) = ρ (b * a m) v := by simp [map_mul]
    rw [h0]
    conv_lhs => rw [← a.sum_repr (b * a m)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have hc : ∀ n, σ b * σ (dualScaled a n) =
      ∑ m, σ (dualScaled a m) * ((a.repr (b * a m) n : ℤ) : Ω) := by
    intro n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, mul_dualScaled a hd, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc n, Finset.sum_smul]

end General

theorem exists_scaledCasimir :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (n : ℕ) (a c : Fin n → 𝓞 F), (∑ m, c m * a m = (((NumberField.discr F : ℤ) : 𝓞 F))) ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 F →+* Module.End Ω V) (σ : 𝓞 F →+* Ω) (b : 𝓞 F) (v : V), ρ b (∑ m, σ (c m) • ρ (a m) v) = σ b • ∑ m, σ (c m) • ρ (a m) v := by
  intro F _ _
  let a := Module.finBasis ℤ (𝓞 F)
  have hdet : (Algebra.traceMatrix ℤ a).det = NumberField.discr F := by
    rw [← Algebra.discr_def, NumberField.discr_eq_discr]
  have hd : (Algebra.traceMatrix ℤ a).det ≠ 0 := by
    rw [hdet]; exact NumberField.discr_ne_zero F
  refine ⟨_, a, dualScaled a, ?_, ?_⟩
  · rw [sum_dualScaled_mul a hd, hdet]
  · intro Ω _ V _ _ ρ σ b v
    exact equivariant a hd ρ σ b v

end GlobalTheory.CompanionTheory.Ar.ScaledCasimir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem dual_pull : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hD : ∀ f : Module.Dual Ω W, f = 0 := by
      intro f
      have hf : f ∈ Submodule.span Ω (Set.range b) := hsp ▸ Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty] at hf
      exact (Submodule.mem_bot Ω).1 hf
    have hW0 : ∀ e ∈ W, e = 0 := by
      intro e he
      have : (⟨e, he⟩ : W) = 0 :=
        (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl
      exact congrArg Subtype.val this
    have hW'0 : W' = ⊥ := by
      rw [hW', Submodule.span_eq_bot]
      rintro _ ⟨e, he, rfl⟩
      rw [hW0 e he, map_zero]
    have hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥ :=
      Submodule.span_eq_bot.2 fun e he => hW0 e he.1
    rw [hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]
    · rintro _ ⟨e, he, rfl⟩
      have : e = 0 := by simpa using he
      rw [this, map_zero]
    · rintro e ⟨he, -⟩
      rw [hW'0] at he
      exact (Submodule.mem_bot Ω').1 he
  have hω'' := hω' hr
  let hb : Module.Basis (Fin r) Ω (Module.Dual Ω W) := Module.Basis.mk hli hsp.ge
  have hbb : ∀ k, hb k = b k := fun k => Module.Basis.mk_apply hli hsp.ge k
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb
  haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance
  let c : Module.Basis (Fin r) Ω W := hb.dualBasis.map (Module.evalEquiv Ω W).symm
  have hbc : ∀ l k, b l (c k) = if l = k then 1 else 0 := by
    intro l k
    have h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k) := by
      simp [c]
    rw [h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]

  have hexp : ∀ e : W, e = ∑ k, b k e • c k := by
    intro e
    conv_lhs => rw [← c.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : b k e = ∑ m, c.repr e m * b k (c m) := by
      calc b k e = b k (∑ m, c.repr e m • c m) := by rw [c.sum_repr]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp [hbc]

  have hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := by
    intro k
    refine ⟨(c k).2, fun w hw => ?_⟩
    have hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b) := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        rw [hbc]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      | zero => simpa using R.zero_mem
      | add x y _ _ hx hy => simpa using R.add_mem hx hy
      | smul a x _ hx =>
        have : (a • x) (c k) = (a : Ω) * x (c k) := rfl
        rw [this]
        exact R.mul_mem a.2 hx
    exact key _ hwr

  have hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l := by
    intro l
    have : b l ∈ ω.map (W.dualRestrict.restrictScalars R) := by
      rw [hmap]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  choose wl hwl hwb using hpick
  have hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V) := by
    intro e' he'
    have hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V)) := by
      rw [hW', Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V) := by
        have := congrArg (Subtype.val) (hexp ⟨e, he⟩)
        simpa using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [SetLike.mem_coe, h1, map_sum]
      refine sum_mem fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')
    exact ⟨a, ha.symm⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨he', hint⟩
    obtain ⟨a, rfl⟩ := hspan e' he'
    have hal : ∀ l, a l ∈ R' := by
      intro l
      have h1 := hint (jd (wl l)) (by
        rw [hω'']
        exact Submodule.subset_span ⟨wl l, hwl l, rfl⟩)
      have h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        have : ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0) := by
          intro k
          have h3 : wl l (c k : V) = if l = k then 1 else 0 := by
            rw [← hbc, ← hwb]
            simp [Submodule.dualRestrict_apply]
          rw [map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]
        simp [this]
      rwa [h2] at h1
    rw [SetLike.mem_coe]
    refine sum_mem fun k _ => ?_
    have : a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
      · rw [hW']
        exact Submodule.subset_span ⟨x, hx.1, rfl⟩
      · rw [hω''] at hw
        induction hw using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨u, hu, rfl⟩ := hf
          rw [hjd]
          exact hR _ (hx.2 u hu)
        | zero => simpa using R'.zero_mem
        | add f g _ _ hf hg => simpa using R'.add_mem hf hg
        | smul a f _ hf =>
          have : (a • f) (j x) = (a : Ω') * f (j x) := rfl
          rw [this]
          exact R'.mul_mem a.2 hf
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.Ar.HcptPull
end

