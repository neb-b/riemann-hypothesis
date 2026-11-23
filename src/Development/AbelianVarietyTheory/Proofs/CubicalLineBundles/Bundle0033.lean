module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.SelfDualDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_enum (H : Host E) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H 1 0 ty ∧
    ∀ i, ty i (H.rt : E) = H.rt0 := by
  classical
  let e := (Fintype.equivFin {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}).symm
  refine ⟨_, fun i => (e i).1, fun τ => ⟨fun h => ?_, fun h => ?_⟩, fun i => (e i).2⟩
  · rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (e.injective (Subtype.ext (a.2.trans b.2.symm)))⟩,
      ⟨⟨e.symm ⟨τ, h⟩, by simp⟩⟩⟩
  · haveI : IsEmpty {i // (e i).1 = τ} := ⟨fun a => h (a.2 ▸ (e a.1).2)⟩
    simp

theorem trace_eq (H : Host E) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H 1 0 ty) (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = 2 * (∑ i, ty i a).re := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty a
  have h2 := PeriodNonempty.sum_type H he a
  have h3 : ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ i, e i a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ), Equiv.sum_comp e (fun τ => τ a)]
    exact (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ a)).symm
  simp only [Nat.cast_one, _root_.one_mul, Nat.cast_zero, zero_mul, add_zero] at h1 h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, Finset.sum_add_distrib, ← map_sum, ← h1] at h3
  have := congrArg Complex.re h3
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at this
  linarith

theorem exists_form (𝔄 : Submodule (𝓞 E) E) (ξ : E) (hξ0 : ξ ≠ 0)
    (hdual : ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ 𝔄) :
    ∃ EF : LinearMap.BilinForm ℤ 𝔄, Function.Bijective EF ∧
      ∀ x y : 𝔄, (EF x y : ℚ) = Algebra.trace ℚ E (ξ * (x : E) * IsCMField.complexConj E (y : E)) := by
  choose f hf using fun x y : 𝔄 => (hdual x).2 x.2 y y.2
  let EF : LinearMap.BilinForm ℤ 𝔄 := LinearMap.mk₂ ℤ f
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, Submodule.coe_add, mul_add, add_mul, map_add (f := _)])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, ← hf, ← hf, ← zsmul_eq_mul _ c, ← map_zsmul]
      congr 1
      simp
      ring)
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, Submodule.coe_add, map_add (f := _), mul_add, map_add (f := _)])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, ← hf, ← hf, ← zsmul_eq_mul _ c, ← map_zsmul]
      congr 1
      simp
      ring)
  have hEF : ∀ x y : 𝔄, (EF x y : ℚ) = Algebra.trace ℚ E (ξ * (x : E) * IsCMField.complexConj E (y : E)) :=
    fun x y => (hf x y).symm
  refine ⟨EF, ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun φ => ?_⟩, hEF⟩
  · by_contra h0
    have hx0 : (x : E) ≠ 0 := fun h => h0 (Subtype.ext h)
    have hz : ∀ a : 𝓞 E, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E x * IsCMField.complexConj E a) = 0 :=
      fun a => by
        have := hEF x (a • x)
        rw [hx, Submodule.coe_smul, Algebra.smul_def, map_mul (IsCMField.complexConj E)] at this
        simp only [LinearMap.zero_apply, Int.cast_zero] at this
        rw [this]
        congr 1
        simp only [RingOfIntegers.coe_eq_algebraMap]
        ring
    have hall : ∀ z : E, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E x * IsCMField.complexConj E z) = 0 :=
      fun z => by
        obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ {z}
        have := hz ⟨n • z, hi z (by simp)⟩
        change Algebra.trace ℚ E (_ * IsCMField.complexConj E (n • z)) = 0 at this
        rw [map_zsmul, mul_smul_comm, map_zsmul] at this
        exact (smul_eq_zero.1 this).resolve_left hn
    have := (traceForm_nondegenerate ℚ E).1 (ξ * x * IsCMField.complexConj E x) fun z => by
      simpa [Algebra.traceForm_apply] using hall (IsCMField.complexConj E z)
    simp [hξ0, hx0] at this
  · obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
      𝔄.subtype.toAddMonoidHom 𝔄.subtype_injective ((Int.castAddHom ℚ).comp φ.toAddMonoidHom)
    have hg' : ∀ x : 𝔄, g x = φ x := fun x => DFunLike.congr_fun hg x
    obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
      (g.comp (IsCMField.complexConj E : E →+* E).toAddMonoidHom).toRatLinearMap
    have hz' : ∀ y : E, Algebra.trace ℚ E (ξ * (z / ξ) * IsCMField.complexConj E y) = g y := fun y => by
      have := LinearMap.congr_fun hz (IsCMField.complexConj E y)
      rw [mul_div_cancel₀ _ hξ0]
      exact this.trans (by simp)
    refine ⟨⟨_, (hdual _).1 fun y hy => ⟨φ ⟨y, hy⟩, (hz' y).trans (hg' ⟨y, hy⟩)⟩⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℚ)
    rw [hEF, hz', hg']


omit [IsCMField E] in
theorem finrank_int (𝔄 : Submodule (𝓞 E) E) (hfg : 𝔄.FG) (hne : 𝔄 ≠ ⊥) :
    Module.finrank ℤ 𝔄 = Module.finrank ℚ E := by
  obtain ⟨N, hN, ψ, hψ⟩ := PrincipalDatum.exists_clear 𝔄 hfg
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective ψ := fun x y h => by
    apply Subtype.ext
    apply mul_left_cancel₀ hNE
    rw [← hψ, ← hψ, h]
  haveI : Module.Finite ℤ 𝔄 := Module.Finite.of_injective (ψ.restrictScalars ℤ) hinj
  rw [← RingOfIntegers.rank]
  obtain ⟨x₀, hx₀, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  refine le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := ψ.restrictScalars ℤ) hinj)
    (LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.toSpanSingleton (𝓞 E) 𝔄 ⟨x₀, hx₀⟩).restrictScalars ℤ) ?_)
  exact smul_left_injective (𝓞 E) (m := (⟨x₀, hx₀⟩ : 𝔄)) (by simpa using h0)

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔄 : Submodule (𝓞 E) E) (ξ : E), 𝔄.FG → 𝔄 ≠ ⊥ → IsCMField.complexConj E ξ = -ξ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0) → (∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ 𝔄) → ∃ (D : Datum H) (e : D.La ≃ₗ[𝓞 E] 𝔄), D.p = 1 ∧ D.q = 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * (e x : E) * IsCMField.complexConj E (e y : E)) := by
  intro E _ _ _ H 𝔄 ξ hfg hne hξ hneg hdual
  classical
  obtain ⟨g, ty, hty, hrt⟩ := exists_enum H
  have hg := PeriodDatum.two_mul_eq_of_isTypeFn H hty
  have hg0 : 0 < g := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hξ0 : ξ ≠ 0 := fun h => by simpa [h] using hneg _ (hrt ⟨0, hg0⟩)
  obtain ⟨EF, hbij, hEF⟩ := exists_form 𝔄 ξ hξ0 hdual
  have hre : ∀ i, (ty i ξ).re = 0 := fun i => by
    have h := IsCMField.complexEmbedding_complexConj E (ty i) ξ
    rw [hξ, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  let P : 𝔄 →+ (Fin g → ℂ) :=
    { toFun := fun x i => ty i (x : E)
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hP : ∀ x i, P x i = ty i (x : E) := fun _ _ => rfl
  let Hm : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal fun i => ((-2 * (ty i ξ).im : ℝ) : ℂ)
  have hHm : ∀ z w, hermForm Hm z w = ∑ i, ((-2 * (ty i ξ).im : ℝ) : ℂ) * (z i * starRingEnd ℂ (w i)) :=
    fun z w => by
      simp only [hermForm, Hm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]; rfl
  have hH : Hm.IsHermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    funext i
    exact Complex.conj_ofReal _)
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re := fun z hz => by
    rw [hHm, Complex.re_sum]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
    have hc : ∀ i, 0 < -2 * (ty i ξ).im := fun i => by linarith [hneg _ (hrt i)]
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (hc i).le (Complex.normSq_nonneg _)
    · rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_pos (hc j) (Complex.normSq_pos.2 hj)
  have him : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y := fun x y => by
    have h := trace_eq H hty (ξ * (x : E) * IsCMField.complexConj E (y : E))
    rw [← hEF, Rat.cast_intCast] at h
    rw [h, hHm, Complex.im_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj, hP, hP, _root_.mul_assoc (ty i ξ)]
    generalize ty i (x : E) * starRingEnd ℂ (ty i (y : E)) = u
    simp [hre]
    ring
  have hlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i => by
    rw [hP, hP, ← map_mul]
    rfl
  have hinj : Function.Injective P := fun x y h =>
    Subtype.ext ((ty ⟨0, hg0⟩).injective (congrFun h ⟨0, hg0⟩))
  have hdisc : DiscreteTopology P.range := by
    obtain ⟨hr0, hs⟩ := PrincipalDatum.principal_root_re_zero_im_sq H
    have hs0 : H.rt0.im ≠ 0 := fun h => by
      rw [h] at hs
      have := H.d_prime.pos
      have : (0 : ℝ) < H.d := by exact_mod_cast this
      linarith
    rw [discreteTopology_iff_isOpen_singleton_zero]
    refine ⟨{z | |H.rt0.im * (hermForm Hm z z).re| < 1}, ?_, ?_⟩
    · refine isOpen_lt ?_ continuous_const
      simp only [hHm]
      fun_prop
    · ext ⟨_, x, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        by_contra h0
        have h1 := hpos (P x) fun e => h0 (Subtype.ext e)
        have h2 := him (H.rt • x) x
        have h3 : P (H.rt • x) = H.rt0 • P x := funext fun i => by rw [hlin, hrt]; rfl
        rw [h3, PeriodDatum.hermForm_smul_left, Complex.mul_im, hr0, zero_mul, zero_add] at h2
        rw [h2] at h
        have h4 : EF (H.rt • x) x = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h)
        rw [h4, Int.cast_zero] at h2
        exact (mul_ne_zero hs0 h1.ne') h2
      · intro h
        rw [show P x = 0 from congrArg Subtype.val h]
        simp [hermForm]
  have hspan : Submodule.span ℝ (Set.range P) = ⊤ := by
    have hz : Submodule.span ℤ (Set.range P) = LinearMap.range P.toIntLinearMap :=
      Submodule.span_eq (LinearMap.range P.toIntLinearMap)
    have h := Real.finrank_eq_int_finrank_of_discrete (s := Set.range P) (by rw [hz]; exact hdisc)
    apply Submodule.eq_top_of_finrank_eq
    rw [Set.finrank, Set.finrank, hz, LinearMap.finrank_range_of_inj (f := P.toIntLinearMap) hinj,
      finrank_int 𝔄 hfg hne] at h
    rw [h, ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
    omega
  have hadj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y) := fun a x y => by
    apply Int.cast_injective (α := ℚ)
    rw [hEF, hEF, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def,
      map_mul (IsCMField.complexConj E),
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      IsCMField.complexConj_apply_apply]
    congr 1
    ring
  obtain ⟨D, e, hp, hq, he⟩ := PeriodDatum.exists_datum E H 𝔄 EF 1 0 g ty P Hm hty hbij hadj hlin hinj hdisc
    hspan hH hpos him
  exact ⟨D, e, hp, hq, fun x y => by rw [he, hEF]⟩

end GlobalTheory.CM.SelfDualDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM

theorem hasType_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G') (e : G ≅ G') (ρ : R) (p q : ℕ), Serre.IsLinearHom a a' e.hom → HasType H a' ρ p q → HasType H a ρ p q := by
  intro E _ _ _ H R _ G G' _ _ a a' e ρ p q he h k _ _ β hβ τ
  have := he.isMonHom
  have key : ∀ n, LieMult a (spMap β) τ n ↔ LieMult a' (spMap β) τ n := fun n => by
    have := LiePull.lieMult_pull _ _ _ G' G (𝟙 _) e.hom.left a' a (isGrpPullback_of_iso e)
      (fun c => congrArg (fun z => z.left) (he.comm c)) k (spMap β) τ n
    rwa [Category.comp_id] at this
  rw [key, key]
  exact h k β hβ τ

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFamIsometryInjective
section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.LamF

theorem hermFam_isometry_injective {K : Type*} [Field K] [NumberField K] {V V' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s a b, h'.form s (M a) (M b) = h.form s a b) : Function.Injective M := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent K ![x] := by
    rw [linearIndependent_unique_iff]; simpa using h0
  have h1 := (h.posDef s 1 ![x] hli).diag_pos (i := 0)
  have h2 : h'.form s (M x) (M x) = 0 := by
    have := h'.smul_right s 0 (M x) (M x)
    rw [zero_smul, map_zero, zero_mul] at this
    rw [← this, hx]
  rw [hM] at h2
  simp [h2] at h1

theorem deg_map_isometry : ∀ (K : Type) [Field K] [NumberField K] (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V') (Λ : Submodule (𝓞 K) V), Λ.FG → (∀ s a b, h'.form s (M a) (M b) = h.form s a b) → ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Λ.map (M.restrictScalars (𝓞 K))) = ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K _ _ V V' _ _ _ _ _ _ _ _ h h' M E hE hM
  have hinj := hermFam_isometry_injective h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, Submodule.span_image]
    exact ⟨x, hv.2.2 hx, rfl⟩
  rw [arakelovDegree_eq_degreeOfFamily h hE hv, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  unfold degreeOfFamily
  have e1 : ∀ s, h'.gram s (M ∘ v) = h.gram s v := fun s => by
    ext i j; simp [HermFam.gram, hM]
  have e2 : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]; rfl
  simp only [e1, e2, Submodule.map_toAddSubgroup]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ (by exact hinj)]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.IntCoord

section General

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR c)) (LieCombBaseChange.epsScale_over c)

theorem sc_comm (a b : R) : sc a ≫ sc b = sc b ≫ sc a := by
  refine Over.OverMorphism.ext ?_
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, mul_left_comm]

theorem sc_one : sc (1 : R) = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber R)))
  show spMap _ = spMap (RingHom.id _)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => sc (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    congr 2
    exact funext fun i => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨_, fun _ => rfl, rfl⟩

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) : IsLieComb ![c] ![v] w ↔ w = sc c ≫ v := by
  rw [isLieComb_iff]
  simp

theorem isLieComb_mul (v w : epsR R ⟶ G) : IsLieComb ![1, 1] ![v, w] (v * w) := by
  rw [isLieComb_iff]
  simp [sc_one]

theorem isLieComb_nil : IsLieComb (![] : Fin 0 → R) (![] : Fin 0 → (epsR R ⟶ G)) 1 := by
  rw [isLieComb_iff]
  simp

theorem eq_of_isVecOver {R' : Type} [CommRing R'] {f : R →+* R'} (hf : Function.Injective f) {A : Over (Sp R)}
    [IsSeparated A.hom] {A' : Over (Sp R')} {φ : A'.left ⟶ A.left} {u u' : epsR R ⟶ A} {w : epsR R' ⟶ A'}
    (h : IsVecOver f φ u w) (h' : IsVecOver f φ u' w) : u = u' := by
  have : IsSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) := by
    refine (schemeDominant_specMap_iff _).2 fun x y e => ?_
    have e1 := congrArg TrivSqZeroExt.fst e
    have e2 := congrArg TrivSqZeroExt.snd e
    simp [Chart.dualMapR] at e1 e2
    exact TrivSqZeroExt.ext (hf e1) (hf e2)
  refine Over.OverMorphism.ext ?_
  exact hom_ext_of_isSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) A.hom (h.symm.trans h')
    ((Over.w u).trans (Over.w u').symm)

end General

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)

theorem isCoord_comb {n : ℕ} {u : Fin n → (epsR (𝓞 K) ⟶ P.A)} {c : Fin n → Fin F.P₀.g → K}
    (h : ∀ i, F.IsCoord (u i) (c i)) {a : Fin n → 𝓞 K} {u' : epsR (𝓞 K) ⟶ P.A} (ha : IsLieComb a u u') :
    F.IsCoord u' (∑ i, a i • c i) := by
  have := P.isAb.comm
  have := F.P₀.isAb.comm
  choose ht w hw hc using h
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver F.fib.2.1.1 u'
  refine ⟨(LieComb.lieComb_algebra _ _ _ u ht).2.1 a u' ha, w', hw', ?_⟩
  exact (LieComb.lieComb_algebra _ _ _ F.v F.basis.1).2.2.1 n c w _ w' hc
    ((lieComb_baseChange _ _ _ _ _ _ F.fib.2.1 n u u' a w w' hw ha).1 hw')

theorem isCoord_one : F.IsCoord 1 0 := by
  simpa using isCoord_comb F (c := ![]) (fun i => i.elim0) isLieComb_nil

theorem isCoord_mul {u u' : epsR (𝓞 K) ⟶ P.A} {c c' : Fin F.P₀.g → K} (h : F.IsCoord u c) (h' : F.IsCoord u' c') :
    F.IsCoord (u * u') (c + c') := by
  simpa using isCoord_comb F (c := ![c, c']) (fun i => by fin_cases i; exacts [h, h']) (isLieComb_mul u u')

theorem isCoord_smul {u u' : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} {r : 𝓞 K} (h : F.IsCoord u c)
    (h' : IsLieComb ![r] ![u] u') : F.IsCoord u' (r • c) := by
  simpa using isCoord_comb F (c := ![c]) (fun i => by fin_cases i; exact h) h'

theorem mem_span_iff (p : (epsR (𝓞 K) ⟶ P.A) → Prop) (h1 : p 1) (hm : ∀ u u', p u → p u' → p (u * u'))
    (hs : ∀ r u, p u → p (sc r ≫ u)) (c : Fin F.P₀.g → K) :
    c ∈ Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u} ↔ ∃ u, F.IsCoord u c ∧ p u := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, isCoord_one F, h1⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, pu⟩ := hx
    obtain ⟨u', hu', pu'⟩ := hy
    exact ⟨_, isCoord_mul F hu hu', hm _ _ pu pu'⟩
  | smul r x _ hx =>
    obtain ⟨u, hu, pu⟩ := hx
    exact ⟨_, isCoord_smul F hu ((isLieComb_one_iff r u _).2 rfl), hs _ _ pu⟩

end GlobalTheory.CM.IntCoord

namespace GlobalTheory.CM

open IntCoord

theorem integral_tangent_coordinates : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∀ u, IsTangent u → ∃! c, F.IsCoord u c) ∧ (∀ u u' c, F.IsCoord u c → F.IsCoord u' c → u = u') ∧ (∀ u u' c c', F.IsCoord u c → F.IsCoord u' c' → F.IsCoord (u * u') (c + c')) ∧ (∀ u u' c (r : 𝓞 K), F.IsCoord u c → IsLieComb ![r] ![u] u' → F.IsCoord u' (r • c)) ∧ (∀ c, c ∈ F.lieLat ↔ ∃ u, F.IsCoord u c) ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) c, c ∈ F.eigLat act τ ↔ ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a) := by
  intro K _ _ P F
  refine ⟨fun u hu => ?_, fun u u' c h h' => ?_, fun u u' c c' => isCoord_mul F, fun u u' c r => isCoord_smul F,
    fun c => ?_, fun O _ act τ c => ?_⟩
  · obtain ⟨w, hw, hw'⟩ := existsUnique_isVecOver F.fib.2.1.1 u
    obtain ⟨c, hc, hc'⟩ := F.basis.2 w (hw.isTangent F.fib.2.1 hu)
    exact ⟨c, ⟨hu, w, hw, hc⟩, fun c' ⟨_, w', h₁, h₂⟩ => hc' c' (hw' w' h₁ ▸ h₂)⟩
  · obtain ⟨-, w, hw, hc⟩ := h
    obtain ⟨-, w', hw', hc'⟩ := h'
    obtain rfl : w = w' := ((isLieComb_iff _ _ _).1 hc).trans ((isLieComb_iff _ _ _).1 hc').symm
    have := P.isAb.proper
    exact eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hw hw'
  · simpa [GenFib.lieLat] using mem_span_iff F (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ _ => trivial) c
  · refine mem_span_iff F (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a)) (fun a => ?_)
      (fun u u' h h' a => ?_) (fun r u h a => ?_) c
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_one, MonObj.one_comp]
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_mul, MonObj.mul_comp, (isLieComb_one_iff _ _ _).1 (h a),
        (isLieComb_one_iff _ _ _).1 (h' a)]
    · rw [isLieComb_one_iff, Category.assoc, (isLieComb_one_iff _ _ _).1 (h a), ← Category.assoc, sc_comm,
        Category.assoc]

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isFibreOf_iff_isPolFibre : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Nontrivial R'] (f : R →+* R') (A : Out.PolAV (Sp R)) (x : KeyIn R') (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (spMap f) φ ↔ IsPolFibre f A x.P φ := by
  intro R R' _ _ _ f A x φ
  refine ⟨fun h => ⟨?_, h.1, LBIso.symm h.2⟩, fun h => ⟨h.2.1, LBIso.symm h.2.2⟩⟩
  exact H1.dim_unique _ x.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1.1 A.smoothDim)
    (eSec x.P.A (Classical.arbitrary (PrimeSpectrum R')))

end GlobalTheory.LamF
end

