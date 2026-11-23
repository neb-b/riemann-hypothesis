module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeLocalFlat.proof (h : ConePolyLocalization.Statement.{u}) : ConeLocalFlat.Statement.{u} := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose v hv using hW.relevant
  obtain ⟨hA, hloc⟩ := h F K ι P hP W hW hPW v hv
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have : IsScalarTower (degZeroLoc P {W}) (MvPolynomial K (degZeroLoc P {W})) (coneLocal P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocal P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl
    exact Module.Flat.trans _ (MvPolynomial K (degZeroLoc P {W})) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
      (coneLocal P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocFrac.proof : DegZeroLocFrac.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro x hx

  let E : IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
    { carrier := {x | ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * y₂, Subalgebra.mul_mem _ hy₁ hy₂, z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂,
          mul_ne_zero hz₁0 hz₂0, by rw [div_mul_div_comm]⟩
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * z₂ + z₁ * y₂,
          Subalgebra.add_mem _ (Subalgebra.mul_mem _ hy₁ hz₂) (Subalgebra.mul_mem _ hz₁ hy₂),
          z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_ne_zero hz₁0 hz₂0,
          by rw [div_add_div _ _ hz₁0 hz₂0]⟩
      algebraMap_mem' := fun c => ⟨algebraMap F _ c, Subalgebra.algebraMap_mem _ c, 1,
        Subalgebra.one_mem _, one_ne_zero, (div_one _).symm⟩
      inv_mem' := by
        rintro _ ⟨y, hy, z, hz, hz0, rfl⟩
        by_cases hy0 : y = 0
        · exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by simp [hy0]⟩
        · exact ⟨z, hz, y, hy, hy0, by rw [inv_div]⟩ }
  suffices hle : homFracDegZero P ≤ E from hle hx
  unfold homFracDegZero
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩

  obtain ⟨e, h, hh, hbe, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := h𝒲P W (h𝒲.mem_toFinset.mp hW)
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) b
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmP⟩ := exists_form_not_mem_of_isRelevant (H := P) hP.relevant (e - b)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    div_ne_zero (hq0 _ fun h' => (hP.isPrime.mem_or_mem h').elim hgP hmP) (hq0 _ hhP), ?_⟩
  simp only [map_mul]
  rw [div_div_div_cancel_right₀ (hq0 _ hhP), mul_div_mul_right _ _ (hq0 _ hmP)]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocal.proof (h : DegZeroLocQuot.Statement.{u}) : DegZeroLocLocal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have hWp : W.IsPrime := hW.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hrep : ∀ x : degZeroLoc P {W}, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ P ∧ g ∉ W ∧
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := fun x => by
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := h F K ι P {W}
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) x x.2
    exact ⟨b, f, g, hf, hg, hgP, hgW W (Set.mem_singleton W), hx⟩

  have hnon : ∀ (x : degZeroLoc P {W}) (f g : MRing ι F), g ∉ W → f ∈ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → ¬ IsUnit x := by
    intro x f g hgW hfW hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := hrep y
    have hgP : g ∉ P := fun hg => hgW (hPW hg)
    have h1 : ((x * y : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = 1 := by
      rw [hy]; rfl
    rw [Subalgebra.coe_mul, hx, hy', div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
      ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' hfW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hWp.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W h4]

  have hunit : ∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
      IsMultiHomog g b → g ∉ P → f ∉ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → IsUnit x := by
    intro x b f g hf hg hgP hfW hx
    have hfP : f ∉ P := fun h' => hfW (hPW h')
    have hmem := div_mem_degZeroLoc P {W} hg hf hfP
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hfW)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, hx, div_mul_div_comm, mul_comm (algebraMap _ _ _),
      div_self (mul_ne_zero (hne g hgP) (hne f hfP))]
  have : Nontrivial (degZeroLoc P {W}) :=
    ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a c ha hc
  obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := hrep a
  obtain ⟨b', f', g', hf', hg', hg'P, hg'W, hy⟩ := hrep c
  have hfW : f ∈ W := by
    by_contra hfW
    exact (mem_nonunits_iff.mp ha) (hunit a b f g hf hg hgP hfW hx)
  have hf'W : f' ∈ W := by
    by_contra hf'W
    exact (mem_nonunits_iff.mp hc) (hunit c b' f' g' hf' hg' hg'P hf'W hy)
  refine mem_nonunits_iff.mpr (hnon (a + c) (f * g' + g * f') (g * g') (fun h5 => ?_)
    (W.add_mem (W.mul_mem_right g' hfW) (W.mul_mem_left g hf'W)) ?_)
  · rcases hWp.mem_or_mem h5 with h6 | h6
    exacts [hgW h6, hg'W h6]
  · rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (hne g hgP) (hne g' hg'P)]
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_add, map_mul]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocNoetherian.proof (h : DegZeroLocQuot.Statement.{u}) :
    DegZeroLocNoetherian.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  let φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    (IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)
  have hφ : ∀ f, f ∉ P → φ f ≠ 0 := fun f hf h0 => hf (by
    rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)
  choose v hv using hW.relevant
  let e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)
  let c : (K → ℕ) → MRing ι F := fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k
  have hcW : ∀ b, c b ∉ W := by
    intro b
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
  have hc : ∀ b, IsMultiHomog (c b) b := by
    intro b
    have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))
    have hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hb] at hprod
    exact hprod
  have hcadd : ∀ b b', c (b + b') = c b * c b' := fun b b' => by
    simp only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hmono : ∀ m : (Σ k, ι k) →₀ ℕ,
      φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m)) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · simp [c]
    · intro x n m _ _ ih
      have hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) *
          φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n))) := by
        rw [Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]
        have hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n := by
          simp only [c, blockWeight]
          rw [Finset.prod_eq_single x.1]
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        rw [hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]
      rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add (f := _), hcadd, map_mul, hs]
      ring

  have hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b) := by
    intro b f hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    have hmon : monomial m (AddMonoidAlgebra.coeff f m) = AddMonoidAlgebra.coeff f m • monomial m (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]
  have hle : e.range ≤ degZeroLoc P {W} := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm))
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)
  have : Algebra.FiniteType F e.range :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have _ : IsNoetherianRing e.range := Algebra.FiniteType.isNoetherianRing F e.range
  let _ : Algebra e.range (degZeroLoc P {W}) := (Subalgebra.inclusion hle).toAlgebra
  let M : Submonoid e.range :=
    (IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))
  have hloc : IsLocalization M (degZeroLoc P {W}) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_,
      fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hz⟩ := h F K ι P {W}
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2
    have hgW' : g ∉ W := hgW W rfl
    have hcb : φ (c b) ≠ 0 := hφ _ fun hm => hcW b (hPW hm)
    have hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g := hz
    have heg : e g ≠ 0 := by
      intro h0
      apply hφ g hgP
      rw [hhom b g hg, h0, zero_mul]
    have hinv : (e g)⁻¹ ∈ degZeroLoc P {W} := by
      have hq : (e g)⁻¹ = φ (c b) / φ g := by
        rw [hhom b g hg]
        field_simp
      rw [hq]
      exact div_mem_degZeroLoc P {W} (hc b) hg hgP
        (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')
    have hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M :=
      isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩
    refine ⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι F ⧸ P)) * e g = e f
    rw [hz', hhom b f hf, hhom b g hg]
    field_simp
  exact IsLocalization.isNoetherianRing M _ inferInstance

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocQuot.proof : DegZeroLocQuot.Statement := by
  intro F _ K _ ι P _ 𝒲 h𝒲 x hx

  set φ : MRing ι F →+* FractionRing (MRing ι F ⧸ P) :=
    (algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))).comp (Ideal.Quotient.mk P) with hφ
  have hne : ∀ g : MRing ι F, g ∉ P → φ g ≠ 0 := fun g hg => by
    rw [hφ, RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  let Q : FractionRing (MRing ι F ⧸ P) → Prop := fun y =>
    ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧ y = φ f / φ g
  have key : Q x := by
    refine Algebra.adjoin_induction (p := fun y _ => Q y) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
      exact ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
    · intro c
      refine ⟨0, C c, 1, isWeightedHomogeneous_C _ c, isWeightedHomogeneous_one F _, ?_, ?_, ?_⟩
      · exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
      · intro W hW
        exact (Ideal.ne_top_iff_one W).mp (h𝒲 W hW).ne_top
      · rw [map_one, div_one, hφ, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))]
        rfl
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * g' + g * f', g * g', (hf.mul hg').add (hg.mul hf'), hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_add_div _ _ (hne g hgP) (hne g' hgP'), map_add (f := _), map_mul, map_mul, map_mul]
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * f', g * g', hf.mul hf', hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_mul_div_comm, map_mul, map_mul]
  exact key

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ringKrullDim_eq_of_relDim {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  unfold relDim at h
  rw [hm] at h
  cases hd : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [hd] at h
    exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      exact absurd h (WithTop.top_ne_coe)
    | coe D =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      change (((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h
      have h := WithTop.coe_inj.mp h
      have : D = m + Fintype.card K := by omega
      rw [this]
      rfl

theorem DegZeroLocalRing.proof (h1 : DegZeroLocLocal.Statement.{u})
    (h2 : DegZeroLocNoetherian.Statement.{u}) (h3 : DegZeroLocDim.Statement.{u}) :
    DegZeroLocalRing.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  refine ⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩
  have e := h3 F K ι P hP W hW hPW
  rw [ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn] at e
  revert e
  generalize ringKrullDim (degZeroLoc P {W}) = d
  intro e
  cases d with
  | bot =>
    rw [WithBot.bot_add] at e
    exact absurd e WithBot.bot_ne_coe
  | coe d =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at e
    induction d using ENat.recTopCoe with
    | top =>
      rw [top_add] at e
      exact absurd e.symm (ENat.natCast_ne_top _)
    | coe d =>
      rw [← Nat.cast_add, Nat.cast_inj] at e
      have : d = 1 := by omega
      rw [this]
      rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

