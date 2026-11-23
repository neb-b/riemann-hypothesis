module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter

noncomputable section

theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

theorem exists_isSheet_fin_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : ∃ γ, IsSheet P Ψ y w γ := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  refine ⟨fun _ => z, rfl, Eventually.of_forall fun y' => ⟨differentiableAt_const _, hz, ?_⟩⟩
  rw [Subsingleton.elim y' y]
  exact hΨ

theorem regularityPointsSum_holds.proof : regularityPointsSum_holds.Statement := by
  classical
  intro K _ ι _ P hP
  obtain ⟨k₀⟩ := hP.1
  have hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P 0 hP
  have hgood : IsGoodProj P hΨ.choose := hΨ.choose_spec
  have hF : (fibre P hΨ.choose (default : Fin 0 → ℂ)).Finite :=
    fibreFinite K ι P 0 hΨ.choose hP hgood default
  let pick : (((k : K) → ι k) → ℂ) → (Σ k, ι k) → ℂ := fun w =>
    if hγ : ∃ γ, IsSheet P hΨ.choose default w γ then hγ.choose default else 0
  have hpick : ∀ w ∈ fibre P hΨ.choose default, pick w ∈ mcPts P ∧ segre (pick w) = w := by
    intro w hw
    have hγ := exists_isSheet_fin_zero hw
    simp only [pick, dif_pos hγ]
    exact ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.1⟩
  have hone : ∀ w ∈ fibre P hΨ.choose default, hΨ.choose w 0 = 1 := by
    rintro w ⟨_, _, _, h⟩
    rw [h]
    rfl
  have hR : ∀ t ∈ hF.toFinset.image pick, ∃ w ∈ fibre P hΨ.choose default, t = pick w := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨w, hF.mem_toFinset.mp hw, rfl⟩
  refine ⟨hF.toFinset.image pick, fun t ht => ?_, fun z hz => ?_, fun h _ => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hR t ht
    exact (hpick w hw).1
  · have ha : hΨ.choose (segre z) 0 ≠ 0 := fun h0 =>
      hgood z hz (funext fun i => by rw [Fin.eq_zero i]; exact h0)
    set a := hΨ.choose (segre z) 0 with ha_def

    let c : K → ℂ := fun k => if k = k₀ then a⁻¹ else 1
    have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, ha]
    have hprod : ∏ k, c k = a⁻¹ := by
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
      simp [c]
    have hw₁ : segre (fun p => c p.1 * z p) ∈ fibre P hΨ.choose default := by
      refine ⟨_, mcPts_smul hP.2.1.2.1 c hc hz, rfl, funext fun i => ?_⟩
      rw [Fin.eq_zero i, segre_smul, hprod, map_smul, Pi.smul_apply, smul_eq_mul,
        ← ha_def, inv_mul_cancel₀ ha]
      rfl
    have hseg₁ : segre (fun p => c p.1 * z p) = a⁻¹ • segre z := by rw [segre_smul, hprod]

    have horb : ∀ t ∈ hF.toFinset.image pick, SameOrbit z t → segre t = a⁻¹ • segre z := by
      intro t ht ⟨c', _, hzt⟩
      obtain ⟨w, hw, rfl⟩ := hR t ht
      have hs : segre z = (∏ k, c' k) • segre (pick w) := by rw [hzt, segre_smul]
      have h1 : a = ∏ k, c' k := by
        rw [ha_def, hs, map_smul, Pi.smul_apply, smul_eq_mul, (hpick w hw).2, hone w hw, mul_one]
      rw [hs, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
    refine ⟨pick (segre (fun p => c p.1 * z p)), ⟨Finset.mem_image_of_mem _ (hF.mem_toFinset.mpr hw₁), ?_⟩,
      fun t ⟨ht, hzt⟩ => ?_⟩
    · refine sameOrbit_of_segre (hpick _ hw₁).1.1 a ha ?_
      rw [(hpick _ hw₁).2, hseg₁, smul_smul, mul_inv_cancel₀ ha, one_smul]
    · obtain ⟨w, hw, rfl⟩ := hR t ht
      have hw' : w = segre (fun p => c p.1 * z p) := by
        rw [← (hpick w hw).2, horb _ ht hzt, hseg₁]
      rw [hw']
  · unfold ptsIntegral
    rw [dif_pos hΨ]
    unfold ptsIntegralAt
    rw [integral_unique]
    have hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, MeasureTheory.volume_pi]
    rw [hvol, one_smul]
    refine (?_ : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ fibre P hΨ.choose y,
      sheetDensity P hΨ.choose (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h y w =
        ∑ t ∈ hF.toFinset.image pick, h t) _
    intro y
    rw [Subsingleton.elim y default, finsum_mem_eq_finite_toFinset_sum _ hF,
      Finset.sum_image fun x hx y hy hxy => by
        rw [← (hpick x (hF.mem_toFinset.mp hx)).2, hxy, (hpick y (hF.mem_toFinset.mp hy)).2]]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hγ := exists_isSheet_fin_zero (hF.mem_toFinset.mp hw)
    unfold sheetDensity
    rw [dif_pos hγ, maDensity_fin_zero, mul_one]
    simp only [pick, dif_pos hγ]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PIntClosureLocFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem IntClosureLocFinite.proof (h : RelAlgClosureFinite.Statement) :
    IntClosureLocFinite.Statement := by
  classical
  intro F L _ _ φ S hS A T hDA hloc
  let : Algebra A L := (φ.comp A.subtype).toAlgebra

  let D : Subring F := Subring.closure (T : Set F)
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T))
      (Subring.closureEquivAdjoinInt _).symm
  let : Algebra D L := (φ.comp D.subtype).toAlgebra
  let : Algebra D A := (Subring.inclusion hDA).toAlgebra
  have : IsScalarTower D A L := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let K := FractionRing D
  have hinj : Function.Injective (φ.comp D.subtype) := φ.injective.comp Subtype.val_injective
  let : Algebra K L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm
  have hKS : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.closure (S : Set L) := hS ▸ Subfield.mem_top x
    exact (Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr
      (IntermediateField.subset_adjoin K _) hx

  let M := algebraicClosure K L
  have : FiniteDimensional K M := h K L S hKS
  have : IsScalarTower D M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite D (integralClosure D M) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩

  let U : Submonoid D := (IsUnit.submonoid A).comap (Subring.inclusion hDA)
  have : IsLocalization U A := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩
    · obtain ⟨b, hb, c, hc, hc0, hcA, hzc⟩ := hloc z z.2
      have hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩) :=
        IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))
      exact ⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩
    · rw [Subring.inclusion_injective hDA hd]
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx

  obtain ⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x := ⟨_, rfl⟩
  rw [← hy] at hmx
  have hyK : IsIntegral K y := hmx.tower_top
  let yM : M := ⟨y, hyK⟩
  have hyMint : IsIntegral D yM := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]
    exact hmx
  have hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _) :=
    hs ▸ Submodule.mem_top
  let f : integralClosure D M →ₗ[D] L :=
    (IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap
  have hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L) := by
    have hmap := Submodule.mem_map_of_mem (f := f) hyspan
    rw [Submodule.map_span] at hmap
    rw [Finset.coe_image]
    exact hmap
  have hyA := Submodule.span_subset_span D A _ hyD

  have hu : IsUnit (algebraMap D A m) := hm
  have hyu : y = (hu.unit : A) • x := by
    rw [hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]
  have hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y := by
    rw [hyu, smul_smul, Units.inv_mul, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ hyA

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem hermLine_eq_of {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

theorem isSmoothHerm_hermZpow {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℤ) :
    IsSmoothHerm (hermZpow A m) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have h : (hermZpow A (n : ℤ)).h = fun z => A.h z ^ n := funext fun z => zpow_natCast (A.h z) n
    unfold IsSmoothHerm
    rw [h]
    exact hA.pow n
  · have h : (hermZpow A (-(n : ℤ))).h = fun z => (A.h z ^ n)⁻¹ :=
      funext fun z => by rw [← zpow_natCast, ← zpow_neg]; rfl
    unfold IsSmoothHerm
    rw [h]
    exact (hA.pow n).inv fun z hz => (pow_pos (A.pos z hz) n).ne'

def famExt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (e : Fin 2 → HermLine ι) : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => Fin 2 → ℝ) ℝ :=
  ∑ s : Fin n → Fin 2,
    I P n (e ∘ s) • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap fun j => LinearMap.proj (s j)

section Family

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}


omit [∀ k, Fintype (ι k)] in
theorem famExt_apply (e : Fin 2 → HermLine ι) (v : Fin n → Fin 2 → ℝ) :
    famExt I P n e v = ∑ s : Fin n → Fin 2, I P n (e ∘ s) * ∏ j, v j (s j) := by
  simp [famExt, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]


omit [∀ k, Fintype (ι k)] in
theorem famExt_basis (e : Fin 2 → HermLine ι) (t : Fin n → Fin 2) :
    famExt I P n e (fun j => Pi.single (t j) 1) = I P n (e ∘ t) := by
  rw [famExt_apply, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ t j := by
      by_contra h
      push Not at h
      exact hs (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem famExt_symm (hI : IsIntersectionFamily I) (hP : IsArithVar P n) (e : Fin 2 → HermLine ι)
    (he : ∀ i, IsSmoothHerm (e i)) : IsSymmForm (famExt I P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hI.1 P n (e ∘ s) σ.symm hP fun j => he _]

theorem fam_snoc_zpow_zero (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) :
    I P (n + 1) (Fin.snoc L (hermZpow X 0)) = 0 := by
  have e : (hermZpow X 0).tensor (hermZpow X 0) = hermZpow X 0 :=
    hermLine_eq_of (by simp [HermLine.tensor, hermZpow]) (by funext z; simp [HermLine.tensor, hermZpow])
  have h := hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX 0) (isSmoothHerm_hermZpow hX 0)
  rw [e] at h
  linarith

theorem fam_snoc_zpow_nat (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (k : ℕ) :
    I P (n + 1) (Fin.snoc L (hermZpow X k)) = k * I P (n + 1) (Fin.snoc L X) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact fam_snoc_zpow_zero hI hP L hL hX
  | succ k ih =>
    have e : hermZpow X ((k + 1 : ℕ) : ℤ) = (hermZpow X k).tensor X :=
      hermLine_eq_of (by simp [HermLine.tensor, hermZpow, add_smul])
        (funext fun z => by
          show X.h z ^ ((k + 1 : ℕ) : ℤ) = X.h z ^ (k : ℤ) * X.h z
          rw [zpow_natCast, zpow_natCast, pow_succ])
    rw [e, hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX k) hX, ih]
    push_cast
    ring

theorem fam_snoc_zpow (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (m : ℤ) :
    I P (n + 1) (Fin.snoc L (hermZpow X m)) = m * I P (n + 1) (Fin.snoc L X) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [fam_snoc_zpow_nat hI hP L hL hX k, Int.cast_natCast]
  · have hs : ∀ m : ℤ, IsSmoothHerm (hermZpow X m) := isSmoothHerm_hermZpow hX
    have hsum := hI.2.1 P n L _ _ hP hL (hs (-k)) (hs k)
    have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).mp hP.2.1.1.ne_top
    have hh : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
      intro d hd k'
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    have hT : I P (n + 1) (Fin.snoc L ((hermZpow X (-k)).tensor (hermZpow X k))) =
        I P (n + 1) (Fin.snoc L (hermZpow X 0)) := by
      rw [hI.2.2 P n L _ 1 0 hP hL (isSmoothHerm_tensor (hs _) (hs _))
          (fun k' => by simp [HermLine.tensor, hermZpow]) hh h1,
        hI.2.2 P n L _ 1 0 hP hL (hs 0) (fun k' => by simp [hermZpow]) hh h1, recR_eq, recR_eq]
      congr 1
      unfold arInt
      congr 1
      funext z
      unfold logNorm
      simp only [map_one, norm_one]
      show Real.log (1 / (X.h z ^ (-(k : ℤ)) * X.h z ^ (k : ℤ))) = Real.log (1 / X.h z ^ (0 : ℤ))
      rcases eq_or_ne (X.h z) 0 with hx | hx
      · rw [hx]
        rcases eq_or_ne k 0 with rfl | hk
        · simp
        · rw [zero_zpow (k : ℤ) (by exact_mod_cast hk), mul_zero]
          simp
      · rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hx)]
        simp
    rw [hT, fam_snoc_zpow_zero hI hP L hL hX, fam_snoc_zpow_nat hI hP L hL hX k] at hsum
    push_cast
    linarith

theorem fam_update_eq_snoc (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {B : HermLine ι}
    (hB : IsSmoothHerm B) :
    I P (n + 1) (Function.update L a B) =
      I P (n + 1) (Fin.snoc (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) B) := by
  have hs : ∀ j, IsSmoothHerm (Function.update L a B j) := by
    intro j
    rcases eq_or_ne j a with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      exact hL j
  rw [← hI.1 P (n + 1) _ (Equiv.swap a (Fin.last n)) hP hs]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Function.comp_apply, Fin.snoc_castSucc, Function.update_of_ne]
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h

end Family

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.SameOrbitOneSpecZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def VerticalClosedPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ∑ t ∈ R, Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ / ‖eval t (map (Int.castRingHom ℂ) g)‖)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

abbrev ProjectiveLineBundle.Diag {D : ℕ} (S : ProjectiveLineBundle D) : Ideal (MRing S.WIdx) :=
  T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 0)

section Statements

def ZeroSetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (s : MRing ι)
    (a : K → ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsMultiHomog s a → s ∉ P →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) ≠ 0 → g₁ z = g₂ z) →
    ptsIntegral P φ g₁ = ptsIntegral P φ g₂

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
end

