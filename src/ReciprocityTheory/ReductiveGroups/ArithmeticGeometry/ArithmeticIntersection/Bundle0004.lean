module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LintegralIoiOfRealMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaB
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open MeasureTheory

theorem integral_sphere_isometry (L : E3 ≃ₗᵢ[ℝ] E3) (F : E3 → ℝ)
    (hF : Integrable (fun n : S2 => F n) sphereMeasure) :
    ∫ n : S2, F (L n) ∂sphereMeasure = ∫ n : S2, F n ∂sphereMeasure := by
  have hinv := sphereInv_thm
  unfold SphereInvStatement at hinv
  have hmp := hinv.2 L
  have h := integral_map (μ := sphereMeasure) hmp.measurable.aemeasurable
    (f := fun m : S2 => F (m : E3)) (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

theorem integrable_mul_inner {F : S2 → ℝ} (hF : Integrable F sphereMeasure) (v : E3) :
    Integrable (fun n : S2 => F n * inner ℝ (n : E3) v) sphereMeasure := by
  have hc : Continuous (fun n : S2 => inner ℝ (n : E3) v) :=
    continuous_subtype_val.inner continuous_const
  refine Integrable.mono' (hF.norm.mul_const ‖v‖)
    (hF.aestronglyMeasurable.mul hc.aestronglyMeasurable) (ae_of_all _ fun n => ?_)
  have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
  have hb : |inner ℝ (n : E3) v| ≤ ‖v‖ := by
    calc |inner ℝ (n : E3) v| ≤ ‖(n : E3)‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖v‖ := by rw [hn, one_mul]
  rw [norm_mul, Real.norm_eq_abs (inner ℝ (n : E3) v)]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

section moments

variable {u : E3} {f : ℝ → ℝ}

theorem moment1_inv (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    (L : E3 ≃ₗᵢ[ℝ] E3) (hL : L u = u) (v : E3) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (L v) ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure := by
  have key : ∀ x y : E3, inner ℝ (L.symm x) y = inner ℝ x (L y) := by
    intro x y
    rw [← L.inner_map_map (L.symm x) y, L.apply_symm_apply]
  have h := integral_sphere_isometry L.symm (fun x => f (inner ℝ x u) * inner ℝ x v)
    (integrable_mul_inner hI v)
  simp only [key, hL] at h
  exact h

theorem moment2_inv (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    (L : E3 ≃ₗᵢ[ℝ] E3) (hL : L u = u) (v w : E3) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (L v) * inner ℝ (n : E3) (L w)
        ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w
        ∂sphereMeasure := by
  have key : ∀ x y : E3, inner ℝ (L.symm x) y = inner ℝ x (L y) := by
    intro x y
    rw [← L.inner_map_map (L.symm x) y, L.apply_symm_apply]
  have h := integral_sphere_isometry L.symm (fun x => f (inner ℝ x u) * inner ℝ x v * inner ℝ x w)
    (integrable_mul_inner (integrable_mul_inner hI v) w)
  simp only [key, hL] at h
  exact h

theorem reflection_fix {a c : E3} (h : inner ℝ a c = 0) : (ℝ ∙ a)ᗮ.reflection c = c := by
  have hc : c ∈ (ℝ ∙ a)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.2 h
  exact Submodule.reflection_mem_subspace_eq_self hc

theorem moment1_perp (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    {a : E3} (ha : inner ℝ a u = 0) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a ∂sphereMeasure = 0 := by
  have hRu : (ℝ ∙ a)ᗮ.reflection u = u := reflection_fix ha
  have hRa : (ℝ ∙ a)ᗮ.reflection a = -a :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg a
  have h := moment1_inv hI ((ℝ ∙ a)ᗮ.reflection) hRu a
  rw [hRa] at h
  simp only [inner_neg_right, mul_neg, integral_neg] at h
  linarith

theorem moment2_perp (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    {a c : E3} (ha : inner ℝ a u = 0) (hc : inner ℝ a c = 0) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a * inner ℝ (n : E3) c
      ∂sphereMeasure = 0 := by
  have hRu : (ℝ ∙ a)ᗮ.reflection u = u := reflection_fix ha
  have hRc : (ℝ ∙ a)ᗮ.reflection c = c := reflection_fix hc
  have hRa : (ℝ ∙ a)ᗮ.reflection a = -a :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg a
  have h := moment2_inv hI ((ℝ ∙ a)ᗮ.reflection) hRu a c
  rw [hRa, hRc] at h
  simp only [inner_neg_right, mul_neg, neg_mul, integral_neg] at h
  linarith

theorem moment2_swap (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    {a c : E3} (ha : inner ℝ a u = 0) (hc : inner ℝ c u = 0) (hac : ‖a‖ = ‖c‖) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) c * inner ℝ (n : E3) c ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a * inner ℝ (n : E3) a
        ∂sphereMeasure := by
  have hdu : inner ℝ (a - c) u = 0 := by rw [inner_sub_left, ha, hc, sub_zero]
  have hRu : (ℝ ∙ (a - c))ᗮ.reflection u = u := reflection_fix hdu
  have hRa : (ℝ ∙ (a - c))ᗮ.reflection a = c := Submodule.reflection_sub hac
  have h := moment2_inv hI ((ℝ ∙ (a - c))ᗮ.reflection) hRu a a
  rw [hRa] at h
  exact h

end moments

theorem exists_basis_zero_eq {u : E3} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = u := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).restrict fun _ : Fin 3 => u) := by
    refine ⟨fun _ => hu, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hv
  exact ⟨b, hb 0 rfl⟩

private theorem integral_const_mul_sphereMeasure (c : ℝ) (g : S2 → ℝ) :
    ∫ n, c * g n ∂sphereMeasure = c * ∫ n, g n ∂sphereMeasure := by
  exact integral_const_mul c g

theorem archimedes_thm : ArchimedesStatement := by
  unfold ArchimedesStatement
  intro u v w f hu hf
  obtain ⟨b, hb⟩ := exists_basis_zero_eq hu
  have hf1 : IntervalIntegrable (fun t => f t * t) MeasureTheory.volume (-1) 1 :=
    hf.mul_continuousOn continuousOn_id
  have hf2 : IntervalIntegrable (fun t => f t * t * t) MeasureTheory.volume (-1) 1 :=
    hf1.mul_continuousOn continuousOn_id
  obtain ⟨hI, h0⟩ := arch0 u f hu hf
  have h1 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u ∂sphereMeasure
      = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t := (arch0 u (fun t => f t * t) hu hf1).2
  have hI1 : Integrable (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u) sphereMeasure :=
    integrable_mul_inner hI u
  have h2 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u ∂sphereMeasure
      = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := (arch0 u (fun t => f t * t * t) hu hf2).2
  have hI2 : Integrable (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u)
      sphereMeasure := integrable_mul_inner hI1 u
  have horth : ∀ i j : Fin 3, i ≠ j → inner ℝ (b i) (b j) = 0 := fun i j h => b.orthonormal.2 h
  have hnorm : ∀ i : Fin 3, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hbu : ∀ i : Fin 3, i ≠ 0 → inner ℝ (b i) u = 0 := by
    intro i hi; rw [← hb]; exact horth i 0 hi
  have hexp : ∀ x y : E3, inner ℝ x y = ∑ i, inner ℝ (b i) y * inner ℝ x (b i) := by
    intro x y
    rw [← b.sum_inner_mul_inner x y]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hX : ∀ i : Fin 3, i ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) (b i) ∂sphereMeasure = 0 :=
    fun i hi => moment1_perp (u := u) (f := fun t => f t * t) hI1 (hbu i hi)
  have hG : ∀ i j : Fin 3, Integrable (fun n : S2 =>
      f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j)) sphereMeasure :=
    fun i j => integrable_mul_inner (integrable_mul_inner hI (b i)) (b j)
  have hpt1 : ∀ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v =
      ∑ i, inner ℝ (b i) v * (f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i)) := by
    intro n
    rw [hexp (n : E3) v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hkey1 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      ∑ i, inner ℝ (b i) v * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) ∂sphereMeasure := by
    simp only [hpt1]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => integral_const_mul_sphereMeasure _ _
    · intro i _; exact (integrable_mul_inner hI (b i)).const_mul _
  have hpt : ∀ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w =
      ∑ i, ∑ j, (inner ℝ (b i) v * inner ℝ (b j) w) *
        (f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j)) := by
    intro n
    rw [hexp (n : E3) v, hexp (n : E3) w]
    simp only [Fin.sum_univ_three]
    ring
  have hkey : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      ∑ i, ∑ j, (inner ℝ (b i) v * inner ℝ (b j) w) * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j) ∂sphereMeasure := by
    simp only [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun j _ => integral_const_mul_sphereMeasure _ _)
      · intro j _; exact (hG i j).const_mul _
    · intro i _; exact integrable_finsetSum _ (fun j _ => (hG i j).const_mul _)
  have hM00 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b 0) ∂sphereMeasure = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := by
    rw [hb]; exact h2
  have hM0 : ∀ j : Fin 3, j ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b j) ∂sphereMeasure = 0 := by
    intro j hj; rw [hb]; exact hX j hj
  have hM0' : ∀ j : Fin 3, j ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b j) * inner ℝ (n : E3) (b 0) ∂sphereMeasure = 0 := by
    intro j hj
    have e : (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b j) * inner ℝ (n : E3) (b 0)) =
        fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b j) := by
      funext n; ring
    rw [e]; exact hM0 j hj
  have hM12 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 2) ∂sphereMeasure = 0 :=
    moment2_perp hI (hbu 1 (by decide)) (horth 1 2 (by decide))
  have hM21 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 1) ∂sphereMeasure = 0 :=
    moment2_perp hI (hbu 2 (by decide)) (horth 2 1 (by decide))
  have hM22 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) ∂sphereMeasure = ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure :=
    moment2_swap hI (hbu 1 (by decide)) (hbu 2 (by decide))
      (by rw [hnorm, hnorm])
  have hsq : ∀ n : S2, inner ℝ (n : E3) u * inner ℝ (n : E3) u + inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) +
      inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) = 1 := by
    intro n
    have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
    have h := hexp (n : E3) (n : E3)
    rw [Fin.sum_univ_three, hb, real_inner_self_eq_norm_sq, hn, one_pow,
      real_inner_comm (n : E3) u, real_inner_comm (n : E3) (b 1),
      real_inner_comm (n : E3) (b 2)] at h
    linarith
  have hsum : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure + ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure - ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u ∂sphereMeasure := by
    rw [← integral_add (hG 1 1) (hG 2 2), ← integral_sub hI hI2]
    congr 1; funext n
    linear_combination (f (inner ℝ (n : E3) u)) * hsq n
  have hQ : 2 * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure =
      1 / 2 * (∫ t in (-1 : ℝ)..1, f t) - 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := by
    linarith [hsum, hM22, h0, h2]
  have hγ : inner ℝ (b 1) v * inner ℝ (b 1) w + inner ℝ (b 2) v * inner ℝ (b 2) w =
      inner ℝ v w - inner ℝ u v * inner ℝ u w := by
    have h := hexp v w
    rw [Fin.sum_univ_three, hb, real_inner_comm u v, real_inner_comm (b 1) v,
      real_inner_comm (b 2) v] at h
    linarith
  have hJ : ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)) =
      (inner ℝ u v * inner ℝ u w - (inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2) *
          (∫ t in (-1 : ℝ)..1, f t * t * t) +
        (inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2 * ∫ t in (-1 : ℝ)..1, f t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hf2.const_mul _) (hf.const_mul _)]
    congr 1; funext t; ring
  refine ⟨hI, h0, ?_, ?_⟩
  · rw [hkey1, Fin.sum_univ_three, moment1_perp hI (hbu 1 (by decide)),
      moment1_perp hI (hbu 2 (by decide)), hb, h1, intervalIntegral.integral_mul_const]
    ring
  · rw [hkey, hJ]
    simp only [Fin.sum_univ_three]
    rw [hM00, hM0 1 (by decide), hM0 2 (by decide), hM0' 1 (by decide), hM0' 2 (by decide),
      hM12, hM21, hM22, hb]
    linear_combination (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure) * hγ +
      ((inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2) * hQ

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

section
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem krullDimLE_one_of_krullDim_eq (h : ringKrullDim A = 1) : Ring.KrullDimLE 1 A := by
  rw [Ring.krullDimLE_iff, h]
  simp

theorem krullDim_quotient_eq_one_iff_eq_bot [Ring.KrullDimLE 1 A] (h : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 ↔ p.asIdeal = ⊥ := by
  constructor
  · intro hq
    by_contra hne
    have hmax : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot p.isPrime hne
    have h0 := ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    rw [h0] at hq
    exact zero_ne_one hq
  · intro hp
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hp).trans (RingEquiv.quotientBot A)), h]

theorem length_coker_ne_top (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Ring.KrullDimLE 1 A] {x : A} (hx : x ≠ 0) :
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ := by
  have htors : Module.IsTorsionBy A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) x := by
    intro n
    refine Submodule.Quotient.induction_on _ n (fun m => ?_)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, rfl⟩
  have htors' : Module.IsTorsionBySet A (M ⧸ LinearMap.range (LinearMap.lsmul A M x))
      (Ideal.span {x} : Set A) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr htors
  letI : Module (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) := htors'.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    htors'.isScalarTower
  haveI : Ring.KrullDimLE 0 (A ⧸ Ideal.span {x}) := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have hc : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P).IsPrime := Ideal.IsPrime.comap _
    have hne : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P ≠ ⊥ := by
      intro h0
      have hxm : x ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
        exact P.zero_mem
      rw [h0, Ideal.mem_bot] at hxm
      exact hx hxm
    haveI hm := Ideal.IsPrime.isMaximal_of_ne_bot hc hne
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.Quotient.mk_surjective
    have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj
      (m := Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P) (by
        intro a ha
        rw [RingHom.mem_ker] at ha
        rw [Ideal.mem_comap, ha]
        exact P.zero_mem)
    rwa [Ideal.map_comap_of_surjective _ hsurj] at hmap
  haveI : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  haveI : Module.Finite (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hs : Function.Surjective (algebraMap A (A ⧸ Ideal.span {x})) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem length_ker_eq_zero_of_torsionFree (M : Type*) [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M]
    {x : A} (hx : x ≠ 0) :
    length A (LinearMap.ker (LinearMap.lsmul A M x)) = 0 := by
  rw [Module.length_eq_zero_iff]
  have hreg : IsSMulRegular M x := IsSMulRegular.of_ne_zero hx
  have hker : LinearMap.ker (LinearMap.lsmul A M x) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun a b hab => hreg (by simpa using hab))
  rw [hker]
  infer_instance

theorem length_localization_bot_eq_finrank (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    length (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) =
      (finrank A M : ℕ∞) := by
  have hfield : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hfield.toField
  have hle : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := by
    intro a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => ha (by rw [h0]; exact Submodule.zero_mem _))
  haveI : Module.Finite (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) :=
    Module.Finite.of_isLocalizedModule (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M)
  rw [Module.length_of_free_of_finite, Module.length_eq_one, mul_one]
  rw [IsLocalization.finrank_eq (Localization.AtPrime (⊥ : Ideal A)) (⊥ : Ideal A).primeCompl hle,
    IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M) hle]

theorem ordQuotient_bot (x : A) :
    ordMod ⟨⊥, Ideal.isPrime_bot⟩ x = Ring.ord A x := by
  unfold ordMod Ring.ord
  dsimp only
  have hs : Function.Surjective (algebraMap A (A ⧸ (⊥ : Ideal A))) := Ideal.Quotient.mk_surjective
  rw [← Module.length_eq_of_surjective hs]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ A (⊥ : Ideal A)) (Ideal.span {x}) =
      Ideal.span {Ideal.Quotient.mk (⊥ : Ideal A) x} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  have e1 := (Ideal.quotientEquivAlgOfEq A h1).symm.trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ A ⊥ (Ideal.span {x})).trans
      (Ideal.quotientEquivAlgOfEq A (bot_sup_eq (Ideal.span {x}))))
  exact e1.toLinearEquiv.length_eq

end

theorem dimOneTorsionFreeFormula : LocalLengthAdditivityTorsionFree := by
  intro A _ _ _ _ M _ _ _ _ x h hx
  haveI : Ring.KrullDimLE 1 A := krullDimLE_one_of_krullDim_eq h
  obtain ⟨-, heq⟩ := dimOneFormula A M x h (length_coker_ne_top M hx)
  rw [heq, length_ker_eq_zero_of_torsionFree M hx, zero_add]
  have hset : {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1} = {⟨⊥, Ideal.isPrime_bot⟩} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [krullDim_quotient_eq_one_iff_eq_bot h p]
    constructor
    · intro hp
      ext1
      exact hp
    · intro hp
      rw [hp]
  change ∑ᶠ p ∈ {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}, _ = _
  rw [hset, finsum_mem_singleton]
  dsimp only
  rw [length_localization_bot_eq_finrank, ordQuotient_bot]

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Polynomial

end ReciprocityTheory.ChartRestriction.G.AI
end

