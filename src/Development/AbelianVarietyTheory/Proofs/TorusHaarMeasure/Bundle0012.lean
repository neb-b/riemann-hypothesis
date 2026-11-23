module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetMul
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.ValMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_gram_mul_right_re {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (N : Matrix n ι ℂ) (B : Matrix ι ι ℂ) :
    ((N * B)ᴴ * (N * B)).det.re = Complex.normSq B.det * (Nᴴ * N).det.re := by
  rw [Matrix.conjTranspose_mul,
    show Bᴴ * Nᴴ * (N * B) = Bᴴ * (Nᴴ * N) * B by simp only [Matrix.mul_assoc],
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : star B.det * (Nᴴ * N).det * B.det = (Complex.normSq B.det : ℂ) * (Nᴴ * N).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [h, Complex.re_ofReal_mul]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.ValMul.value_mul_eq : ((∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ A : Matrix ι ι (𝓞 E), A.det ≠ 0 → ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X x ι _ _ w hw hwΛ A hA
  classical
  set w' : ι → Fin r → E := fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b with hw'
  have hsmul : ∀ (c : 𝓞 E) (v : Fin r → E), c • v = (c : E) • v := fun c v => rfl

  have hmat : ∀ τ : X.Ψ, (Matrix.of fun k a => τ.1 (w' a k)) =
      (Matrix.of fun k a => τ.1 (w a k)) * A.map (fun c => τ.1 (c : E)) := by
    intro τ
    ext k a
    simp [Matrix.mul_apply, w', Finset.sum_apply, Algebra.smul_def, mul_comm]
  have hnum : ∀ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))).det.re) =
      ‖τ.1 (A.det : E)‖ ^ 2 * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    rw [hmat τ, ← Matrix.mul_assoc (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹, det_gram_mul_right_re]
    congr 1
    have hd : (A.map fun c => τ.1 (c : E)).det = τ.1 (A.det : E) := by
      have := RingHom.map_det (τ.1.comp (algebraMap (𝓞 E) E)) A
      exact this.symm
    rw [hd, Complex.normSq_eq_norm_sq]
  have hspanE : Submodule.span E (Set.range w') = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨c, rfl⟩
      set B : Matrix ι ι E := A.map fun t => (t : E) with hB
      have hBdet : IsUnit B.det := by
        have h := RingHom.map_det (algebraMap (𝓞 E) E) A
        have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hA
        refine isUnit_iff_ne_zero.mpr ?_
        have hB' : B.det = ((A.det : 𝓞 E) : E) := h.symm
        rw [hB']
        exact h0
      have hrec : ∑ a, B⁻¹ a c • w' a = w c := by
        calc ∑ a, B⁻¹ a c • w' a = ∑ a, ∑ b, (B b a * B⁻¹ a c) • w b := by
              refine Finset.sum_congr rfl fun a _ => ?_
              simp only [w', Finset.smul_sum, smul_smul, hB, Matrix.map_apply, mul_comm]
          _ = ∑ b, (B * B⁻¹) b c • w b := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Matrix.mul_apply, Finset.sum_smul]
          _ = w c := by
              rw [Matrix.mul_nonsing_inv B hBdet]
              simp [Matrix.one_apply]
      rw [← hrec]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hle1 : (Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup ≤
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hle2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
    intro v hv
    have hv' : v ∈ Submodule.span (𝓞 E) (Set.range w) := hv
    refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Submodule.span_le.mpr ?_ hv'
      rintro _ ⟨a, rfl⟩
      exact hwΛ a
    · show v ∈ Submodule.span E (Set.range w)
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv'
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hidx : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    let ψ : (ι → 𝓞 E) →+ (Fin r → E) :=
      { toFun := fun c => ∑ b, ((c b : 𝓞 E) : E) • w b
        map_zero' := by simp
        map_add' := by
          intro c d
          simp [add_smul, Finset.sum_add_distrib] }
    have hψ : ∀ c, ψ c = ∑ b, ((c b : 𝓞 E) : E) • w b := fun c => rfl
    have hψinj : Function.Injective ψ := by
      intro c d hcd
      have h0 : ∑ b, (((c b : 𝓞 E) : E) - ((d b : 𝓞 E) : E)) • w b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hψ, ← hψ]
        exact sub_eq_zero.mpr hcd
      funext b
      have := Fintype.linearIndependent_iff.mp hw _ h0 b
      exact RingOfIntegers.coe_injective (sub_eq_zero.mp this)
    have hψmem : ∀ c, ψ c ∈ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
      intro c
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w)
      rw [hψ]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    let φ : (ι → 𝓞 E) →+ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup :=
      ψ.codRestrict _ hψmem
    have hφsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv
      refine ⟨c, Subtype.ext ?_⟩
      show ψ c = _
      rw [hψ]
      exact Finset.sum_congr rfl fun b _ => (hsmul (c b) (w b)).symm
    have hlin : ∀ v : ι → 𝓞 E, ∑ a, v a • w' a = ψ (A.mulVec v) := by
      intro v
      rw [hψ]
      calc ∑ a, v a • w' a = ∑ a, ∑ b, (((A b a : 𝓞 E) : E) * ((v a : 𝓞 E) : E)) • w b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [w', hsmul, Finset.smul_sum, smul_smul, mul_comm]
        _ = ∑ b, ((A.mulVec v b : 𝓞 E) : E) • w b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [Matrix.mulVec, dotProduct]
            push_cast
            rw [Finset.sum_smul]
    have hcomap : ((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup).comap φ =
        (LinearMap.range A.mulVecLin).toAddSubgroup := by
      ext c
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w') ↔ c ∈ LinearMap.range A.mulVecLin
      rw [Submodule.mem_span_range_iff_exists_fun, LinearMap.mem_range]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨v, hψinj (by rw [Matrix.mulVecLin_apply, ← hlin]; exact hv)⟩
      · rintro ⟨v, rfl⟩
        exact ⟨v, hlin v⟩
    rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφsurj, hcomap]
    exact _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det ι A hA
  have hidxR : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℝ) =
      ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) := by
    exact_mod_cast hidx
  have hN : ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) ≠ 0 := by
    have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by
      exact_mod_cast hA
    have := (Algebra.norm_ne_zero_iff (R := ℚ)).mpr h0
    positivity
  rw [Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib,
    ← _root_.GlobalTheory.abs_norm_eq_prod_cmType_sq r X, hspanE, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Nat.cast_mul, hidxR, mul_div_mul_left _ _ hN]

end GlobalTheory.ValMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOrthUpdateMulInv
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma inv_keeps_gram {r : ℕ} {J a : Matrix (Fin r) (Fin r) ℂ} (hJ : J.det ≠ 0)
    (ha : aᵀ * J * a.map (starRingEnd ℂ) = J) :
    (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ) = J := by
  have hdet : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
    rw [← ha, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have h2 : (a⁻¹)ᵀ * aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  calc (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ)
      = (a⁻¹)ᵀ * (aᵀ * J * a.map (starRingEnd ℂ)) * (a⁻¹).map (starRingEnd ℂ) := by rw [ha]
    _ = ((a⁻¹)ᵀ * aᵀ) * J * (a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

theorem isOrth_update_mul_inv :
    (∀ (r : ℕ) (X : Data E r) (τ0 : X.Ψ) (x : Frame X.Ψ r) (a : Matrix (Fin r) (Fin r) ℂ), IsOrth X x → (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → IsOrth X (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X τ0 x a hx ha τ
  letI : DecidableEq X.Ψ := Classical.decEq _
  by_cases hτ : τ = τ0
  · subst hτ
    have hm : mat (Function.update x τ (mat x τ * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ * a⁻¹ := by
      unfold mat
      exact Function.update_self _ _ _
    have hJ : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)
        = gram τ.1 X.Gm (mat x τ) := by
      rw [hx τ]
      congr 1
      funext k
      unfold sgn
      split_ifs <;> simp
    have hdet : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1).det
        ≠ 0 := by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      split_ifs <;> simp
    have h := inv_keeps_gram hdet ha
    rw [hJ] at h
    rw [hm, ← hx τ, ← h, GlobalTheory.UnitaryFrames.gram_eq_mul, GlobalTheory.UnitaryFrames.gram_eq_mul,
      Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  · have hm : mat (Function.update x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ := by
      unfold mat
      exact Function.update_of_ne hτ _ _
    rw [hm]
    exact hx τ

end GlobalTheory.FiniteCovolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatDen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem latDen : (∀ (r : ℕ) (X : Data E r), (∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ) ∧ ∃ n : ℕ, 0 < n ∧ ∀ v ∈ X.Λ, ∀ k, IsIntegral ℤ ((n : E) * v k)) := by
  intro r X
  have hsq : ∀ k : ℤ, (((k.natAbs * k.natAbs : ℕ)) : E) = (k : E) * (k : E) := by
    intro k
    have h : ((k.natAbs * k.natAbs : ℕ) : ℤ) = k * k := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' k
    rw [← Int.cast_natCast, h, Int.cast_mul]
  have hpos : ∀ k : ℤ, k ≠ 0 → 0 < k.natAbs * k.natAbs := fun k hk =>
    Nat.mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨k, hk, hm⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
    refine ⟨_, hpos k hk, ?_⟩
    rw [hsq, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact zsmul_mem hm k
  · obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den X.Λ X.Λ_fg
    refine ⟨_, hpos k hk, fun v hv a => ?_⟩
    rw [hsq, mul_assoc]
    have h1 : IsIntegral ℤ (k : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := k))
    exact h1.mul (hi v hv a)

end GlobalTheory.LatDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajorantEqSumNormSqOrthonormalFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.MajorantOrthFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
      (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
        X.maj x τ v = ∑ a, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by
  intro r X x hx
  refine ⟨_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx, fun τ v => ?_⟩
  have hdet : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 := _root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx τ
  have hG : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := hx τ
  set P := _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ with hP
  set c := P⁻¹ *ᵥ v with hc
  have hv : v = P *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v (_root_.ReciprocityTheory.ChartRestriction.G.FD.col P a) = c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := by
    intro a
    have hcolumn : _root_.ReciprocityTheory.ChartRestriction.G.FD.col P a = P *ᵥ Pi.single a 1 := by
      ext i
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec_single_one]
    rw [hcolumn, hv, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]
  have hvv : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v v = ∑ a, c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) * star (c a) := by
    conv_lhs => rw [hv]
    rw [_root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, mul_assoc]
  have hgp : X.gramPos x τ = 1 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos
    rw [← hP, hG]
    ext a b
    simp [Matrix.one_apply, Matrix.diagonal_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have hp : X.p0 ≤ r := X.p0_le
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.posPart
  rw [hgp, hvv]
  simp only [← hP, inv_one, Matrix.one_apply, hcol]
  simp [Finset.sum_ite_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have key : ∀ f : Fin r → ℝ,
      ∑ b : Fin X.p0, f (Fin.castLE hp b) = ∑ a : Fin r, if (a : ℕ) < X.p0 then f a else 0 := by
    intro f
    have hmap := Finset.sum_map Finset.univ (Fin.castLEEmb hp) f
    simp only [Fin.castLEEmb_apply] at hmap
    rw [← Finset.sum_filter, ← hmap]
    congr 1
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.isLt
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
  rw [key fun a => (c a).re * (c a).re + (c a).im * (c a).im, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  split_ifs <;> ring

end GlobalTheory.MajorantOrthFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexIntegralSpanSupermultiplicative
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_mul_le_of_le {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by
  rw [← GlobalTheory.relIndex_sup_mul_relIndex_inf A M₁ _ M₂ _ h₁ h₂, mul_comm, ← inf_inf_distrib_left]
  refine Nat.mul_le_mul_left _ (AddSubgroup.relIndex_le_of_le_right ?_ hne)
  exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)


omit [IsCMField E] in
theorem span_le_inf_span {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
  refine le_inf ?_ ?_
  · have : Submodule.span (𝓞 E) (Set.range w) ≤ Λ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
    exact fun x hx => this hx
  · exact fun x hx => Submodule.span_le_restrictScalars (𝓞 E) E _ hx

theorem relIndex_span_mul_le : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  intro r X α β γ _ _ _ _ _ _ w hw hΛ
  have hw' : LinearIndependent (𝓞 E) w := hw.restrict_scalars' (𝓞 E)
  obtain ⟨i₁, s₁⟩ := GlobalTheory.span_inf_sup_overlapping_parts (𝓞 E) _ α β γ w hw'
  obtain ⟨i₂, s₂⟩ := GlobalTheory.span_inf_sup_overlapping_parts E _ α β γ w hw
  have hne := relIndex_span_ne_zero r X _ w hw hΛ
  rw [← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup] at hne
  have key := relIndex_mul_le_of_le _ _ _ _ _
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)) fun a => hΛ _)
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) fun a => hΛ _) hne
  rw [← i₁, ← i₂, ← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  exact key

end GlobalTheory.SpanIndex
end

