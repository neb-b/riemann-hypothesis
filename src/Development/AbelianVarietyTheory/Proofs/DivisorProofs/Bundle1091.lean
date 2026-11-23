module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.AbsHalfInv

theorem v_det_KGL {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v (k.val.det) = 1 := by
  obtain ⟨y, rfl⟩ := hk
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  obtain ⟨u, hu⟩ := hu
  have hdet : (Formalism.UG.bc (Ov E w).subtype y).val.det = ((u : Ov E w) : w.adicCompletion E) := by
    rw [hu]
    change (y.val.map (Ov E w).subtype).det = _
    exact (RingHom.map_det (Ov E w).subtype y.val).symm
  rw [hdet]
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

theorem v_det_mul_left {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((k * m).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, one_mul]

theorem v_det_mul_right {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((m * k).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, mul_one]

theorem absHalf_congr {E : Type} [Field E] [NumberField E] {w : Pl E} {x y : w.adicCompletion E}
    (h : Valued.v x = Valued.v y) : absHalf w x = absHalf w y := by
  have : ordL x = ordL y := by unfold ordL; simp only [h]
  unfold absHalf
  rw [this]

end GlobalTheory.BCT.AbsHalfInv

open GlobalTheory.BCT.AbsHalfInv in
theorem GlobalTheory.BCT.absHalf_blockDet_KGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  intro E _ _ _ a b w m k h1 h2
  refine ⟨absHalf_congr ?_, absHalf_congr ?_⟩
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_left h1, v_det_mul_left h2]
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_right h1, v_det_mul_right h2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPoint
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem frame_eventually {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}
    (hA : A ∈ E.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtension
section
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine Formalism.BasicNotions

namespace GlobalTheory.FlatLine

section Descent

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']

theorem exp_ne_zero_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) : ε 𝔓 ≠ 0 := by
  intro h0
  have hmem : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k') ∈ 𝔓.asIdeal := Ideal.absNorm_mem _
  have h2 : 𝔓.valuation k' (algebraMap (𝓞 k') k' ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k')) < 1 := by
    rwa [HeightOneSpectrum.valuation_lt_one_iff_mem]
  have h1 := hv 𝔓 (Ideal.absNorm 𝔓.asIdeal : k)
  rw [h0, pow_zero, map_natCast] at h1
  rw [map_natCast, h1] at h2
  exact lt_irrefl _ h2

theorem mem_iff_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) (x : 𝓞 k) :
    x ∈ (π 𝔓).asIdeal ↔ 𝔓.valuation k' (algebraMap k k' (x : k)) < 1 := by
  rw [hv, pow_lt_one_iff (exp_ne_zero_of_valuation_pow hv 𝔓), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k)]

theorem eq_of_valuation_pow {π π' : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε ε' : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (hv' : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π' 𝔓).valuation k z ^ ε' 𝔓) :
    π = π' ∧ ε = ε' := by
  have hπ : π = π' := by
    funext 𝔓
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_iff_of_valuation_pow hv, mem_iff_of_valuation_pow hv']
  refine ⟨hπ, ?_⟩
  funext 𝔓
  obtain ⟨z, hz⟩ := (π 𝔓).valuation_exists_uniformizer k
  have h := (hv 𝔓 z).symm.trans (hv' 𝔓 z)
  rw [← hπ, hz, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

theorem lineDeg_descent : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']
    (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ),
    (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) →
    ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ),
    (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite →
    (Function.support ρ).Finite ∧
      lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  intro k k' _ _ _ _ _ π ε hv r ρ hfin
  classical
  obtain ⟨π₀, ε₀, hv₀, hsum⟩ :=
    GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm k k' (algebraMap k k')
  obtain ⟨hπ, hε'⟩ := eq_of_valuation_pow hv hv₀
  rw [← hπ, ← hε'] at hsum
  choose s hs hne hid using hsum
  have hε : ∀ 𝔓, ε 𝔓 ≠ 0 := exp_ne_zero_of_valuation_pow hv
  have hk : (0 : ℝ) < finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hk' : (0 : ℝ) < finrank ℚ k' := by exact_mod_cast Module.finrank_pos

  have hρ : (Function.support ρ).Finite := by
    refine (hfin.image π).subset ?_
    intro 𝔭 h𝔭
    obtain ⟨𝔓, h𝔓⟩ := hne 𝔭
    have he : π 𝔓 = 𝔭 := (hs 𝔭 𝔓).1 h𝔓
    refine ⟨𝔓, ?_, he⟩
    simp only [Function.mem_support, he]
    exact mul_ne_zero (by exact_mod_cast hε 𝔓) h𝔭
  refine ⟨hρ, ?_⟩

  have harch := GlobalTheory.finrank_mul_sum_embeddings_comp k k' (algebraMap k k') (fun σ => Real.log (r σ))
  have hA : (∑ σ : k' →+* ℂ, Real.log (r (σ.comp (algebraMap k k')))) / (finrank ℚ k' : ℝ)
      = (∑ σ : k →+* ℂ, Real.log (r σ)) / (finrank ℚ k : ℝ) := by
    rw [div_eq_div_iff hk'.ne' hk.ne']
    linarith [harch]

  have hdisj : ((hρ.toFinset : Finset (HeightOneSpectrum (𝓞 k))) : Set (HeightOneSpectrum (𝓞 k))).PairwiseDisjoint s := by
    intro a _ b _ hab
    exact Finset.disjoint_left.2 fun 𝔓 ha hb => hab (((hs a 𝔓).1 ha).symm.trans ((hs b 𝔓).1 hb))
  unfold lineDeg lw
  beta_reduce
  have h1 : Function.support (fun la : HeightOneSpectrum (𝓞 k) =>
      ρ la * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k : ℝ))) ⊆ ↑hρ.toFinset := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
    simp [hx]
  have h2 : Function.support (fun la : HeightOneSpectrum (𝓞 k') =>
      (ε la : ℝ) * ρ (π la) * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k' : ℝ)))
      ⊆ ↑(hρ.toFinset.biUnion s) := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    have h0 : ρ (π x) = 0 := by
      by_contra h
      apply hx
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset,
        Function.mem_support]
      exact ⟨π x, h, (hs _ _).2 rfl⟩
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, hA,
    Finset.sum_biUnion hdisj]
  congr 1
  refine Finset.sum_congr rfl fun 𝔭 _ => ?_
  have e1 : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * ρ (π 𝔓) * (Real.log (Ideal.absNorm 𝔓.asIdeal) / (finrank ℚ k' : ℝ))
      = ρ 𝔭 / (finrank ℚ k' : ℝ) * ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔓 h => ?_
    rw [(hs 𝔭 𝔓).1 h]
    ring
  have hS : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal)
      = (finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) / (finrank ℚ k : ℝ) := by
    rw [eq_div_iff hk.ne']
    linarith [hid 𝔭]
  rw [e1, hS]
  field_simp

end Descent

end GlobalTheory.FlatLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetTraceClassFunction
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap Matrix
open Formalism.REAL (KG toMK)

namespace GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

variable {n : ℕ} {ε : Fin n → Bool}

def physM (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix {x : Fin n × Fin n // IsPhys ε x} {x : Fin n × Fin n // IsPhys ε x} ℂ :=
  fun x y => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)

theorem physM_eq_adMat (k : Matrix (Fin n) (Fin n) ℂ) (x y : {x : Fin n × Fin n // IsPhys ε x}) :
    physM ε k x y = adMat ε k x.1 y.1 := by
  simp [physM, adMat, x.2, y.2]

theorem physM_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) :
    physM ε (a * b) = physM ε a * physM ε b := by
  ext x y
  rw [physM_eq_adMat, adMat_mul ha hb, Matrix.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (IsPhys ε)]
  have h0 : ∑ z : {z : Fin n × Fin n // ¬ IsPhys ε z}, adMat ε a x.1 z * adMat ε b z y.1 = 0 :=
    Finset.sum_eq_zero fun z _ => by simp [adMat, x.2, z.2]
  rw [h0, add_zero]
  simp only [physM_eq_adMat]

theorem physM_one : physM ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  rw [physM_eq_adMat, adMat_one]
  by_cases h : x = y
  · subst h; simp
  · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    simp [h, h']

theorem physDet_eq (k : Matrix (Fin n) (Fin n) ℂ) : physDet ε k = (1 - physM ε k).det := by
  unfold physDet
  congr 1

theorem physDet_conj (k k' : KG ε) : physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) := by
  have ha : toMK k'⁻¹ ∈ Kset ε := (k'⁻¹).2
  have hb : toMK k ∈ Kset ε := k.2
  have hc : toMK k' ∈ Kset ε := k'.2
  have hab : toMK k'⁻¹ * toMK k ∈ Kset ε := (k'⁻¹ * k).2
  have hac : physM ε (toMK k'⁻¹) * physM ε (toMK k') = 1 := by
    rw [← physM_mul ha hc, show toMK k'⁻¹ * toMK k' = toMK (k'⁻¹ * k') from rfl, inv_mul_cancel]
    exact physM_one
  rw [physDet_eq, physDet_eq, show toMK (k'⁻¹ * k * k') = toMK k'⁻¹ * toMK k * toMK k' from rfl,
    physM_mul hab hc, physM_mul ha hb]
  have e : 1 - physM ε (toMK k'⁻¹) * physM ε (toMK k) * physM ε (toMK k') =
      physM ε (toMK k'⁻¹) * (1 - physM ε (toMK k)) * physM ε (toMK k') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hac]
  rw [e, det_mul, det_mul, mul_comm (det (physM ε (toMK k'⁻¹))), mul_assoc, ← det_mul, hac, det_one, mul_one]

theorem trK_conj {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (k k' : KG ε) :
    trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  have hmul : ∀ a b : KG ε, (T (toMK (a * b)) : W →ₗ[ℂ] W) = (T (toMK a) : W →ₗ[ℂ] W) * (T (toMK b)) := by
    intro a b
    rw [show toMK (a * b) = toMK a * toMK b from rfl, hT.1.2 _ a.2 _ b.2]
    rfl
  have h1 : (T (toMK (1 : KG ε)) : W →ₗ[ℂ] W) = 1 := by
    rw [show toMK (1 : KG ε) = 1 from rfl, hT.1.1]
    rfl
  unfold trK
  rw [hmul, hmul, LinearMap.trace_mul_comm, ← mul_assoc, ← hmul k' k'⁻¹, mul_inv_cancel, h1, one_mul]

end GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

namespace GlobalTheory.PsCo.PcEF

theorem adjointDetTrace_classFunction (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε) :
    physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
      ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
        (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
        Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
        trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  refine ⟨PhysicalMatrixDeterminant.physDet_conj k k', ?_⟩
  intro W _ _ _ T hT
  exact PhysicalMatrixDeterminant.trK_conj T hT k k'

end GlobalTheory.PsCo.PcEF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensity
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem aemeasurable_chart_of_locally_continuous {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ} (hS : IsOpen S)
    (h : ∀ y ∈ S, y ∈ e.source →
      ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) :
    AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS
  refine ContinuousOn.aemeasurable (fun v hv => ContinuousAt.continuousWithinAt ?_) hO.measurableSet
  obtain ⟨hvt, hvS⟩ := hv
  obtain ⟨g, hg, hev⟩ := h _ hvS (e.map_target hvt)
  rw [e.right_inv hvt] at hg
  refine hg.congr ?_
  have h1 := (e.continuousAt_symm hvt).eventually hev
  filter_upwards [h1, e.open_target.mem_nhds hvt] with w hw hwt
  rw [hw, e.right_inv hwt]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_twisted_unit_integral : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (exact GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnit
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.AlmostLowUnits

theorem det_almost {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hb : (b : ℕ) = a + 1) (hab : A a b ≠ 0)
    (hl : ∀ i j : Fin n, i < j → ¬ (i = a ∧ j = b) → A i j = 0) :
    A.det = (A a a * A b b - A a b * A b a) * ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_iff_val_lt_val]; omega
  set c := A a a / A a b with hc
  set U := A.updateCol a (fun k => A k a + (-c) • A k b) with hU
  set N := U.submatrix id (Equiv.swap a b) with hN
  have hdetU : U.det = A.det := Matrix.det_updateCol_add_smul_self A hne (-c)
  have hdetN : N.det = - A.det := by
    rw [hN, Matrix.det_permute', Equiv.Perm.sign_swap hne, hdetU]; simp
  have hUapp : ∀ i j, U i j = if j = a then A i a - c * A i b else A i j := by
    intro i j
    rw [hU, Matrix.updateCol_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  have hNapp : ∀ i j, N i j = U i (Equiv.swap a b j) := fun _ _ => rfl
  have htri : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hNapp]
    by_cases hja : j = a
    · rw [hja, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
      rw [hja] at hij'
      exact hl i b (lt_trans hij' hlt) (fun h => (ne_of_lt hij') h.1)
    · by_cases hjb : j = b
      · rw [hjb, Equiv.swap_apply_right, hUapp, if_pos rfl]
        rw [hjb] at hij'
        by_cases hia : i = a
        · rw [hia, hc, div_mul_cancel₀ _ hab, sub_self]
        · have hia' : i < a := by
            have h1 : (i : ℕ) < b := hij'
            have h2 : (i : ℕ) ≠ a := fun h => hia (Fin.ext h)
            rw [Fin.lt_iff_val_lt_val]; omega
          rw [hl i a hia' (fun h => hia h.1), hl i b (lt_trans hia' hlt) (fun h => hia h.1)]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, hUapp, if_neg hja]
        exact hl i j hij' (fun h => hjb h.2)
  have hprod := Matrix.det_of_lowerTriangular N htri
  have hmb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hmb] at hprod
  have hNa : N a a = A a b := by rw [hNapp, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
  have hNb : N b b = A b a - c * A b b := by rw [hNapp, Equiv.swap_apply_right, hUapp, if_pos rfl]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, N i i = ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hib := (Finset.mem_erase.1 hi).1
    have hia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [hNapp, Equiv.swap_apply_of_ne_of_ne hia hib, hUapp, if_neg hia]
  rw [hNa, hNb, hrest, hdetN] at hprod
  have e : A a b * (A b a - c * A b b) = A a b * A b a - A a a * A b b := by
    rw [hc]; field_simp
  rw [← mul_assoc, e] at hprod
  linear_combination (-1 : K) * hprod

theorem units_of_det {K α : Type} [Field K] [DecidableEq α] (O : Subring K) {s : Finset α} (x : α → K) (y d : K)
    (hd : d = y * ∏ i ∈ s, x i) (hd0 : d ≠ 0) (hdi : d⁻¹ ∈ O) (hy : y ∈ O) (hx : ∀ i ∈ s, x i ∈ O) :
    (y ≠ 0 ∧ y⁻¹ ∈ O) ∧ ∀ i ∈ s, x i ≠ 0 ∧ (x i)⁻¹ ∈ O := by
  have hP : ∏ i ∈ s, x i ∈ O := O.prod_mem hx
  rw [hd] at hd0
  refine ⟨⟨left_ne_zero_of_mul hd0, ?_⟩, fun i hi => ?_⟩
  · have e : y⁻¹ = d⁻¹ * ∏ i ∈ s, x i := by
      rw [hd, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul hd0), mul_one]
    rw [e]; exact O.mul_mem hdi hP
  · have e : d = x i * (y * ∏ j ∈ s.erase i, x j) := by
      rw [hd, ← Finset.mul_prod_erase s x hi]; ring
    have h0 : x i * (y * ∏ j ∈ s.erase i, x j) ≠ 0 := by rw [← e, hd]; exact hd0
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have e' : (x i)⁻¹ = d⁻¹ * (y * ∏ j ∈ s.erase i, x j) := by
      rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul h0), mul_one]
    rw [e']
    exact O.mul_mem hdi (O.mul_mem hy (O.prod_mem fun j hj => hx j (Finset.mem_of_mem_erase hj)))

end GlobalTheory.FlagPush.AlmostLowUnits


open GlobalTheory.FlagPush.AlmostLowUnits in
theorem GlobalTheory.FlagPush.almostLow_units : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g →
    (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧
      minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  intro ι m τ a b hb K _ O g hg hp
  have hlτ : ∀ i j : Fin (m τ), i < j → ¬ (i = a ∧ j = b) → g τ i j = 0 := fun i j hij h =>
    hg.2.2 τ i j hij (fun h' => h ⟨eq_of_heq (Sigma.mk.inj h'.1).2, eq_of_heq (Sigma.mk.inj h'.2).2⟩)
  have hdetτ := det_almost (g τ) a b hb hg.2.1 hlτ
  have hmO : minor τ a b g ∈ O :=
    O.sub_mem (O.mul_mem ((hp τ).1 a a) ((hp τ).1 b b)) (O.mul_mem ((hp τ).1 a b) ((hp τ).1 b a))
  have hτ := units_of_det O (fun i => g τ i i) (minor τ a b g) ((g τ).det) hdetτ (hp τ).2.1 (hp τ).2.2.1 hmO
    (fun i _ => (hp τ).1 i i)
  refine ⟨?_, hτ.1⟩
  rintro ⟨σ, i⟩ h1 h2
  by_cases hσ : σ = τ
  · subst hσ
    have hia : i ≠ a := fun e => h1 (by rw [e])
    have hib : i ≠ b := fun e => h2 (by rw [e])
    exact hτ.2 i (Finset.mem_erase.2 ⟨hib, Finset.mem_erase.2 ⟨hia, Finset.mem_univ _⟩⟩)
  · have htri : (g σ).BlockTriangular OrderDual.toDual := fun i j hij =>
      hg.2.2 σ i j (OrderDual.toDual_lt_toDual.1 hij) (fun h' => hσ (congrArg Sigma.fst h'.1))
    have hdet := Matrix.det_of_lowerTriangular (g σ) htri
    have h := units_of_det O (s := Finset.univ) (fun j => g σ j j) 1 ((g σ).det) (by rw [one_mul]; exact hdet)
      (hp σ).2.1 (hp σ).2.2.1 O.one_mem (fun j _ => (hp σ).1 j j)
    exact h.2 i (Finset.mem_univ _)
end

