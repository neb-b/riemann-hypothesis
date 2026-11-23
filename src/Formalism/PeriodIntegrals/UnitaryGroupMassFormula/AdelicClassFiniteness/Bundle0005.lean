module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSmulRight

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
section
namespace PIW.AdelClassFin

theorem lattice_intersection' : LInter := lInter_of dual_intersection
theorem lattice_denominator : LDenom := lDenom_of dual_denominator
theorem lattice_dense : LDense := lDense_of dual_dense
theorem dual_hat_lattice : LHatDual := lHatDual_of dual_intersection lattice_denominator lattice_dense dual_hat_integral
theorem lattice_m_is_lattice : MLat := mLat_of lattice_intersection' lattice_denominator
theorem lattice_m_generation : MGen := mGen_of lattice_denominator lattice_dense
theorem lattice_m_dual : MDual := mDual_of dual_intersection dual_hat_integral dual_hat_lattice lattice_m_generation
theorem lattice_map_injective : MInj := mInj_of lattice_m_generation

theorem stDict : StDict := stDict_of lattice_m_is_lattice lattice_m_dual lattice_map_injective lattice_m_equiv

end PIW.AdelClassFin
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpComp
section
noncomputable section

namespace PIW.AdelClassFin

open scoped Matrix

theorem spComp : SpComp := by
  intro E _ k m P R hPR
  have hsurj : Function.Surjective (Matrix.toLin' P) := fun v =>
    ⟨R *ᵥ v, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
  have hrank : Module.finrank E (LinearMap.range (Matrix.toLin' P)) = k := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  rw [hrank, Module.finrank_fin_fun] at hsum
  have hker : Module.finrank E (LinearMap.ker (Matrix.toLin' P)) = m - k := by omega
  refine ⟨by omega, ?_⟩
  let b : Module.Basis (Fin (m - k)) E (LinearMap.ker (Matrix.toLin' P)) := Module.finBasisOfFinrankEq E _ hker
  have hU : ∀ y : Fin (m - k) → E,
      (Matrix.of fun i j => (b j : Fin m → E) i) *ᵥ y =
        ((b.equivFun.symm y : LinearMap.ker (Matrix.toLin' P)) : Fin m → E) := by
    intro y
    ext i
    rw [Module.Basis.equivFun_symm_apply]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Matrix.of fun i j => (b j : Fin m → E) i, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (LinearMap.mem_ker.mp (b j).2) i
    rw [Matrix.toLin'_apply] at h
    exact h
  · intro y y' h
    simp only [hU] at h
    exact b.equivFun.symm.injective (Subtype.ext h)
  · intro w hw
    refine ⟨b.equivFun ⟨w, LinearMap.mem_ker.mpr (by rw [Matrix.toLin'_apply]; exact hw)⟩, ?_⟩
    rw [hU, LinearEquiv.symm_apply_apply]

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpDen
section
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem spDen : SpDen := by
  intro E _ _ k X
  have h : ∀ p : Fin k × Fin k, ∃ D : ℕ, 1 ≤ D ∧ (D : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range := by
    intro p
    obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (X p.1 p.2)))
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    have hmem : (y : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range :=
      ⟨⟨(y : E) * X p.1 p.2, by rw [mem_integralClosure_iff]; simpa [zsmul_eq_mul] using hint⟩, rfl⟩
    have h2 : (y.natAbs : ℤ) = y ∨ (y.natAbs : ℤ) = -y := by
      rcases Int.natAbs_eq y with h | h
      · exact Or.inl h.symm
      · right; linarith
    rw [← Int.cast_natCast]
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hmem
    · rw [Int.cast_neg, neg_mul]; exact neg_mem hmem
  choose Dp hDp1 hDp using h
  refine ⟨∏ p, Dp p, Finset.one_le_prod' fun p _ => hDp1 p, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Dp (Finset.mem_univ (i, j))
  rw [hc, Nat.cast_mul, mul_comm (Dp (i, j) : E), mul_assoc]
  exact Subring.mul_mem _ ⟨c, by simp⟩ (hDp (i, j))

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SplHformZero
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

theorem spl_ker {E : Type} [Field E] [StarRing E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E)
    (hΓ : (cT (starRingEnd E) V * J * V).det ≠ 0) (w : Fin m → E) :
    (cT (starRingEnd E) V * J) *ᵥ (w - V *ᵥ ((cT (starRingEnd E) V * J * V)⁻¹ *ᵥ
      ((cT (starRingEnd E) V * J) *ᵥ w))) = 0 := by
  simp [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]

theorem spl_cross {E : Type} [Field E] [StarRing E] {m k n : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E) (h : cT (starRingEnd E) V * J * U = 0)
    (c : Fin k → E) (w : Fin n → E) : hform (starRingEnd E) J (V *ᵥ c) (U *ᵥ w) = 0 := by
  have e1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (fun i => starRingEnd E ((V *ᵥ c) i)) =
      (V.map (starRingEnd E)) *ᵥ (fun k => starRingEnd E (c k)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  have h' : (V.map (starRingEnd E))ᵀ * J * U = 0 := h
  rw [e1, e2, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h', Matrix.zero_mulVec, dotProduct_zero]

theorem spLat : SpLat := by
  intro E _ _ _ m k n d D J M V U hp hV hD hΓ hΓD hVJU hU hsurj
  obtain ⟨hH, hdet, hfg, hsp, hint, hdual⟩ := hp
  have hD0 : (D : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hR : ∀ x ∈ M, ∀ c : E, c ∈ (algebraMap (𝓞 E) E).range → c • x ∈ M := by
    rintro x hx c ⟨a, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem a hx
  have hVc : ∀ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) → V *ᵥ c ∈ M := by
    intro c hc
    have e : V *ᵥ c = ∑ i, c i • (fun r => V r i) := by
      ext r
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => hR _ (hV i) _ (hc i)
  have dec : ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E,
      U *ᵥ y ∈ M ∧ (D : E) • z = V *ᵥ c + U *ᵥ y := by
    intro z hz
    set c := (cT (starRingEnd E) V * J * V)⁻¹ *ᵥ ((cT (starRingEnd E) V * J) *ᵥ ((D : E) • z)) with hc
    have hci : ∀ i, c i ∈ (algebraMap (𝓞 E) E).range := by
      intro i
      have hg : ∀ j, ((cT (starRingEnd E) V * J) *ᵥ z) j ∈ (algebraMap (𝓞 E) E).range := fun j => by
        rw [cT_mulVec_apply]
        exact hint _ (hV j) _ hz
      rw [hc, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      generalize (cT (starRingEnd E) V * J) *ᵥ z = g at hg ⊢
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [← mul_assoc]
      exact Subring.mul_mem _ (hΓD i j) (hg j)
    obtain ⟨y, hy⟩ := hsurj _ (spl_ker J V hΓ ((D : E) • z))
    have hDz : (D : E) • z ∈ M := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hz D
    refine ⟨c, hci, y, ?_, ?_⟩
    · rw [hy]
      exact M.sub_mem hDz (hVc c hci)
    · rw [hy]
      abel
  have hsplit : ∀ w : Fin m → E, ∃ c, ∃ y, w = V *ᵥ c + U *ᵥ y := by
    intro w
    obtain ⟨y, hy⟩ := hsurj _ (spl_ker J V hΓ w)
    exact ⟨_, y, by rw [hy]; abel⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, dec⟩
  ·
    have hcc : cT (starRingEnd E) (cT (starRingEnd E) U) = U := by
      ext i j
      simp [cT]
    unfold IsHerm at hH ⊢
    rw [cT_mul, cT_mul, hH, hcc, Matrix.mul_assoc]
  ·
    intro h0
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have orth : ∀ w, hform (starRingEnd E) J w (U *ᵥ a) = 0 := by
      intro w
      obtain ⟨c, y, rfl⟩ := hsplit w
      rw [hform_add_left, spl_cross J V U hVJU, zero_add, hform_mulVec, hform_eq, ha, dotProduct_zero]
    have hJa : J *ᵥ (U *ᵥ a) = 0 := by
      ext i
      rw [← hform_single_left]
      exact orth _
    have hUa : U *ᵥ a = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hJa⟩)
    exact ha0 (hU (by rw [hUa, Matrix.mulVec_zero]))
  ·
    refine Submodule.fg_of_fg_map_injective (f := (Matrix.mulVecLin U).restrictScalars (𝓞 E))
      (fun a b h => hU h) ?_
    exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  ·
    set W : Submodule E (Fin m → E) := LinearMap.range (Matrix.mulVecLin V) ⊔
      (Submodule.span E (M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E)) : Set (Fin n → E))).map
        (Matrix.mulVecLin U) with hW
    have hMW : Submodule.span E (M : Set (Fin m → E)) ≤ W := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨c, -, y, hyM, hz'⟩ := dec z hz
      refine Submodule.mem_sup.mpr ⟨V *ᵥ ((D : E)⁻¹ • c), ⟨_, rfl⟩, U *ᵥ ((D : E)⁻¹ • y),
        Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (Submodule.subset_span hyM)), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← hz', smul_smul, inv_mul_cancel₀ hD0, one_smul]
    rw [hsp, top_le_iff] at hMW
    rw [Submodule.eq_top_iff']
    intro y0
    have h0 : U *ᵥ y0 ∈ W := by rw [hMW]; exact Submodule.mem_top
    obtain ⟨a, ⟨c, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp h0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    simp only [Matrix.mulVecLin_apply] at hab
    have hP : ∀ v, (cT (starRingEnd E) V * J) *ᵥ (U *ᵥ v) = 0 := fun v => by
      rw [Matrix.mulVec_mulVec, hVJU, Matrix.zero_mulVec]
    have hc0 : c = 0 := by
      have e1 : (cT (starRingEnd E) V * J * V) *ᵥ c = 0 := by
        have := congrArg (fun v => (cT (starRingEnd E) V * J) *ᵥ v) hab
        simp only [Matrix.mulVec_add, hP, add_zero, Matrix.mulVec_mulVec] at this
        exact this
      have := congrArg (fun v => (cT (starRingEnd E) V * J * V)⁻¹ *ᵥ v) e1
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΓ)] using this
    rw [hc0, Matrix.mulVec_zero, zero_add] at hab
    have : y = y0 := hU hab
    rw [← this]
    exact hy
  ·
    intro x hx y hy
    rw [← hform_mulVec]
    exact hint _ hx _ hy
  ·
    intro w hw
    have h1 : (d : E) • ((D : E) • (U *ᵥ w)) ∈ M := by
      refine hdual _ fun z hz => ?_
      obtain ⟨c, -, y, hyM, hz'⟩ := dec z hz
      have e : hform (starRingEnd E) J z ((D : E) • (U *ᵥ w)) =
          hform (starRingEnd E) J ((D : E) • z) (U *ᵥ w) := by
        have h1 := hform_smul J 1 (D : E) z (U *ᵥ w)
        have h2 := hform_smul J (D : E) 1 z (U *ᵥ w)
        rw [one_smul] at h1 h2
        rw [h1, h2, star_one, star_natCast]
        ring
      rw [e, hz', hform_add_left, spl_cross J V U hVJU, zero_add, hform_mulVec]
      exact hw y hyM
    show U *ᵥ (((d * D : ℕ) : E) • w) ∈ M
    rw [Nat.cast_mul, mul_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact h1

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StHOfOpen
section
namespace PIW.AdelClassFin

theorem stH_of_open (hO : SpOne) (hI : IdealBoundAll) (h1 : SvMajE) (h2 : SvCodiff) (h3 : SvBasis) (h4 : SvGramDet)
    (h5 : SvReal) : StH :=
  stH_of_parts (partShort_of partMink h1 h2 h3 h4 h5) partUnits (partIso_of hI) (partSplit_of_one hO)

end PIW.AdelClassFin
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorBasis
section
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_basis : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

end PIW.AdelClassFin

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorCodifferent
section
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_codifferent : SvCodiff := by
  intro E _ _
  refine ⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩
  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy a'
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E)
    (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem
  rw [← NumberField.coe_discr] at hint
  have hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y) := by
    convert hint using 1
    rw [Algebra.smul_def, mul_one, map_intCast]
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs := ⟨_, rfl⟩
  rw [← hn]
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · rw [← hn] at h
    refine ⟨z, ?_⟩
    rw [hz, h, Int.cast_natCast]
  · rw [← hn] at h
    refine ⟨-z, ?_⟩
    rw [map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]

end PIW.AdelClassFin

end
end

