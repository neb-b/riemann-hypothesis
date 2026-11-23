module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0017
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.DivByPartialYAtZeroSubstAtXAtY

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixJ_nonunits_add {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : a ∈ A.nonunits)
    (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  exact add_mem ha hb

def fixJRoots {Ω : Type*} [Field Ω] (P : Polynomial ℤ) : Finset Ω := (P.map (Int.castRingHom Ω)).roots.toFinset

theorem mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) (r : Ω) :
    r ∈ fixJRoots (Ω := Ω) P ↔ P.eval₂ (Int.castRingHom Ω) r = 0 := by
  rw [fixJRoots, Multiset.mem_toFinset, Polynomial.mem_roots (hP.map _).ne_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map]

theorem map_mem_fixJRoots {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic)
    (g : Ω ≃ₐ[E] Ω) {r : Ω} (hr : r ∈ fixJRoots (Ω := Ω) P) : g r ∈ fixJRoots (Ω := Ω) P := by
  rw [mem_fixJRoots hP] at hr ⊢
  have h := Polynomial.hom_eval₂ P (Int.castRingHom Ω) (g : Ω →+* Ω) r
  rw [hr, map_zero, RingHom.ext_int ((g : Ω →+* Ω).comp (Int.castRingHom Ω)) (Int.castRingHom Ω)] at h
  exact h.symm

theorem isIntegral_of_mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) {r : Ω}
    (hr : r ∈ fixJRoots (Ω := Ω) P) : IsIntegral ℤ r := by
  refine ⟨P, hP, ?_⟩
  rw [algebraMap_int_eq]
  exact (mem_fixJRoots hP r).1 hr

def fixJStab (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω] (P : Polynomial ℤ) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {g | ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb r hr
    rw [AlgEquiv.mul_apply, hb r hr, ha r hr]
  inv_mem' := by
    intro a ha r hr
    have := ha r hr
    calc a⁻¹ r = a⁻¹ (a r) := by rw [this]
      _ = r := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

theorem mem_fixJStab {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} {g : Ω ≃ₐ[E] Ω} :
    g ∈ fixJStab E Ω P ↔ ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r := Iff.rfl

theorem fixJStab_normal {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic) :
    (fixJStab E Ω P).Normal := by
  constructor
  intro n hn g
  rw [mem_fixJStab] at hn ⊢
  intro r hr
  have h1 : g⁻¹ r ∈ fixJRoots (Ω := Ω) P := map_mem_fixJRoots hP g⁻¹ hr
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem fixJStab_isOpen {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    {P : Polynomial ℤ} : IsOpen (fixJStab E Ω P : Set (Ω ≃ₐ[E] Ω)) := by
  let K : IntermediateField E Ω := IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)
  haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
  intro g hg
  rw [mem_fixJStab]
  intro r hr
  exact hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocA
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixed_mem_Kur {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hK : FiniteDimensional ℚ_[l] K) (y : PadicAlgCl l)
    (h : ∀ ρ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, (∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) → ρ y = y) :
    y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l K := by
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_iff_fixed (ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (p := l) (K := K)) y]
  intro σ hσ
  exact h σ ((ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff hK σ).1 hσ)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def redSqD (d : ℕ) : ℂ := 2 * omegaK d - 1

def IsHalfReps (L : PeriodPair) (α : ℂ) (T : Finset ℂ) : Prop :=
  (∀ P ∈ T, α * P ∈ L.lattice ∧ 2 * P ∉ L.lattice) ∧
  (∀ P ∈ T, ∀ Q ∈ T, (P - Q ∈ L.lattice ∨ P + Q ∈ L.lattice) → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ T, z - P ∈ L.lattice ∨ z + P ∈ L.lattice)

def xsOf (L : PeriodPair) (T : Finset ℂ) : Finset ℂ := T.image L.weierstrassP

section Alg

variable {K : Type} [Field K]

def rootPoly (xs : Finset K) : K[X] := ∏ x ∈ xs, (X - C x)

def fW (g2 g3 x : K) : K := 4 * x ^ 3 - g2 * x - g3

def fW' (g2 x : K) : K := 12 * x ^ 2 - g2

def veluFun (g2 g3 : K) (xs : Finset K) (t : K) : K :=
  t + ∑ x ∈ xs, (fW g2 g3 x / (t - x) ^ 2 + fW' g2 x / (2 * (t - x)))

def veluNum [DecidableEq K] (g2 g3 : K) (xs : Finset K) : K[X] :=
  X * rootPoly xs ^ 2
    + ∑ x ∈ xs, (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x)) * rootPoly (xs.erase x) ^ 2

def homS (U : PowerSeries K) (m : ℕ) (Q : K[X]) : PowerSeries K :=
  ∑ i ∈ Finset.range (m + 1), PowerSeries.C (Q.coeff i) * U ^ i * PowerSeries.X ^ (2 * (m - i))

end Alg

def KerProdAt (d : ℕ) (L : PeriodPair) (l e : ℕ) : Prop :=
  ∃ (N : ℕ) (T : Finset ℂ), ¬ l ∣ N ∧ ¬ e ∣ N ∧ ¬ e ∣ T.card ∧
    (∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) ∧
    ∀ k : Subfield ℂ, L.g₂ ∈ k → L.g₃ ∈ k → omegaK d ∈ k → ∏ z ∈ T, L.weierstrassP z ∈ k

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SubstOfLog
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb : MvPowerSeries.HasSubst ![atX e, atY e] := Formalism.G.LogP.hs2 hx0 hy0
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (![atX e, atY e] i) = 0 := by
    intro i; fin_cases i <;> simpa
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb hb0 h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes (hX 0), ← PowerSeries.subst_comp_subst_apply hes (hX 1),
    hlog', PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1), smul_add]

theorem LawD.comm_of_log (h : LawD lam Φ) {e f : PowerSeries K} {c d : K}
    (he0 : constantCoeff e = 0) (hf0 : constantCoeff f = 0)
    (hlog : lam.subst e = C c * lam) (hlogf : lam.subst f = C d * lam) :
    e.subst f = f.subst e := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hlogf' : lam.subst f = d • lam := by rw [hlogf, smul_eq_C_mul]
  refine Formalism.G.LogP.psubst_injective (σ := Unit) h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero hf0 _ he0)
    (PowerSeries.constantCoeff_subst_eq_zero he0 _ hf0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hfs, ← PowerSeries.subst_comp_subst_apply hfs hes,
    hlog', hlogf', PowerSeries.subst_smul hfs, PowerSeries.subst_smul hes, hlog', hlogf',
    smul_smul, smul_smul, mul_comm]

theorem mulL_homCls (h : HD σ lam Φ A a) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) : HomCls l Φ A Φ A e := by
  refine ⟨he0, he, ?_, ?_⟩
  · rw [h.toLawD.subst_of_log he0 hlog, sub_self]
    exact divByMv_zero _
  · rw [h.toLawD.comm_of_log he0 h.A0 hlog h.Alog, sub_self]
    intro n
    simp

theorem mulL_deriv (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) (derivative e) := by
  have hconst : constantCoeff (derivative lam) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp [h.lam1]
  have hmul : derivative lam * d2 Φ = 1 := by
    have hchain : d2 (lam.subst Φ) = derivative lam * d2 Φ := by
      rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst h.Φ0, evalYZero_mul,
        evalYZero_subst _ h.Φ0, h.evalYZero_eq, PowerSeries.X_subst, ← partialYAtZero_eq]
    have hlogD := congrArg d2 h.log
    rwa [hchain, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY,
      h.lam1, zero_add, map_one] at hlogD
  have hunit : constantCoeff (d2 Φ) = 1 := by
    have hcoeff := congrArg constantCoeff hmul
    rwa [map_mul, hconst, one_mul, map_one] at hcoeff
  have hIntegral : IntegralPS (derivative lam) := by
    rw [integralPS_iff_divBy_one]
    refine divBy_of_mul_unit (integralPS_partialYAtZero h.Φint) (by rw [hunit, norm_one]) ?_
    rw [mul_comm, hmul]
    intro n
    by_cases hn : n = 0 <;> simp [coeff_one, hn]
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : (derivative lam).subst e * derivative e = C (l : K) * derivative lam := by
    rw [← PowerSeries.derivative_subst hes, hlog]
    simp
  have hi : IntegralPS ((derivative lam).subst e) :=
    (integralPS_iff_mv _).2 (integralMv_subst hIntegral he0 ((integralPS_iff_mv _).1 he))
  have hc : constantCoeff ((derivative lam).subst e) = 1 := by
    exact (PowerSeries.constantCoeff_subst_of_constantCoeff_zero he0 (derivative lam)).trans hconst
  refine divBy_of_mul_unit hi (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hIntegral n)

theorem hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh : PowerSeries K,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have descend {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
      (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0) (hΦ₁ : IntegralMv Φ₁)
      (hΦ₂ : IntegralMv Φ₂) (hA₁0 : constantCoeff A₁ = 0)
      (hA₁ : IntegralPS A₁) (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g)
      (hg' : DivBy (l : K) (derivative g)) :
      DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
        HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by
    have hc : DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) := by
      intro m
      rw [map_sub, PowerSeries.coeff_subst_X_pow hl0, Algebra.algebraMap_self, RingHom.id_apply]
      split_ifs with hm
      · obtain ⟨q, rfl⟩ := hm
        rw [desc, coeff_mk, Nat.mul_div_cancel_left q hF.prime.pos, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [sub_zero]
        have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero l)
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        have h := hg' n
        rwa [coeff_derivative, norm_mul, ← Nat.cast_add_one,
          norm_natCast_of_coprime hF.prime hF.norm_l _ hm, mul_one] at h
    refine ⟨hc, ?_⟩
    have hg₁0 : constantCoeff (desc l g) = 0 := by rw [desc_const, hg.g0]
    have hg₁ : IntegralPS (desc l g) := desc_integral hg.gInt
    generalize desc l g = g₁ at hc hg₁0 hg₁ ⊢
    obtain ⟨E, hE⟩ : ∃ E : PowerSeries K, E = g₁.subst ((X : PowerSeries K) ^ l) := ⟨_, rfl⟩
    have hE0 : constantCoeff E = 0 := by
      rw [hE]
      refine PowerSeries.constantCoeff_subst_eq_zero ?_ g₁ hg₁0
      rw [map_pow]
      exact (congrArg (· ^ l) (constantCoeff_X (R := K))).trans (zero_pow hl0)
    have hEint : IntegralPS E := by
      rw [hE]
      exact (integralPS_iff_divBy_one _).2 ((divBy_expand_iff 1 l hl0 g₁).2
        ((integralPS_iff_divBy_one _).1 hg₁))
    have hc' : DivBy (l : K) (g - E) := by rw [hE]; exact hc
    refine ⟨hg₁0, hg₁, ?_, ?_⟩
    · rw [← divByMv_expand_iff (l : K) l hl0, map_sub]
      have T := homE_expand_subst_map_congr hF hg₁ hc Φ₁ hΦ₁0 hΦ₁
      have hv : MvPowerSeries.HasSubst ![atX g₁, atY g₁] :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero (homE_vec_const hg₁0)
      have hex : MvPowerSeries.expand l hl0 (Φ₂.subst ![atX g₁, atY g₁]) =
          Φ₂.subst ![atX E, atY E] := by
        rw [MvPowerSeries.expand_subst l hl0 hv]
        congr 1
        funext i
        fin_cases i
        · show MvPowerSeries.expand l hl0 (atX g₁) = atX E
          rw [atX, atX, homE_expand_subst_X hl0, hE]
        · show MvPowerSeries.expand l hl0 (atY g₁) = atY E
          rw [atY, atY, homE_expand_subst_X hl0, hE]
      have T5 : DivByMv (l : K) (Φ₂.subst ![atX g, atY g] - Φ₂.subst ![atX E, atY E]) :=
        divByMv_subst2_congr hF.norm_l.le hΦ₂ (homE_vec_const hg.g0) (homE_vec_const hE0)
          (homE_vec_integral hg.gInt) (homE_vec_integral hEint) (homE_vec_divBy hc')
      rw [hex]
      have := divByMv_add (divByMv_add T hg.add) T5
      rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
    · rw [divBy_iff_mv, ← divByMv_expand_iff (l : K) l hl0, map_sub]
      have T := homE_expand_subst_map_congr (ι := Unit) hF hg₁ hc A₁ hA₁0 ((integralPS_iff_mv _).1 hA₁)
      have hex : MvPowerSeries.expand l hl0 (A₂.subst g₁) = A₂.subst E := by
        rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero' hg₁0), hE]
        congr 1
        exact PowerSeries.expand_apply l hl0 g₁
      have T5 : DivByMv (l : K) (A₂.subst g - A₂.subst E) :=
        divByMv_subst_congr (ι := Unit) hF.norm_l.le hA₂ hg.g0 hE0 ((integralPS_iff_mv _).1 hg.gInt)
          ((integralPS_iff_mv _).1 hEint) ((divBy_iff_mv _ _).1 hc')
      rw [hex]
      have := divByMv_add (divByMv_add T ((divBy_iff_mv _ _).1 hg.eig)) T5
      rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have hσ := h.map hF
  obtain ⟨hc1, hH1⟩ := descend h.Φ0 h.Φint h.Φint h.A0 h.Aint h.Aint
    (mulL_homCls h he0 he hlog) (mulL_deriv h.toLawD he0 he hlog)
  have hsmall : ‖coeff 1 (desc l e)‖ ≤ ‖(l : K)‖ := by
    refine hom_eigen hσ.A0 h.A0 hH1 ?_
    rw [hσ.coeff_one_A, h.coeff_one_A]
    exact h.a_ne
  have hd1 : DivBy (l : K) (derivative (desc l e)) := by
    let Φσ := MvPowerSeries.map σ Φ
    have hchain (D : PowerSeries K) : d2 (D.subst Φσ) = derivative D * d2 Φσ := by
      rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hσ.Φ0, evalYZero_mul,
        evalYZero_subst _ hσ.Φ0, hσ.toLawD.evalYZero_eq, PowerSeries.X_subst, ← partialYAtZero_eq]
    have hadd := divBy_partialYAtZero hH1.add
    rw [partialYAtZero_sub, hchain] at hadd
    have hsubst := divBy_partialYAtZero_subst_atX_atY h.Φint hH1.g0 hH1.gInt hsmall
    have hprod : DivBy (l : K) (derivative (desc l e) * d2 Φσ) := by
      simpa only [sub_add_cancel] using divBy_add hadd hsubst
    have hmul : derivative (PowerSeries.map σ lam) * d2 Φσ = 1 := by
      have hlogD := congrArg d2 hσ.log
      rwa [hchain, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY,
        hσ.lam1, zero_add, map_one] at hlogD
    have hconst : constantCoeff (derivative (PowerSeries.map σ lam)) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
      simp [hσ.lam1]
    have hunit : constantCoeff (d2 Φσ) = 1 := by
      have hcoeff := congrArg constantCoeff hmul
      rwa [map_mul, hconst, one_mul, map_one] at hcoeff
    exact divBy_of_mul_unit (integralPS_partialYAtZero hσ.Φint) (by rw [hunit, norm_one])
      (by rwa [mul_comm])
  obtain ⟨hc2, hH2⟩ := descend hσ.Φ0 hσ.Φint h.Φint hσ.A0 hσ.Aint h.Aint hH1 hd1
  refine ⟨desc l (desc l e), ?_, ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]
    exact hH2
  · have hXs : PowerSeries.HasSubst ((X : PowerSeries K) ^ l) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have h3 := (divBy_expand_iff (l : K) l hl0 _).2 hc2
    rw [PowerSeries.subst_sub hXs, PowerSeries.subst_comp_subst_apply hXs hXs,
      PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs, ← pow_mul, ← sq] at h3
    have h4 := divBy_add hc1 h3
    rwa [sub_add_sub_cancel] at h4
  · rw [coeff_one_desc, desc, coeff_mk, sq]

theorem hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by
  obtain ⟨hh, -, hc, -⟩ := hon_shape hF h he0 he hlog
  obtain ⟨i, hi, hi1⟩ := hlev
  have hq0 : l ^ 2 ≠ 0 := pow_ne_zero _ hF.prime.ne_zero
  by_cases hdvd : l ^ 2 ∣ i
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [coeff_zero_eq_constantCoeff_apply, he0, norm_zero] at hi1
      exact absurd hi1 zero_ne_one
    · rw [← le_antisymm hi (Nat.le_of_dvd hpos hdvd)]
      exact hi1
  · have h1 := hc i
    rw [map_sub, coeff_subst_X_pow hq0, if_neg hdvd, sub_zero, hi1] at h1
    exact absurd h1 (not_le.2 hF.norm_l)

end ReciprocityTheory.ChartRestriction.L1
end
end

