module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.DiagOfCong
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

private theorem cong_roots {K : Type} [NormedField K] [IsUltrametricDist K] {N : ℕ} (hN : ‖(N : K)‖ = 1)
    (s t : Multiset K) (hs : ∀ a ∈ s, a ^ N = 1) (ht : ∀ a ∈ t, a ^ N = 1)
    (h : ∀ k, ‖((s.map fun a => X - C a).prod).coeff k - ((t.map fun a => X - C a).prod).coeff k‖ < 1) : s = t := by
  let O : ValuationSubring K := (NormedField.valuation (K := K)).valuationSubring
  have hm : ∀ a : O, residue O a = 0 ↔ ‖(a : K)‖ < 1 := fun a => by
    rw [residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact Iff.rfl
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  let T := {a : O // a ^ N = 1}
  have lift : ∀ s : Multiset K, (∀ a ∈ s, a ^ N = 1) → ∃ s' : Multiset T, s = s'.map fun a => (a.1 : K) := fun s hs =>
    ⟨s.attach.map fun a => ⟨⟨a.1, show ‖a.1‖₊ ≤ 1 from
      ((pow_eq_one_iff_left hN0).1 (by rw [← nnnorm_pow, hs _ a.2, nnnorm_one])).le⟩, Subtype.ext (hs _ a.2)⟩, by
        simp [Multiset.map_map]⟩
  obtain ⟨s, rfl⟩ := lift s hs
  obtain ⟨t, rfl⟩ := lift t ht
  have inj : Function.Injective fun a : T => residue O a.1 := by
    intro a b hab
    have hab : residue O a.1 = residue O b.1 := hab
    have h1 := Commute.geom_sum₂_mul (Commute.all a.1 b.1) N
    rw [a.2, b.2, sub_self, mul_eq_zero] at h1
    refine Subtype.ext (sub_eq_zero.1 (h1.resolve_left fun h2 => ?_))
    have h3 := congrArg (residue O) h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hab, map_zero] at h3
    rw [geom_sum₂_self, mul_eq_zero] at h3
    rcases h3 with h3 | h3
    · rw [← map_natCast (residue O), hm] at h3
      simp [hN] at h3
    · have h4 := congrArg (residue O) b.2
      rw [map_pow, eq_zero_of_pow_eq_zero h3, zero_pow hN0, map_one] at h4
      exact zero_ne_one h4
  have e : ∀ s : Multiset T, ((s.map fun a => (a.1 : K)).map fun a => X - C a).prod =
      ((s.map fun a : T => X - C a.1).prod).map O.subtype := fun s => by
    simp [Polynomial.map_multiset_prod, Multiset.map_map]
  have e' : ∀ s : Multiset T, ((s.map fun a : T => X - C a.1).prod).map (residue O) =
      ((s.map fun a => residue O a.1).map fun a => X - C a).prod := fun s => by
    simp [Polynomial.map_multiset_prod, Multiset.map_map]
  have h5 : ((s.map fun a : T => X - C a.1).prod).map (residue O) = ((t.map fun a : T => X - C a.1).prod).map (residue O) := by
    ext k
    have := h k
    rw [e, e, coeff_map, coeff_map, ← map_sub] at this
    rw [coeff_map, coeff_map, ← sub_eq_zero, ← map_sub, hm]
    exact this
  have h6 := congrArg Polynomial.roots h5
  rw [e', e', roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h6
  rw [Multiset.map_injective inj h6]

private theorem fin_range {Γ K H : Type} [Group Γ] [Field K] [Group H] {n N : ℕ} (hN : N ≠ 0) (t : Fin n → Γ →* Kˣ)
    (ht : ∀ i g, t i g ^ N = 1) (ρ : Γ →* H) (hρ : ∀ g, (∀ i, t i g = 1) → ρ g = 1) : (Set.range ρ).Finite := by
  haveI : NeZero N := ⟨hN⟩
  let T : Γ → Fin n → rootsOfUnity N K := fun g i => ⟨t i g, ht i g⟩
  refine (Set.finite_range fun z => ρ (Function.invFun T z)).subset ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨T g, ?_⟩
  have h1 : T (Function.invFun T (T g)) = T g := Function.invFun_eq ⟨g, rfl⟩
  have h2 := hρ (Function.invFun T (T g) * g⁻¹) fun i => by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact congrArg Subtype.val (congrFun h1 i)
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem diag_of_cong {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n N : ℕ} (hN : ‖(N : Qbar l)‖ = 1)
    (t : Fin n → Γ →* (Qbar l)ˣ) (ht : ∀ i g, t i g ^ N = 1) (ρ : Γ →* GL (Fin n) (Qbar l))
    (hρ : ∀ g, (∀ i, t i g = 1) → ρ g = 1)
    (h : ∀ g k, ‖(ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff k - (∏ i, (X - C (t i g : Qbar l))).coeff k‖ < 1) :
    ∃ P : GL (Fin n) (Qbar l), ∀ g, ((P * ρ g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (t i g : Qbar l) := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  let δ : Γ →* GL (Fin n) (Qbar l) := (W.diagRep t).toHomUnits
  have hδ : ∀ g, (δ g : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (t i g : Qbar l) := fun g => rfl
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ δ (Formalism.MainNotions.SumRepresentations.isSSRep_of_finite ρ (fin_range hN0 t ht ρ hρ))
    (Formalism.MainNotions.SumRepresentations.isSSRep_of_finite δ (fin_range hN0 t ht δ fun g hg => Units.ext (by simp [hδ, hg]))) fun g => by
      rw [hδ, Matrix.charpoly_diagonal]
      have hs := (IsAlgClosed.splits (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).eq_prod_roots_of_monic
        (Matrix.charpoly_monic _)
      have e : ∏ i, (X - C (t i g : Qbar l)) = ((Finset.univ.val.map fun i => (t i g : Qbar l)).map fun a => X - C a).prod := by
        rw [Multiset.map_map]; rfl
      refine hs.trans (e ▸ congrArg (fun s : Multiset (Qbar l) => (s.map fun a => X - C a).prod)
        (cong_roots hN _ _ (fun a ha => ?_) (fun a ha => ?_) fun k => by rw [← e, ← hs]; exact h g k))
      · have h1 := spectrum.pow_mem_pow _ N (Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots ha))
        rw [← Units.val_pow_eq_pow_val, ← map_pow, hρ _ fun i => by rw [map_pow, ht], Units.val_one] at h1
        by_contra h2
        refine h1 ?_
        rw [← map_one (algebraMap (Qbar l) _), resolventSet, Set.mem_setOf_eq, ← map_sub]
        exact (IsUnit.mk0 _ (sub_ne_zero.2 h2)).map _
      · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
        rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  refine ⟨P⁻¹, fun g => ?_⟩
  rw [inv_inv, ← hδ, ← hP g]

end UpperTheory.V.Hi.Up
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

private theorem int_iff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

theorem coef_le (a : c.O) : ‖algebraMap c.O (Qbar l) a‖ ≤ 1 :=
  (int_iff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

section Pt

variable {R : Type} [CommRing R] [Algebra c.O R]

theorem pt_lt [IsLocalRing R] (y : R →ₐ[c.O] Qbar l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Gs4b.pt_lt y a ha

variable [Alg.IsCO c.O R] (y : R →ₐ[c.O] Qbar l)

theorem pt_res (b : R) (a : c.O) (h : Alg.res c.O R b = residue c.O a) : ‖y b - algebraMap c.O (Qbar l) a‖ < 1 := by
  rw [← y.commutes, ← map_sub]
  refine pt_lt y _ ((Alg.res_eq_zero_iff c.O R _).1 ?_)
  rw [map_sub, h, AlgHom.commutes]
  exact sub_self _

theorem pt_le (b : R) : ‖y b‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := Alg.IsCO.res_surj (O := c.O) b
  have h := IsUltrametricDist.norm_add_le_max (y (b - algebraMap c.O R a)) (algebraMap c.O (Qbar l) a)
  rw [← y.commutes, ← map_add (f := _), sub_add_cancel, y.commutes] at h
  exact h.trans (max_le (pt_lt y _ ha).le (coef_le a))

theorem pt_unit (b : Rˣ) : ‖y b‖ = 1 := by
  have h : ‖y b‖ * ‖y (b⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (pt_le y _) ?_
  nlinarith [pt_le y (b⁻¹ : Rˣ), norm_nonneg (y b), norm_nonneg (y (b⁻¹ : Rˣ))]

theorem pt_small (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ b ∈ maximalIdeal R ^ N, ‖y b‖ < ε := by
  have key : ∀ (I : Ideal R) (S : Set R) (t : ℝ), 0 ≤ t → (∀ b ∈ S, ‖y b‖ ≤ t) → ∀ b ∈ Ideal.span S, ‖y b‖ ≤ t := by
    intro I S t ht hS b hb
    induction hb using Submodule.span_induction with
    | mem z hz => exact hS z hz
    | zero => simpa using ht
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul a b _ hb =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pt_le y a)).trans hb
  obtain ⟨S, hS⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨t, t0, t1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ b ∈ maximalIdeal R, ‖y b‖ ≤ t := by
    refine ⟨((S.sup fun b => ‖y b‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun b => ‖y b‖₊) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun b hb => pt_lt y b (hS ▸ Ideal.subset_span hb)
      exact_mod_cast this
    · rw [← hS]
      exact key ⊥ _ _ (NNReal.coe_nonneg _) fun b hb => Finset.le_sup (f := fun b => ‖y b‖₊) hb
  have hp : ∀ N : ℕ, ∀ b ∈ maximalIdeal R ^ N, ‖y b‖ ≤ t ^ N := by
    intro N
    induction N with
    | zero => intro b _; simpa using pt_le y b
    | succ N ih =>
      intro b hb
      rw [pow_succ] at hb
      refine Submodule.mul_induction_on hb (fun a ha b hb => ?_) fun a b ha hb => ?_
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (ht b hb) (norm_nonneg _) (pow_nonneg t0 _)
      · rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε t1
  exact ⟨N, fun b hb => (hp N b hb).trans_lt hN⟩

theorem pt_cont {Γ : Type} [TopologicalSpace Γ] {f : Γ → R} (hf : Alg.AdicCont (maximalIdeal R) f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.continuousAt_iff'.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := pt_small y ε hε
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact hN _ (Ideal.Quotient.eq.1 hg')

theorem pt_ext (x : R →ₐ[c.O] Qbar l) (S : Set R)
    (hS : ∀ (N : ℕ) (b : R), ∃ z ∈ Algebra.adjoin c.O S, b - z ∈ maximalIdeal R ^ N) (h : ∀ z ∈ S, x z = y z) : x = y := by
  refine AlgHom.ext fun b => eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨N, hN⟩ := pt_small x ε hε
  obtain ⟨M, hM⟩ := pt_small y ε hε
  obtain ⟨z, hz, hb⟩ := hS (max N M) b
  have e : x z = y z := Algebra.adjoin_le (S := AlgHom.equalizer x y) h hz
  have h1 := hN _ (Ideal.pow_le_pow_right (le_max_left _ _) hb)
  have h2 := hM _ (Ideal.pow_le_pow_right (le_max_right _ _) hb)
  rw [map_sub, ← dist_eq_norm] at h1 h2
  rw [← e, dist_comm] at h2
  exact (IsUltrametricDist.dist_triangle_max _ _ _).trans (max_le h1.le h2.le)

end Pt

end UpperTheory.V.Hi.Up
end

