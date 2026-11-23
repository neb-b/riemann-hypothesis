module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0459
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0031
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPowPrimePowSubLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfIsRootDistinguishedWittPolynomial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.RootLt

open Polynomial

theorem norm_iotaO_le_one (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ‖GlobalTheory.TameFrob.iotaO l a w‖ ≤ 1 := by
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)
    have hω : ω ^ l ^ a = ω := by
      simp only [ω]
      rw [← map_pow, ← map_pow, Fq.pow_card]
    by_contra h
    push_neg at h
    have h2 : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt
    have h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a := pow_lt_pow_right₀ h h2
    rw [pow_one, ← norm_pow, hω] at h3
    exact lt_irrefl _ h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]
    have hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1 :=
      (PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2
    calc _ ≤ 1 * 1 := mul_le_mul hc hx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_lt_one_of_isRoot : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  intro l _ a _ P hP hdiv x hx
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · have : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [this, Polynomial.map_one] at hx
    simp [Polynomial.IsRoot] at hx
  by_contra hge
  push_neg at hge
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

  have hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹ := by
    intro i hi
    obtain ⟨c, hc⟩ := hdiv i hi
    rw [hc, map_mul, norm_mul, hnl]
    calc _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left (norm_iotaO_le_one l a c) (by positivity)
      _ = _ := mul_one _
  have hxd : (1 : ℝ) ≤ ‖x‖ ^ d := one_le_pow₀ hge

  have heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0 := by
    have h := hx
    rw [Polynomial.IsRoot, hP.as_sum] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Polynomial.eval_finsetSum, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_mul] using h
  have hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)
  have hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left heq
  have h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    calc ‖x‖ ^ d = ‖x ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ := by rw [hxeq, norm_neg]
      _ ≤ _ := hsum
  have h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d := by
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    nlinarith
  exact lt_irrefl _ (h1.trans_lt h2)

end GlobalTheory.RootLt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖t i‖)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, NeZero.pos e⟩⟩)
  have ht0 : t i0 ≠ 0 := by
    intro h
    apply h0
    rw [hyt]
    refine Finset.sum_eq_zero fun i _ => norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    simpa [h] using hi0 i (Finset.mem_univ _)
  have hpos : 0 < ‖t i0‖ := norm_pos_iff.2 ht0
  have hrest : ‖∑ i ∈ Finset.univ.erase i0, t i‖ < ‖t i0‖ := by
    have hterm : ∀ i ∈ Finset.univ.erase i0, ‖t i‖ < ‖t i0‖ := by
      intro i hi
      by_cases hti : t i = 0
      · rw [hti, norm_zero]; exact hpos
      refine lt_of_le_of_ne (hi0 i (Finset.mem_univ _)) fun h => ?_
      exact (Finset.mem_erase.1 hi).1 (hdist i i0 hti ht0 h)
    generalize Finset.univ.erase i0 = s at hterm ⊢
    induction s using Finset.induction_on with
    | empty => simpa using hpos
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (max_lt (hterm i (Finset.mem_insert_self _ _))
          (ih (fun j hj => hterm j (Finset.mem_insert_of_mem hj))))
  have hy2 : ‖y‖ = ‖t i0‖ := by
    rw [hyt, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]
  obtain ⟨m, hm⟩ := hnt i0 ht0
  exact ⟨_, by rw [hy2, hm]⟩

end GlobalTheory.ValGroupKprime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.PointConditions

theorem sum_single_jumps {M : Type} [AddCommMonoid M] [One M] (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : M) else 0)) = if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    rw [Finset.sum_eq_single (n + 1)]
    · rw [if_pos (by push_cast; ring)]
    · intro c _ hne
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem isSSRep_rhoChiK (D : D7) (i : D.nd.Loc) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.BlockSemisimple ρ (D.nd.chi i) D.R.t) : IsSSRep (rhoChiK D i ρ) := by
  rw [GlobalTheory.ComplementCompare.isSSRep_iff]
  refine (GlobalTheory.ComplementCompare.semisimple_congr (splitRT (KK D.nd i) D.R.r D.R.t) ?_).2 h
  intro g v
  change splitRT _ _ _ (((rhoChiK D i ρ g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) :
      Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec v) = _
  unfold rhoChiK
  rw [blockRep_coe, blockHom_mulVec, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply]
  refine Prod.ext rfl (funext fun c => ?_)
  show (Matrix.diagonal _).mulVec _ c = _
  rw [Matrix.mulVec_diagonal]
  rfl

theorem main : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  intro D r ρ h i π hπ
  have hc := h.compl i π hπ
  refine ⟨h.frob i π hπ, isSSRep_rhoChiK D i (ρ i π) hc.ss, ?_, ?_⟩
  · intro _ _ _ w hw C τ
    have hB := h.block i π hπ w hw C.LL C.le τ
    refine ⟨fun a => ?_, fun c hc a => hB.2 c hc a⟩
    have h2 : ∀ c ∈ Finset.Icc 1 D.R.t, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0 := fun c hc => hB.2 c hc a
    rw [Finset.sum_congr rfl h2, sum_single_jumps]
    exact hB.1 a
  · obtain ⟨e, he⟩ := hc.rho
    refine ⟨e, fun g u => ?_⟩
    have := he g u
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply] at this
    exact this

end GlobalTheory.PointConditions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mk_one_eq_zero_iff_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (x : M) :
    LocalizedModule.mk x (1 : Submonoid.powers t) = 0 ↔ ∃ r : ℕ, t ^ r • x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers t), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, r, rfl⟩, h⟩
    exact ⟨r, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨r, h⟩
    exact ⟨⟨t ^ r, r, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

theorem exists_eq_mk_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) :
    ∃ (n : M) (k : ℕ), IsFrac t z n k := by
  induction z using LocalizedModule.induction_on with
  | _ n s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨n, k, rfl⟩

theorem mk_one_eq_pow_smul_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) (m : M) (k : ℕ) (h : IsFrac t z m k) :
    LocalizedModule.mk m (1 : Submonoid.powers t) = t ^ k • z := by
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem exists_pow_smul_eq_zero_of_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    (t c : A) (m : M) (k : ℕ) (v : ι → A) (w : ι → M) (z : ι → LocalizedModule (Submonoid.powers t) M)
    (Z : LocalizedModule (Submonoid.powers t) M) (hm : IsFrac t Z m k) (hZ : Z = ∑ j, v j • z j)
    (hw : ∀ j, LocalizedModule.mk (w j) (1 : Submonoid.powers t) = c • z j) :
    ∃ r : ℕ, t ^ r • (c • m - t ^ k • ∑ j, v j • w j) = 0 := by
  rw [← mk_one_eq_zero_iff_pow_smul]
  have h1 := mk_one_eq_pow_smul_of_isFrac t Z m k hm
  have hlin : ∀ x : M, LocalizedModule.mk x (1 : Submonoid.powers t) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) M x := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hlin, map_sub, map_smul, map_smul, map_sum]
  simp only [map_smul, ← hlin, hw, h1, hZ, Finset.smul_sum, smul_smul]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LocalizedModule.smul'_mk, hw, smul_smul, smul_smul]
  congr 1
  ring

theorem mk_tr_eq_smul_Φ_tr {l : ℕ} {R : Type} [CommRing R] (M : FCrys l R) {P P' : Obj l R} (f : Hom P P')
    (d : ↥P.I) (d' : ↥P'.I) (x mx : M.M P) (k : ℕ) (hreg : IsSMulRegular (M.M P') (f.f d))
    (h : IsFrac (d : P.A) (M.Φ P d x) mx k) :
    LocalizedModule.mk (M.tr f mx) (1 : Submonoid.powers (d' : P'.A)) = f.f d ^ k • M.Φ P' d' (M.tr f x) := by
  obtain ⟨n, s, hn⟩ := exists_eq_mk_pow (d' : P'.A) (M.Φ P' d' (M.tr f x))
  obtain ⟨r, hr⟩ := M.Φ_nat f d d' x mx k n s h hn
  rw [mul_pow, mul_smul] at hr
  have hr' := (hreg.pow r).right_eq_zero_of_smul hr
  rw [smul_sub, sub_eq_zero] at hr'
  rw [hn, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨(d' : P'.A) ^ r, r, rfl⟩, ?_⟩
  simpa [Submonoid.smul_def] using hr'

theorem frob_tr_basis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S)
    (hA : ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j))
      (∑ i, bk.toP (A i j) • e i) a)
    (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ)
    (hm : IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k) :
    ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k •
      ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  have hreg : IsSMulRegular (M.M Q) (BK.hf g bk.E) := by
    haveI := M.proj Q
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (_root_.GlobalTheory.BSP.hf_E_span_and_regular l K bk Q g).2

  have key : ∀ j : Fin d, LocalizedModule.mk (M.tr g (∑ i, bk.toP (A i j) • e i)) (1 : Submonoid.powers (t : Q.A)) =
      BK.hf g bk.E ^ a • M.Φ Q t (M.tr g (e j)) := fun j =>
    mk_tr_eq_smul_Φ_tr M g ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ t (e j) _ a hreg (hA j)
  have hsum : ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i) =
      ∑ j, Q.D.φ (y j) • M.tr g (∑ i, bk.toP (A i j) • e i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]; rfl
  have hΦ : M.Φ Q t (∑ j, y j • M.tr g (e j)) = ∑ j, Q.D.φ (y j) • M.Φ Q t (M.tr g (e j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul]
  rw [hsum]
  exact exists_pow_smul_eq_zero_of_sum (t : Q.A) (BK.hf g bk.E ^ a) m k (fun j => Q.D.φ (y j))
    (fun j => M.tr g (∑ i, bk.toP (A i j) • e i)) (fun j => M.Φ Q t (M.tr g (e j))) _ hm hΦ key

end GlobalTheory.BSP
end
end

