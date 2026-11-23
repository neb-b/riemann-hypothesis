module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0024
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0020
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0023
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorSub

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem padic_mem_Kur {l : ℕ} [Fact l.Prime] (a : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] a ∈ MaximalUnramifiedExtension l := by
  have hcont : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
  have hclosed : IsClosed ((MaximalUnramifiedExtension l : Set ℂ_[l])) := Subfield.isClosed_topologicalClosure _
  have hpre : IsClosed ((algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l])) := hclosed.preimage hcont
  have hall : Set.range ((↑) : ℚ → ℚ_[l]) ⊆ (algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    rintro _ ⟨q, rfl⟩
    show algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) ∈ MaximalUnramifiedExtension l
    rw [map_ratCast]
    exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) q
  have hmem : a ∈ closure (Set.range ((↑) : ℚ → ℚ_[l])) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr⟩ := Padic.rat_dense (p := l) a hε
    exact ⟨r, ⟨r, rfl⟩, by rw [dist_eq_norm]; exact hr⟩
  exact hpre.closure_subset_iff.mpr hall hmem

theorem sqrt_mem_Kur {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : ℂ_[l]}
    (hs : s ^ 2 = -(d : ℂ_[l])) : s ∈ MaximalUnramifiedExtension l := by
  have hd : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd (l := l) hld
  have hc : -(d : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact neg_mem (natCast_mem (MaximalUnramifiedExtension l) d)
    | exact neg_mem (by simpa using SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) (d : ℚ))
  have h2 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_neg, hd]
  have hy : ‖s‖ = 1 := by
    have h0 := norm_nonneg s
    nlinarith [h2, h0]
  exact sqrt_mem (l := l) hl (-(d : ℂ_[l])) s hc hy hs

def kurAlg (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  ((MaximalUnramifiedExtension l).comap (algebraMap (PadicAlgCl l) ℂ_[l])).toIntermediateField fun a => by
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) a) ∈ MaximalUnramifiedExtension l
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur a

theorem mem_kurAlg {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} :
    y ∈ kurAlg l ↔ algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := Iff.rfl

theorem kur_le {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : PadicAlgCl l}
    (hs : s ^ 2 = -(d : PadicAlgCl l)) {y : PadicAlgCl l}
    (hy : y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s})) :
    algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by
  have hK : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {s}) := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic s).isIntegral

  have hq2 : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra hlt
    push_neg at hlt
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 1 - 1 = 0 := by rw [pow_one]; omega
    have h2 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 - 1 = 0 := by
      have : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 := by
        calc ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ = 1 := one_pow 2
      omega
    have e : ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 1 = ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 2 := by simp only [ReciprocityTheory.DiscreteGroups.LocalClassField.Kn, h1, h2]
    have d1 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 1) one_pos
    have d2 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 2) two_pos
    rw [e, d2] at d1
    omega

  have hlq : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra h
    obtain ⟨n, hn, hdvd⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_dvd_qK_pow_sub_one (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK h
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := dvd_pow_self _ hn.ne'
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := Nat.one_le_pow _ _ (by omega)
    have h3 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - 1) := by
      first
      | exact Nat.dvd_sub h1 hdvd
      | exact Nat.dvd_sub (by omega) h1 hdvd
    rw [Nat.sub_sub_self hpos] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  have hnd : ∀ k, 0 < k → ¬ l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1 := by
    intro k hk h
    have h1 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := hlq.trans (dvd_pow_self _ hk.ne')
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := Nat.one_le_pow _ _ (by omega)
    have h3 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1) := by
      first
      | exact Nat.dvd_sub h1 h
      | exact Nat.dvd_sub (by omega) h1 h
    rw [Nat.sub_sub_self hpos] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

  have hle : ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s}) ≤ kurAlg l := by
    refine iSup_le fun n => sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_kurAlg]
      refine sqrt_mem_Kur hl hld ?_
      rw [← map_pow, hs, map_neg, map_natCast]
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      have hζ0 : ζ ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := hζ
      rw [SetLike.mem_coe, mem_kurAlg]
      have hζ' : (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := by
        rw [← map_pow, hζ0, map_one]
      have hN : 0 < ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1 := by
        have : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) := le_trans hq2 (Nat.le_self_pow (by omega) _)
        omega
      exact Subfield.le_topologicalClosure _
        (Subfield.subset_closure ⟨_, hN, hnd (n + 1) (Nat.succ_pos n), hζ'⟩)
  exact mem_kurAlg.1 (hle hy)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedVeluFun
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by
  have hne := Formalism.L2.Th1.E.AddThm.P_sub_ne L z P hz hP hp hm
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := Formalism.L2.Th1.E.AddThm.P_add L z P hz hP hp hm
  have h2 := Formalism.L2.Th1.E.AddThm.P_add L z (-P) hz hP' (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
  have hY := L.derivWeierstrassP_sq z hz
  have hy := L.derivWeierstrassP_sq P hP
  rw [L.weierstrassP_neg, h1, h2]
  unfold fW fW'
  generalize L.weierstrassP z = X at *
  generalize L.weierstrassP P = x at *
  generalize L.derivWeierstrassP z = Y at *
  generalize L.derivWeierstrassP P = y at *
  field_simp
  linear_combination 4 * hY + 4 * hy

theorem velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by
  obtain ⟨hK, hdisj⟩ := hT.kerReps
  have hzL : z ∉ L.lattice := fun h => hz (hs z h)
  rw [isogenyP L α _ hα hs hK z hz, Finset.sum_union hdisj,
    Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
  simp only [veluFun, xsOf]
  rw [Finset.sum_image (by intro a ha b hb h; exact hT.injOn ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hαP, h2P⟩ := hT.1 P hP

  have hPL : P ∉ L.lattice := fun h => h2P (by rw [two_mul]; exact L.lattice.add_mem h h)

  have hp : z + P ∉ L.lattice := fun h => hz (by
    have := L.lattice.sub_mem (hs _ h) hαP
    rwa [mul_add, add_sub_cancel_right] at this)
  have hm : z - P ∉ L.lattice := fun h => hz (by
    have := L.lattice.add_mem (hs _ h) hαP
    rwa [mul_sub, sub_add_cancel] at this)
  exact velu_pair L z P hzL hPL hp hm

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorLift
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_close {C : Type} [NormedField C] [IsUltrametricDist C] {x a p q : C} (hx : ‖x‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hp : ‖p‖ ≤ 1) (hxa : ‖x - a‖ < 1) :
    ‖(a ^ 3 + p * a + q) - (x ^ 3 + p * x + q)‖ < 1 := by
  have e : (a ^ 3 + p * a + q) - (x ^ 3 + p * x + q) = (a - x) * (a ^ 2 + a * x + x ^ 2 + p) := by ring
  rw [e, norm_mul]
  have h1 : ‖a ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have h2 : ‖a * x‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hx
  have h3 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hb : ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)) hp)
  rw [norm_sub_rev] at hxa
  calc ‖a - x‖ * ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ ‖a - x‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hxa

theorem norm_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] {c d : C} (hd : ‖d‖ = 1)
    (h : ‖c - d‖ < 1) : ‖c‖ = 1 := by
  have hne : ‖d‖ ≠ ‖c - d‖ := by rw [hd]; exact (ne_of_lt h).symm
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel, hd] at h2
  rw [h2]
  exact max_eq_left h.le

theorem tor_lift (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (hx : ‖px _ P‖ ≤ 1) (hy : ‖py _ P‖ = 1) :
    ∃ Q : (shortW g2 g3).toAffine.Point, InSub (MaximalUnramifiedExtension l) Q ∧ InFormalGroupPoints (P - Q) := by
  have hI := good_int h
  have hC := good_coeff h
  obtain ⟨-, -, -, h4, h6, -⟩ := hI
  obtain ⟨-, -, -, m4, m6⟩ := hC
  have hl2 : l ≠ 2 := by have := h.five; omega
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change ‖y‖ = 1 at hy
    obtain ⟨a, haT, hxa⟩ := res_full l x hx
    have haK : a ∈ MaximalUnramifiedExtension l := tch_mem_kur l haT
    have ha1 : ‖a‖ ≤ 1 := tch_norm_le l haT
    have hE : y ^ 2 = x ^ 3 + (shortW g2 g3).a₄ * x + (shortW g2 g3).a₆ := by
      have := (WeierstrassCurve.Affine.equation_iff _ _).1 hns.1
      simpa [shortW] using this
    set p := (shortW g2 g3).a₄ with hp
    set q := (shortW g2 g3).a₆ with hq
    have hc1 : ‖a ^ 3 + p * a + q‖ = 1 := by
      refine norm_one_of_close (d := y ^ 2) (by rw [norm_pow, hy, one_pow]) ?_
      rw [hE]
      exact cubic_close hx ha1 h4 hxa
    have hcK : a ^ 3 + p * a + q ∈ MaximalUnramifiedExtension l :=
      add_mem (add_mem (pow_mem haK 3) (mul_mem m4 haK)) m6
    obtain ⟨b, hbK, hb2, hb1⟩ := exists_sqrt l hl2 _ hcK hc1
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hb1
      exact zero_ne_one hb1
    have hQns : (shortW g2 g3).toAffine.Nonsingular a b := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨?_, Or.inr ?_⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        simp only [shortW] at hb2 hp hq ⊢
        rw [hb2, hp, hq]
        ring
      · simp only [shortW]
        intro hh
        apply hb0
        have h2 : (2 : ℂ_[l]) * b = 0 := by linear_combination hh
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 two_ne_zero
        · exact h3
    set P : (shortW g2 g3).toAffine.Point := .some x y hns with hPdef
    set Q : (shortW g2 g3).toAffine.Point := .some a b hQns with hQdef
    have hQS : InSub (MaximalUnramifiedExtension l) Q := ⟨haK, hbK⟩
    by_cases h1 : InFormalGroupPoints (P - Q)
    · exact ⟨Q, hQS, h1⟩
    by_cases h2 : InFormalGroupPoints (P + Q)
    · exact ⟨-Q, inSub_neg _ _ (good_coeff h) Q hQS, by rwa [sub_neg_eq_add]⟩
    exfalso
    obtain ⟨d0, dx, -⟩ := integral_of_not_mem_formalGroup h _ h1
    obtain ⟨s0, sx, -⟩ := integral_of_not_mem_formalGroup h _ h2
    have hu := Formalism.L2.Th1.E.UnitDiff_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P Q
      hP0 (WeierstrassCurve.Affine.Point.some_ne_zero _) s0 d0 hx hy.le ha1 hb1.le sx dx
    change ‖x - a‖ = 1 at hu
    exact absurd hu hxa.ne

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorTwo
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_coeff_ind (p : ℂ_[l] → Prop) (T : Cubic ℂ_[l]) (h0 : p 0) (ha : p T.a) (hb : p T.b)
    (hc : p T.c) (hd : p T.d) (i : ℕ) : p (T.toPoly.coeff i) := by
  rcases i with _ | _ | _ | _ | i
  · simpa [Cubic.coeff_eq_d] using hd
  · simpa [Cubic.coeff_eq_c] using hc
  · simpa [Cubic.coeff_eq_b] using hb
  · simpa [Cubic.coeff_eq_a] using ha
  · rw [Cubic.coeff_eq_zero (by omega)]
    exact h0

theorem tor_two (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (h2 : P + P = 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hl4 : ¬ l ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P 2 hl2 (by rw [two_nsmul]; exact h2) hP0
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P hE
  obtain ⟨hpsi, hkap⟩ :=
    Formalism.L2.Th1.E.UnitKap_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P hP0 h2 hx hy
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change 2 * y + (shortW g2 g3).a₁ * x + (shortW g2 g3).a₃ = 0 at hpsi
    change ‖3 * x ^ 2 + 2 * (shortW g2 g3).a₂ * x + (shortW g2 g3).a₄ - (shortW g2 g3).a₁ * y‖ = 1 at hkap
    change x ∈ MaximalUnramifiedExtension l ∧ y ∈ MaximalUnramifiedExtension l
    have hy0 : y = 0 := by
      simp only [shortW, zero_mul, add_zero] at hpsi
      simpa using hpsi
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [shortW] at heq hkap
    have n4 : ‖(4 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_natCast_Cl_of_not_dvd (l := l) hl4
    have m4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
    refine ⟨?_, hy0 ▸ zero_mem _⟩
    refine hensel_mem l (Cubic.toPoly ⟨1, 0, -g2 / 4, -g3 / 4⟩) ?_ ?_ x hx ?_ ?_
    · exact cubic_coeff_ind (· ∈ MaximalUnramifiedExtension l) _ (zero_mem _) (one_mem _) (zero_mem _)
        (div_mem (neg_mem h.mem2) m4) (div_mem (neg_mem h.mem3) m4)
    · refine cubic_coeff_ind (‖·‖ ≤ 1) _ (by simp) (by simp) (by simp) ?_ ?_
      · simpa [norm_div, n4] using h.norm2
      · simpa [norm_div, n4] using h.norm3
    · simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [hy0] at heq
      linear_combination -heq
    · have : (Cubic.toPoly (⟨1, 0, -g2 / 4, -g3 / 4⟩ : Cubic ℂ_[l])).derivative.eval x
          = 3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y := by
        simp only [Cubic.toPoly, Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_natCast,
          map_natCast]
        push_cast
        ring
      rw [this]
      exact hkap

end ReciprocityTheory.ChartRestriction.L1
end
end

