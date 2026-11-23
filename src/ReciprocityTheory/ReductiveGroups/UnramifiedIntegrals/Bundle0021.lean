module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0020
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0019
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedCardG
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

namespace CardG

theorem card_line {F : Type} [Field F] [Fintype F] (u v : F) (h : u ≠ 0 ∨ v ≠ 0) :
    (Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)).card = Fintype.card F := by
  rcases h with h | h
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (-(v * t) / u, t)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨y, ?_, rfl⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, e, rfl⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).2), Finset.card_univ]
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (t, -(u * t) / v)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨x, rfl, ?_⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, rfl, e⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).1), Finset.card_univ]

theorem card_ker {F : Type} [Field F] [Fintype F] (a b c d : F) (hdet : a * d - b * c = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    (Finset.univ.filter (fun w : F × F => a * w.1 + b * w.2 = 0 ∧ c * w.1 + d * w.2 = 0)).card
      = Fintype.card F := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · rw [← card_line a b hab]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => e.1, fun e => ⟨e, ?_⟩⟩
    rcases hab with h | h
    · apply mul_left_cancel₀ h
      linear_combination c * e + y * hdet
    · apply mul_left_cancel₀ h
      linear_combination d * e - x * hdet
  · push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hcd
      push Not at hcd
      exact hne ⟨ha, hb, hcd.1, hcd.2⟩
    rw [← card_line c d hcd]
    congr 1
    ext ⟨x, y⟩
    simp [ha, hb]

theorem coord_unique (L : PeriodPair) {m n m' n' : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = m' * L.ω₁ + n' * L.ω₂) : m = m' ∧ n = n' := by
  have hi := LinearIndependent.pair_iff.mp L.indep ((m - m' : ℤ) : ℝ) ((n - n' : ℤ) : ℝ) (by
    simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have := hi.1
    have h2 : m - m' = 0 := by exact_mod_cast this
    omega
  · have := hi.2
    have h2 : n - n' = 0 := by exact_mod_cast this
    omega

theorem mem_iff (L : PeriodPair) (p : ℕ) (hp : p ≠ 0) {z : ℂ} {m n : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z) :
    z ∈ L.lattice ↔ (m : ZMod p) = 0 ∧ (n : ZMod p) = 0 := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hz
    obtain ⟨m', n', e⟩ := PeriodPair.mem_lattice.mp hz
    have := coord_unique L (m := m) (n := n) (m' := p * m') (n' := p * n') (by
      rw [h, ← e]; push_cast; ring)
    exact ⟨⟨m', this.1⟩, ⟨n', this.2⟩⟩
  · rintro ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩
    refine PeriodPair.mem_lattice.mpr ⟨m', n', ?_⟩
    apply mul_left_cancel₀ hpc
    rw [← h]; push_cast; ring

def co (L : PeriodPair) (z : ℂ) : ℤ × ℤ :=
  if h : z ∈ L.lattice then
    ((PeriodPair.mem_lattice.mp h).choose, (PeriodPair.mem_lattice.mp h).choose_spec.choose)
  else 0

theorem co_spec (L : PeriodPair) {z : ℂ} (h : z ∈ L.lattice) :
    ((co L z).1 : ℂ) * L.ω₁ + ((co L z).2 : ℂ) * L.ω₂ = z := by
  rw [co, dite_eq_left h]
  exact (PeriodPair.mem_lattice.mp h).choose_spec.choose_spec

end CardG

open CardG

theorem card_G (L : PeriodPair) (β : ℂ) (hβ : MulStable L β) (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Complex.normSq β = ((p * M : ℕ) : ℝ)) (hM : ¬ p ∣ M) (T : Finset ℂ)
    (hT : IsHalfReps L (p : ℂ) T) :
    2 * (T.filter (fun P => β * P ∈ L.lattice)).card + 1 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hS1, hS2, hS3⟩, hdisj⟩ := hT.kerReps
  obtain ⟨a, b, c, d, h1, h2, -, hn⟩ := Ker.matrix_data L β hβ
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hdetZ : a * d - b * c = (p : ℤ) * M := by
    have : ((a * d - b * c : ℤ) : ℝ) = (((p : ℤ) * M : ℤ) : ℝ) := by
      rw [← hn, hN]; push_cast; ring
    exact_mod_cast this
  have hdet : (a : ZMod p) * d - b * c = 0 := by
    have := congrArg (fun k : ℤ => (k : ZMod p)) hdetZ
    simpa using this
  have hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
    simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩
    apply hM
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (M : ℤ) = p * (a' * d' - b' * c') := by
      apply mul_left_cancel₀ hp0
      rw [← hdetZ]; ring
    exact Int.natCast_dvd_natCast.mp ⟨_, this⟩

  have hmul : ∀ {z : ℂ} {m n : ℤ}, (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z →
      (β * z ∈ L.lattice ↔ (a : ZMod p) * m + b * n = 0 ∧ (c : ZMod p) * m + d * n = 0) := by
    intro z m n e
    have := mem_iff L p hp.ne_zero (z := β * z) (m := a * m + b * n) (n := c * m + d * n) (by
      push_cast
      linear_combination β * e - (m : ℂ) * h1 - (n : ℂ) * h2)
    rw [this]; push_cast; rfl
  set S := T ∪ T.image (fun P => -P) with hSdef
  set K := Finset.univ.filter (fun w : ZMod p × ZMod p =>
    (a : ZMod p) * w.1 + b * w.2 = 0 ∧ (c : ZMod p) * w.1 + d * w.2 = 0) with hK
  have hKcard : K.card = p := by
    have := card_ker (a : ZMod p) b c d hdet hne
    rw [ZMod.card] at this
    rw [hK]
    convert this
  have h0K : (0 : ZMod p × ZMod p) ∈ K := by simp [hK]
  have hcardS : (S.filter (fun P => β * P ∈ L.lattice)).card
      = 2 * (T.filter (fun P => β * P ∈ L.lattice)).card := by
    have himg : (T.image (fun P => -P)).filter (fun P => β * P ∈ L.lattice)
        = (T.filter (fun P => β * P ∈ L.lattice)).image (fun P => -P) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨P, hP, rfl⟩, hQ⟩
        refine ⟨P, ⟨hP, ?_⟩, rfl⟩
        have := neg_mem hQ
        simpa using this
      · rintro ⟨P, ⟨hP, hQ⟩, rfl⟩
        refine ⟨⟨P, hP, rfl⟩, ?_⟩
        have := neg_mem hQ
        simpa using this
    rw [hSdef, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), himg,
      Finset.card_image_of_injective _ neg_injective]
    ring
  have hbij : (S.filter (fun P => β * P ∈ L.lattice)).card = (K.erase 0).card := by
    apply Finset.card_nbij
      (fun z => (((co L (p * z)).1 : ZMod p), ((co L (p * z)).2 : ZMod p)))
    · intro P hP
      obtain ⟨hPS, hPβ⟩ := Finset.mem_filter.mp hP
      have e := co_spec L (hS1 P hPS).1
      rw [Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h0
        apply (hS1 P hPS).2
        rw [mem_iff L p hp.ne_zero e]
        exact Prod.mk.inj h0
      · rw [hK, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmul e).mp hPβ⟩
    · intro P hP Q hQ hPQ
      have hPS := (Finset.mem_filter.mp (Finset.mem_coe.mp hP)).1
      have hQS := (Finset.mem_filter.mp (Finset.mem_coe.mp hQ)).1
      have eP := co_spec L (hS1 P hPS).1
      have eQ := co_spec L (hS1 Q hQS).1
      apply hS2 P hPS Q hQS
      rw [mem_iff L p hp.ne_zero (m := (co L (p * P)).1 - (co L (p * Q)).1)
        (n := (co L (p * P)).2 - (co L (p * Q)).2) (by push_cast; linear_combination eP - eQ)]
      obtain ⟨e1, e2⟩ := Prod.mk.inj hPQ
      push_cast
      exact ⟨sub_eq_zero.mpr e1, sub_eq_zero.mpr e2⟩
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hxy0, hxyK⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hxy)
      obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
      set z : ℂ := ((m : ℂ) * L.ω₁ + n * L.ω₂) / p with hz
      have ez : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z := by rw [hz]; field_simp
      have hzp : (p : ℂ) * z ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨m, n, ez⟩
      have hzL : z ∉ L.lattice := by
        rw [mem_iff L p hp.ne_zero ez]
        rintro ⟨e1, e2⟩
        exact hxy0 (by rw [e1, e2]; rfl)
      have hzβ : β * z ∈ L.lattice := (hmul ez).mpr (Finset.mem_filter.mp hxyK).2
      obtain ⟨P, hPS, hzP⟩ := hS3 z hzp hzL
      have eP := co_spec L (hS1 P hPS).1
      refine ⟨P, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hPS, ?_⟩), ?_⟩
      · have : β * P = β * z - β * (z - P) := by ring
        rw [this]
        exact sub_mem hzβ (hβ _ hzP)
      · have := (mem_iff L p hp.ne_zero (m := m - (co L (p * P)).1)
          (n := n - (co L (p * P)).2) (by push_cast; linear_combination ez - eP)).mp hzP
        push_cast at this
        exact Prod.ext (sub_eq_zero.mp this.1).symm (sub_eq_zero.mp this.2).symm
  rw [← hcardS, hbij, Finset.card_erase_of_mem h0K, hKcard]
  have := hp.pos
  omega

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProj
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

section Proj

variable {E : Type} [Field E]

def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)

def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))

theorem coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]

theorem serMap_sum (ψ : E →+ E) {ι : Type} (s : Finset ι) (f : ι → PowerSeries E) :
    serMap ψ (∑ i ∈ s, f i) = ∑ i ∈ s, serMap ψ (f i) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp [coeff_serMap, map_sum]

theorem coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial_apply]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp

theorem natDegree_polMap_le (ψ : E →+ E) (m : ℕ) (Q : E[X]) : (polMap ψ m Q).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polMap, if_neg (by omega)]

variable (k : Subfield E)

theorem coeff_mem_mul {S T : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k)
    (hT : ∀ n, PowerSeries.coeff n T ∈ k) : ∀ n, PowerSeries.coeff n (S * T) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hS _) (hT _)

theorem coeff_mem_one : ∀ n, PowerSeries.coeff n (1 : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

theorem coeff_mem_pow {S : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k) (i : ℕ) :
    ∀ n, PowerSeries.coeff n (S ^ i) ∈ k := by
  induction i with
  | zero => simpa using coeff_mem_one k
  | succ i ih => rw [pow_succ]; exact coeff_mem_mul k ih hS

theorem coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

variable {k}

theorem serMap_mul (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]

theorem serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero ψ

theorem serMap_homS (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {U : PowerSeries E}
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (m : ℕ) (Q : E[X]) :
    serMap ψ (homS U m Q) = homS U m (polMap ψ m Q) := by
  unfold homS
  rw [serMap_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hW : ∀ n, PowerSeries.coeff n (U ^ i * PowerSeries.X ^ (2 * (m - i))) ∈ k :=
    coeff_mem_mul k (coeff_mem_pow k hU i) (coeff_mem_pow k (coeff_mem_X k) _)
  rw [coeff_polMap, if_pos hi', mul_assoc, mul_assoc, mul_comm (PowerSeries.C (Q.coeff i)),
    serMap_mul ψ hψ hW, serMap_C, mul_comm]

theorem exists_proj (k : Subfield E) : ∃ ψ : E →+ E, (∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) ∧
    (∀ x, ψ x ∈ k) ∧ ψ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  refine ⟨(k.subtype : k →+ E).comp g.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro c hc x
    have := g.map_smul (⟨c, hc⟩ : k) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    have h2 : (⟨c, hc⟩ : k) • x = c * x := rfl
    rw [← h2, this]
    rfl
  · intro x
    exact (g x).2
  · have := LinearMap.congr_fun hg 1
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    simp [this]

end Proj

theorem proj_trick {E : Type} [Field E] (k : Subfield E) (U V : PowerSeries E)
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (hV : ∀ n, PowerSeries.coeff n V ∈ k)
    (hU0 : PowerSeries.constantCoeff U = 1) (A B : E[X]) (N : ℕ) (hA : A.natDegree ≤ N + 1)
    (hB : B.Monic) (hBd : B.natDegree = N) (hc : IsCoprime A B)
    (h : V * homS U N B = homS U (N + 1) A) : ∀ i, B.coeff i ∈ k := by
  obtain ⟨ψ, hψ, hψk, hψ1⟩ := exists_proj k
  set A' := polMap ψ (N + 1) A with hA'
  set B' := polMap ψ N B with hB'
  have hA'd : A'.natDegree ≤ N + 1 := natDegree_polMap_le ψ _ A
  have hB'd : B'.natDegree ≤ N := natDegree_polMap_le ψ _ B
  have h' : V * homS U N B' = homS U (N + 1) A' := by
    rw [hA', hB', ← serMap_homS ψ hψ hU, ← serMap_homS ψ hψ hU, ← serMap_mul ψ hψ hV, h]
  have hBN : B'.coeff N = 1 := by
    rw [hB', coeff_polMap, if_pos le_rfl, ← hBd, hB.coeff_natDegree, hψ1]
  have hB'deg : B'.natDegree = N := by
    refine le_antisymm hB'd (le_natDegree_of_ne_zero ?_)
    rw [hBN]; exact one_ne_zero
  have hB'm : B'.Monic := by
    rw [Monic, leadingCoeff, hB'deg, hBN]
  have hcross : A * B' = A' * B := by
    have h0 : homS U (N + 1 + N) (A * B' - A' * B) = 0 := by
      rw [homS_sub, homS_mul U _ _ _ _ hA hB'd, homS_mul U _ _ _ _ hA'd hBd.le, ← h, ← h']
      ring
    have hdeg : (A * B' - A' * B).natDegree ≤ N + 1 + N := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (add_le_add hA hB'd)
      · exact natDegree_mul_le.trans (add_le_add hA'd hBd.le)
    exact sub_eq_zero.mp (homS_eq_zero U hU0 _ _ hdeg h0)
  have hdvd : B ∣ B' := by
    refine hc.symm.dvd_of_dvd_mul_left ?_
    rw [hcross]
    exact dvd_mul_left _ _
  have heq : B = B' :=
    (eq_of_monic_of_dvd_of_natDegree_le hB hB'm hdvd (by rw [hB'deg, hBd])).symm
  intro i
  rw [heq, hB', coeff_polMap]
  split_ifs
  · exact hψk _
  · exact zero_mem k

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValA
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem jInv_sub_1728_eq_div (L : PeriodPair) :
    jInv L - 1728 = 1728 * 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  have hD := discNeZero L
  unfold jInv
  field_simp
  ring

theorem jInv_ratio (L : PeriodPair) (h3 : L.g₃ ≠ 0) :
    27 * jInv L / (jInv L - 1728) = L.g₂ ^ 3 / L.g₃ ^ 2 := by
  have hD := discNeZero L
  rw [jInv_sub_1728_eq_div]
  unfold jInv
  field_simp

theorem exists_cm_lattice_equal_invariants (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) :
    ∃ L0 : PeriodPair, HasCMBy d L0 ∧ jInv L0 = jInv L ∧
      L0.g₂ = 27 * jInv L / (jInv L - 1728) ∧ L0.g₃ = 27 * jInv L / (jInv L - 1728) := by
  obtain ⟨c, hc2⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₃ / L.g₂) (n := 2) (by norm_num)
  have hc : c ≠ 0 := by
    rintro rfl
    have : L.g₃ / L.g₂ ≠ 0 := div_ne_zero h3 h2
    apply this
    rw [← hc2]
    norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := homogeneity L c hc
  refine ⟨scalePair L c hc, hasCMByScale d L c hc hCM, jInvScale L c hc, ?_, ?_⟩
  · rw [hg2, jInv_ratio L h3, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    field_simp
  · rw [hg3, jInv_ratio L h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc2]
    field_simp

theorem jInv_eq_zero_iff (L : PeriodPair) : jInv L = 0 ↔ L.g₂ = 0 := by
  have hD := discNeZero L
  unfold jInv
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

theorem jInv_eq_iff (L : PeriodPair) : jInv L = 1728 ↔ L.g₃ = 0 := by
  have hD := discNeZero L
  rw [← sub_eq_zero, jInv_sub_1728_eq_div, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

end ReciprocityTheory.ChartRestriction.L1
end
end

