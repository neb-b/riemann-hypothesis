module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChange
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr


open Filter Topology in
theorem _root_.GlobalTheory.VolBr.encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hR)
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hB1 : (B 1).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.1 ⟨0, hB.zero_mem 1 zero_le_one⟩
  by_cases hbig : (B (R * Q ^ e)).Finite
  swap
  · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
    exact le_top
  set s : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range j, (Q : ℝ) ^ i with hs
  have hs_succ : ∀ j, s (j + 1) = Q * s j + 1 := by
    intro j
    simp only [hs, Finset.sum_range_succ', pow_succ, pow_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ Finset.sum_nonneg fun i _ ↦ by positivity
  have hs_le : ∀ j, s j + 1 ≤ (Q : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp [hs]
    | succ j ih =>
      rw [hs_succ, pow_succ]
      nlinarith [hs_nonneg j]
  have hclaim : ∀ j ≤ e, (B R).encard ^ j ≤ (B 1).encard ^ j * (B (R * s j)).encard := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hs, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 0 le_rfl⟩
    | succ j ih =>
      intro hj
      have hRs : R * s j ≤ R * Q ^ e := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc s j ≤ (Q : ℝ) ^ j := by linarith [hs_le j]
          _ ≤ (Q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have hfs : (B (R * s j)).Finite := hbig.subset (isBallFam_mono hB hRs)
      have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
      have step := encard_mul_encard_le_isBallFam hB (a := R * s j) (b := R) hQpos (by linarith)
        hfs hfin h1
      have hrad : (Q : ℝ) * (R * s j) + R = R * s (j + 1) := by rw [hs_succ]; ring
      rw [hrad] at step
      calc (B R).encard ^ (j + 1) = (B R).encard ^ j * (B R).encard := pow_succ _ _
        _ ≤ (B 1).encard ^ j * (B (R * s j)).encard * (B R).encard := by
            gcongr; exact ih (by omega)
        _ = (B 1).encard ^ j * ((B (R * s j)).encard * (B R).encard) := mul_assoc _ _ _
        _ ≤ (B 1).encard ^ j * ((B 1).encard * (B (R * s (j + 1))).encard) := by gcongr
        _ = (B 1).encard ^ (j + 1) * (B (R * s (j + 1))).encard := by rw [pow_succ, mul_assoc]
  calc (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * s e)).encard := hclaim e le_rfl
    _ ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
        gcongr
        exact isBallFam_mono hB (mul_le_mul_of_nonneg_left (by linarith [hs_le e]) (by linarith))

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfPolyAsymptotics
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory

theorem eventually_le_of_poly_asymptotics :
    ∀ (d b : ℕ) (f : ℝ → ℕ → ℝ) (g : ℕ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        g ((b * n + 1) * m) ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by
  intro d b f g α β _hd hb hf hg ε hε
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ d := pow_pos hbR d
  obtain ⟨η, θ, hη, hθ, key⟩ : ∃ η θ : ℝ, 0 < η ∧ 0 < θ ∧ (β * η + 2 * θ) * (b : ℝ) ^ d < ε := by
    generalize (b : ℝ) ^ d = c at hc ⊢
    have hβ1 : (0 : ℝ) < |β| + 1 := by positivity
    refine ⟨ε / (4 * c * (|β| + 1)), ε / (8 * c), div_pos hε (by positivity),
      div_pos hε (by positivity), ?_⟩
    have e1 : (|β| + 1) * (ε / (4 * c * (|β| + 1))) * c = ε / 4 := by
      field_simp
    have e2 : ε / (8 * c) * c = ε / 8 := by
      field_simp
    have h1 : β * (ε / (4 * c * (|β| + 1))) * c ≤ |β| * (ε / (4 * c * (|β| + 1))) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self β)
        (div_pos hε (by positivity)).le) hc.le
    have h2 : 0 < ε / (4 * c * (|β| + 1)) * c := mul_pos (div_pos hε (by positivity)) hc
    nlinarith
  set A : ℝ := α + β * η + θ with hAdef
  set B : ℝ := α - θ with hBdef
  have hlim : Tendsto (fun n : ℕ => A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) atTop (𝓝 (A * (b : ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul A
    simpa using this
  have hn : ∀ᶠ n : ℕ in atTop, A * ((b : ℝ) + 1 / (n : ℝ)) ^ d < B * (b : ℝ) ^ d + ε :=
    (tendsto_order.1 hlim).2 _ (by rw [hAdef, hBdef]; nlinarith)
  have hAe : ∀ᶠ j : ℕ in atTop, f η j / (j : ℝ) ^ d < A :=
    (tendsto_order.1 (hf η hη.le)).2 A (by rw [hAdef]; linarith)
  have hBe : ∀ᶠ j : ℕ in atTop, B < f 0 j / (j : ℝ) ^ d :=
    (tendsto_order.1 (hf 0 le_rfl)).1 B (by rw [hBdef, mul_zero, add_zero]; linarith)
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hk : Tendsto (fun m : ℕ => (b * n + 1) * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos _)) tendsto_id
  have hk' : Tendsto (fun m : ℕ => b * n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.mul_pos hb hn1)) tendsto_id
  filter_upwards [hk.eventually (hAe.and (hg η hη)), hk'.eventually hBe, eventually_gt_atTop 0]
    with m ⟨hA1, hG1⟩ hB1 hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (((b * n + 1) * m : ℕ) : ℝ) = ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * m) := by
    push_cast
    rw [show ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * (m : ℝ))
        = (b : ℝ) * n * m + ((n : ℝ)⁻¹ * (n : ℝ)) * m by ring, inv_mul_cancel₀ hnR.ne']
    ring
  have hj' : ((b * n * m : ℕ) : ℝ) = (b : ℝ) * ((n : ℝ) * m) := by push_cast; ring
  have hjpos : (0 : ℝ) < (((b * n + 1) * m : ℕ) : ℝ) := by
    rw [hj]; positivity
  have hj'pos : (0 : ℝ) < ((b * n * m : ℕ) : ℝ) := by
    rw [hj']; positivity
  have hnm : (0 : ℝ) < ((n : ℝ) * m) ^ d := pow_pos (mul_pos hnR hmR) d
  have hA2 := (div_lt_iff₀ (pow_pos hjpos d)).1 hA1
  have hB2 := (lt_div_iff₀ (pow_pos hj'pos d)).1 hB1
  calc g ((b * n + 1) * m) ≤ f η ((b * n + 1) * m) := hG1
    _ ≤ A * ((((b * n + 1) * m : ℕ) : ℝ)) ^ d := hA2.le
    _ = (A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) * ((n : ℝ) * m) ^ d := by rw [hj, mul_pow]; ring
    _ ≤ (B * (b : ℝ) ^ d + ε) * ((n : ℝ) * m) ^ d := mul_le_mul_of_nonneg_right hn.le hnm.le
    _ = B * (((b * n * m : ℕ) : ℝ)) ^ d + ε * ((n : ℝ) * m) ^ d := by rw [hj', mul_pow]; ring
    _ ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConj
section
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.FrobEmb

theorem norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

def compPerm {E C : Type} [Field E] [Field C] (f : C ≃+* C) : Equiv.Perm (E →+* C) where
  toFun τ := f.toRingHom.comp τ
  invFun τ := f.symm.toRingHom.comp τ
  left_inv τ := by ext x; simp
  right_inv τ := by ext x; simp

theorem exists_frobPerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E →
    ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  intro E _ _ _ l _ _
  obtain ⟨Fr, hFr⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 l) ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_base_field
  refine ⟨compPerm Fr.toRingEquiv, ?_, fun τ => rfl⟩
  intro τ x
  have hx : ‖τ (x : E)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int τ x.isIntegral_coe)
  have h := hFr (τ (x : E)) hx
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.residue_cardinality_base_field] at h
  exact h

end GlobalTheory.FrobEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dite_eq_left hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (p := n) (q := n) (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.FinClsLoc.support_subset_compact) | (exact GlobalTheory.FinClsLoc.support_subset_compact) | (intros; apply GlobalTheory.FinClsLoc.support_subset_compact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable (F : Type) [Field F] [NumberField F]

def finU : (Af F)ˣ →* (AF F)ˣ := Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_finU : Continuous (finU F) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

def sndU : (AF F)ˣ →* (Af F)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_circle_toUnits : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, by
    have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
    refine h.congr fun z => ?_
    simp⟩

theorem exists_cong_sub (K : Set (Af F)ˣ) (hK : K ∈ 𝓝 1) : ∃ M : ℕ, 0 < M ∧ ∀ u : (Af F)ˣ,
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ (u : Af F) - 1 = M • c) →
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ((u⁻¹ : (Af F)ˣ) : Af F) - 1 = M • c) → u ∈ K := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hK
  obtain ⟨T, hT, hTK⟩ := hK
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af F => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af F => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af F => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (Filter.inter_mem h1 h2)
  refine ⟨N, hN, fun u ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => hTK (hTT ⟨?_, ?_⟩)⟩
  · change (u : Af F) ∈ T1
    rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
  · change MulOpposite.op ((u⁻¹ : (Af F)ˣ) : Af F) ∈ T2
    rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2

theorem exists_cong_ker (lam : (AF F)ˣ →* Circle) (hlam : Continuous lam)
    (h : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  let ψ : (Af F)ˣ →* ℂˣ := Circle.toUnits.comp (lam.comp (finU F))
  have hψ : Continuous ψ := (continuous_circle_toUnits).comp (hlam.comp (continuous_finU F))
  have hK := (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (x := 1) (by simp)
  obtain ⟨M, hM, hMK⟩ := exists_cong_sub F _ hK
  refine ⟨M, hM, fun b hb hb' => ?_⟩
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  have h2 : ψ (sndU F b) = 1 := hMK (sndU F b) ⟨c, hc, e⟩ ⟨c', hc', e'⟩
  have h3 : lam (finU F (sndU F b)) = 1 := by
    have := congrArg Units.val h2
    exact Subtype.ext (by simpa [ψ] using this)
  set a : (AF F)ˣ := b * (finU F (sndU F b))⁻¹ with ha
  have hfin : ((a : AF F)).2 = 1 := by
    show (b : AF F).2 * ((b⁻¹ : (AF F)ˣ) : AF F).2 = 1
    exact congrArg Prod.snd (Units.mul_inv b)
  have hA : At (evI F) ((a : AF F) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    refine Prod.ext ?_ ?_
    · show u.1 * ((a : AF F).1 - 1) = 0
      rw [hu1, zero_mul]
    · show u.2 * ((a : AF F).2 - 1) = 0
      rw [hfin, sub_self, mul_zero]
  have hb : b = a * finU F (sndU F b) := by rw [ha, inv_mul_cancel_right]
  rw [hb, map_mul, h a hA, h3, mul_one]

end GlobalTheory.HeckeExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupRightActionComponentsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteGroup_rightAction_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  first | exact @GlobalTheory.CompAct.exists_action_components | exact GlobalTheory.CompAct.exists_action_components | (intros; apply GlobalTheory.CompAct.exists_action_components <;> assumption)
end

