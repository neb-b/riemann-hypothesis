module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsPrimeSpanXb
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]

def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem card_quot_span_mul {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by
  let f : S →+ S := AddMonoidHom.mulLeft u
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hu h
  have e1 : (Ideal.span {v}).toAddSubgroup.map f = (Ideal.span {u * v}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r * v, ⟨r, rfl⟩, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
  have e2 : (⊤ : AddSubgroup S).map f = (Ideal.span {u}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  have hle : (Ideal.span {u * v}).toAddSubgroup ≤ (Ideal.span {u}).toAddSubgroup :=
    fun z hz => Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right u v) hz
  have h2 : (Ideal.span {u * v}).toAddSubgroup.relIndex (Ideal.span {u}).toAddSubgroup =
      (Ideal.span {v}).toAddSubgroup.index := by
    rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  have hc : ∀ I : Ideal S, Nat.card (S ⧸ I) = I.toAddSubgroup.index :=
    fun I => (AddSubgroup.index_eq_card _).symm
  rw [hc, hc, hc, ← AddSubgroup.relIndex_mul_index hle, h2, mul_comm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_card_locIdeal_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by
  rw [locIdeal_eq_span h₁] at hf₁ ⊢
  rw [locIdeal_eq_span h₂] at hf₂ ⊢
  rw [locIdeal_eq_span (mul_mem h₁ h₂)]
  have : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : locRing P W) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ := rfl
  rw [this, card_quot_span_mul _ _ (fun h => hne (congrArg Subtype.val h)), Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

theorem log_card_locIdeal_unit {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by
  rw [locIdeal_eq_span hy, Ideal.span_singleton_eq_top.mpr
    (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
  have : Subsingleton (locRing P W ⧸ (⊤ : Ideal (locRing P W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Nat.card_of_subsingleton (0 : locRing P W ⧸ (⊤ : Ideal (locRing P W)))]
  simp

theorem log_card_locIdeal_unit_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by
  rw [locIdeal_eq_span (mul_mem hy hc), locIdeal_eq_span hc]
  have : (⟨y * c, mul_mem hy hc⟩ : locRing P W) = ⟨y, hy⟩ * ⟨c, hc⟩ := rfl
  rw [this, Ideal.span_singleton_mul_left_unit (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]

theorem frac_mem_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) [P.IsPrime] {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W := by
  have hvP : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact fun h => hvW (hPW h))
  exact Subring.subset_closure ⟨u, v, a, hvP, hvW, hu, hv, IsLocalization.eq_mk'_iff_mul_eq.mpr hy⟩

theorem frac_unit_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by
  have hu0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huW (hPW h)
  have hv0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hvW (hPW h)
  set z := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) /
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
  refine ⟨frac_mem_locRing hPW hu hv hvW hy, z, frac_mem_locRing hPW hv hu huW (div_mul_cancel₀ _ hu0), ?_⟩
  rw [mul_div_assoc', hy, div_self hu0]

theorem RegularityLocalProduct.proof (hN : RegularityFunctionFieldNumber.Statement) (hR : RegularityFormula.Statement)
    (hD : RegularityDenominator.Statement) (hC : RegularityDivisorSupportClosed.Statement) (hF : RegularityLocalFinite.Statement) :
    RegularityLocalProduct.Statement := by
  classical
  intro K _ ι _ P f g a x t yf yg hP hf hg hfP hgP hx ht
  have : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hcW⟩ := hD K ι P x hP
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hx0 : x ≠ 0 := fun h => hφ f hfP (by rw [← hx, h]; simp)
  have hb0 : x * c ≠ 0 := mul_ne_zero hx0 hc0
  have hxc : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) = x * c := rfl
  have hmem : ∀ {s : MRing ι} {W}, IsMultiHomog s a → s ∉ P → IsClosedPt W → P ≤ W → (W ∈ divSupp P s ↔ s ∈ W) :=
    fun hs hsP hWc hPW => (hC K ι P _ a _ hP hs hsP).trans ⟨fun h => h.2.2, fun h => ⟨hWc, hPW, h⟩⟩
  have key : ∀ W, IsClosedPt W → P ≤ W →
      (if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P)))) -
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P)))) := by
    intro W hWc hPW
    obtain ⟨hcS, hbS⟩ := hcW W hWc hPW
    by_cases hU : W ∈ divSupp P f ∪ divSupp P g
    · obtain ⟨htW, htn, hyf, hyg⟩ := ht W hU
      have hyfS := frac_mem_locRing hPW hf htW htn hyf
      have hygS := frac_mem_locRing hPW hg htW htn hyg
      have hyf0 : yf W ≠ 0 := fun h => hφ f hfP (by rw [← hyf, h, zero_mul])
      have hyg0 : yg W ≠ 0 := fun h => hφ g hgP (by rw [← hyg, h, zero_mul])
      have hrel : yf W = x * yg W :=
        mul_right_cancel₀ (hφ _ fun h => htn (hPW h)) (by rw [hyf, mul_assoc, hyg, hx])
      obtain ⟨s, hs, hsP, hWs⟩ : ∃ s, IsMultiHomog s a ∧ s ∉ P ∧ W ∈ divSupp P s := by
        rcases hU with h | h
        exacts [⟨f, hf, hfP, h⟩, ⟨g, hg, hgP, h⟩]
      have fin : ∀ y, y ∈ locRing P W → y ≠ 0 → Finite (locRing P W ⧸ locIdeal P W y) :=
        fun y hy hy0 => hF K ι P s a W y hP hs hsP hWs hy hy0
      have hc0' : (c : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hb0' : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hb0 (Subtype.ext h)
      have e : yf W * c = ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) * yg W := by
        rw [hrel, hxc]; ring
      have hm := log_card_locIdeal_mul hyfS hcS hyf0 (fin _ hyfS hyf0) (fin _ hcS hc0')
      have hm' := log_card_locIdeal_mul hbS hygS hb0' (fin _ hbS hb0') (fin _ hygS hyg0)
      rw [e] at hm
      by_cases h1 : W ∈ divSupp P f <;> by_cases h2 : W ∈ divSupp P g
      · rw [if_pos h1, if_pos h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hg htW (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) htn hyg
        have := log_card_locIdeal_unit hygS hz hz1
        rw [if_pos h1, if_neg h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hf htW (fun h => h1 ((hmem hf hfP hWc hPW).mpr h)) htn hyf
        have := log_card_locIdeal_unit hyfS hz hz1
        rw [if_neg h1, if_pos h2]; linarith
      · exact absurd hU (by simp [h1, h2])
    · have h1 : W ∉ divSupp P f := fun h => hU (Or.inl h)
      have h2 : W ∉ divSupp P g := fun h => hU (Or.inr h)
      obtain ⟨hxS, z, hz, hz1⟩ := frac_unit_locRing hPW hf hg (fun h => h1 ((hmem hf hfP hWc hPW).mpr h))
        (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) hx
      rw [if_neg h1, if_neg h2, hxc, log_card_locIdeal_unit_mul hxS hz hz1 hcS]
      ring
  obtain ⟨hbfin, hbsum⟩ := hR K ι P (x * c) hP hb0 (fun W h1 h2 => (hcW W h1 h2).2)
  obtain ⟨hcfin, hcsum⟩ := hR K ι P c hP hc0 (fun W h1 h2 => (hcW W h1 h2).1)
  have eq1 : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) =
        ∑ᶠ W, (if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0) := by
    intro s y
    rw [finsum_mem_def]
    rfl
  have fsA : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      (Function.support fun W =>
        if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0).Finite :=
    fun s y => (divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h)
  have fsB : ∀ z : FractionRing (MRing ι ⧸ P),
      {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W z) ≠ 1}.Finite →
      (Function.support ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
        fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W z)))).Finite :=
    fun z hz => hz.subset fun W hW => by
      rw [Function.mem_support] at hW
      by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
      · rw [Set.indicator_of_mem hWC] at hW
        exact ⟨hWC.1, hWC.2, fun h1 => hW (by rw [h1]; simp)⟩
      · rw [Set.indicator_of_notMem hWC] at hW
        exact absurd rfl hW
  obtain ⟨hFld, hNF⟩ := hN K ι P hP
  let _ := hFld.toField
  have hσ : ∀ y : funField P, y ≠ 0 → ∀ σ : funField P →+* ℂ, σ y ≠ 0 := fun y hy σ h => by
    obtain ⟨z, hz⟩ := hFld.mul_inv_cancel hy
    have := congrArg σ hz
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc _ = ∑ᶠ W, ((if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0)) := by
        rw [eq1 f yf, eq1 g yg, finsum_sub_distrib (fsA f yf) (fsA g yg)]
    _ = ∑ᶠ W, ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸
              locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P))))) W -
          {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P))))) W) := by
        refine finsum_congr fun W => ?_
        by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
        · rw [Set.indicator_of_mem hWC, Set.indicator_of_mem hWC]
          exact key W hWC.1 hWC.2
        · rw [Set.indicator_of_notMem hWC, Set.indicator_of_notMem hWC,
            if_neg fun h => hWC ⟨((hC K ι P f a W hP hf hfP).mp h).1, ((hC K ι P f a W hP hf hfP).mp h).2.1⟩,
            if_neg fun h => hWC ⟨((hC K ι P g a W hP hg hgP).mp h).1, ((hC K ι P g a W hP hg hgP).mp h).2.1⟩]
    _ = ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ (x * c)‖ - ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ c‖ := by
        rw [finsum_sub_distrib (fsB _ hbfin) (fsB _ hcfin), ← finsum_mem_def, ← finsum_mem_def, hbsum, hcsum]
    _ = _ := by
        rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
        refine finsum_congr fun σ => ?_
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hσ x hx0 σ)) (norm_ne_zero_iff.mpr (hσ c hc0 σ))]
        ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pot_cons {e : ℕ} (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem forall_cons {m : ℕ} {p : HermLine ι → Prop} {M : HermLine ι} {N : Fin m → HermLine ι}
    (hM : p M) (hN : ∀ j, p (N j)) : ∀ j, p ((Fin.cons M N : Fin (m + 1) → HermLine ι) j) :=
  fun j => Fin.cases (by simpa using hM) (fun i => by simpa using hN i) j

theorem ptsIntegral_neg {e : ℕ} (Q : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (f : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral Q φ (fun z => -f z) = -ptsIntegral Q φ f := by
  have key : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity Q Ψ φ (fun z => -f z) y w = -sheetDensity Q Ψ φ f y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · simp

theorem log_h_eq_neg_logNorm_one (D : HermLine ι) :
    (fun z => Real.log (D.h z)) = fun z => -logNorm D 1 z := by
  funext z
  simp [logNorm, Real.log_inv]

theorem isSectionOn_one {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by
  refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
    fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ptsIntegral_add_first_log (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by
  rw [log_h_eq_neg_logNorm_one D, ptsIntegral_neg, ptsIntegral_neg, ptsIntegral_neg,
    hAdd K ι Q e L M N D 1 hQ hL hM hN hD (isSectionOn_one hQ hDa)]
  ring

theorem tendsto_finsum_of_finite {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)

theorem DeLeSemiPos.proof (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by
  intro K _ ι _ P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  obtain ⟨a, haA, hsa, hsP⟩ := id hs
  obtain ⟨a', haA', hsa', hs'P⟩ := id hs'
  have ht : ∃ b : K → ℕ, (∀ k, A.a k = b k) ∧ IsMultiHomog s b := ⟨a, haA, hsa⟩
  have ht' : ∃ b : K → ℕ, (∀ k, A'.a k = b k) ∧ IsMultiHomog s' b := ⟨a', haA', hsa'⟩
  obtain ⟨C, hC⟩ := hCurv K ι A' s' ht' hA'
  have hT := isSmoothHerm_ofMetrics_fs (ι := ι) (fun _ => (C : ℤ))
  generalize HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ)) = T at hC hT
  have hfin : ∀ t : MRing ι, {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
    fun t => (divSupp_finite P t).subset fun W h => h.1

  have e1 : ∀ ε : ℝ, 0 < ε →
      ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s) =
        ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A' s' ht' ε).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) := by
    intro ε hε
    have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
    rw [pot_cons, hAdd K ι P n L _ T A s hP hL (isSmoothHerm_tensor hA' hB) hT hA hs,
      hAdd K ι P n L A' _ A s hP hL hA' hB hA hs, hPL1 K ι P n L A _ s hP hL hA hB rfl hs]
  have h1 : Tendsto
      (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s))
      (𝓝[>] 0)
      (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => (e1 ε hε).symm
    refine Tendsto.congr' ev ((tendsto_const_nhds.add
      ((tendsto_finsum_of_finite (hfin s) fun W hW => ?_).sub ?_)).add tendsto_const_nhds)
    · exact (hLim K ι W n L A' s' ht' ((divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2) hL hA'
        (hNot K ι P (n + 2) s s' W hP hsP hs'P hnc hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons A L) A' s' ht' hP (forall_cons hA hL) hA' hs'P
      rwa [pot_cons] at h

  have h2 : ∀ δ : ℝ, 0 < δ →
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) ≤
      (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z)) := by
    intro δ hδ
    have hD : IsSmoothHerm (regLine A s ht δ) := isSmoothHerm_regLine hA hδ
    have hlimD := hLim K ι P (n + 1) (Fin.cons (regLine A s ht δ) L) A' s' ht' hP (forall_cons hD hL) hA'
      hs'P
    rw [pot_cons, hPL1 K ι P n L A' _ s' hP hL hA' hD rfl hs'] at hlimD
    have hR : Tendsto
        (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)))) := by
      have eR : ∀ ε : ℝ, 0 < ε →
          ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log ((regLine A s ht δ).h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) =
          ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
            (fun z => Real.log ((regLine A s ht δ).h z)) := by
        intro ε hε
        have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
        rw [pot_cons, ptsIntegral_add_first_log hAdd hP hL (isSmoothHerm_tensor hA' hB) hT hD rfl,
          ptsIntegral_add_first_log hAdd hP hL hA' hB hD rfl,
          hSt K ι P n L (regLine A s ht δ) (regLine A' s' ht' ε) hP hL hD hB rfl rfl]
      have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => eR ε hε
      exact Tendsto.congr' ev ((tendsto_const_nhds.add hlimD).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto h1 hR (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMono K ι P (n + 1) _ A (regLine A s ht δ) s hP
        (forall_cons (isSmoothHerm_tensor (isSmoothHerm_tensor hA' (isSmoothHerm_regLine hA' hε)) hT) hL)
        (forall_cons (hC ε hε) hLp) hA hs hD rfl
        (fun z hz h0 => logNorm_le_log_regLine_h hδ.le hz.1 h0))
    linarith

  have h3 : Tendsto
      (fun δ => (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (logNorm A s)) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    refine (tendsto_finsum_of_finite (hfin s') fun W hW => ?_).add ?_
    · exact (hLim K ι W n L A s ht ((divSuppArith K ι P (n + 1) A' s' W hP hs' hW.1).1 hW.2) hL hA
        (hNot K ι P (n + 2) s' s W hP hs'P hsP (fun W h h' => hnc W h' h) hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons T L) A s ht hP (forall_cons hT hL) hA hsP
      rwa [pot_cons] at h
  have h4 := ge_of_tendsto h3 (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact h2 δ hδ)
  unfold De
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (S : PluckerBlocks n n j),
    flagMinor M j S * ∏ a ∈ Finset.Iic j, leadMinor M a = leadMinor M j * flagMinor (pivotMatrix M) j S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

