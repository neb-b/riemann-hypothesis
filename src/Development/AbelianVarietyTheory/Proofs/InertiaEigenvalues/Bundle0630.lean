module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ρ : IrrGL (k := k)} {hρ : ρ.IsCusp} {c d c' d' : ℤ} {h : c ≤ d} {h' : c' ≤ d'} {Δ Δ' : Segment k}

theorem first_mem_carrier (Δ : Segment k) : Δ.first ∈ Δ.carrier := mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩

theorem nu_mem_icc {a : ℤ} : ρ.nu a ∈ (icc ρ hρ c d h).carrier ↔ c ≤ a ∧ a ≤ d := by
  simp only [mem_icc, IrrGL.nu_intCast_inj hρ.1]
  exact ⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩

theorem eq_icc_of_first_eq (hρ : ρ.IsCusp) (e : Δ.first = ρ.nu c) :
    Δ = icc ρ hρ c (c + Δ.len - 1) (Int.le_sub_one_of_lt (lt_add_of_pos_right c (Nat.cast_pos.2 Δ.len_pos))) :=
  ext_first e (by simp only [icc, len_ofFirst]; omega)

theorem exists_eq_icc_of_mem (hρ : ρ.IsCusp) {a : ℤ} (ha : ρ.nu a ∈ Δ.carrier) :
    ∃ (c d : ℤ) (h : c ≤ d), Δ = icc ρ hρ c d h := by
  obtain ⟨b, -, hb⟩ := mem_carrier.1 ha
  refine ⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩
  have := congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb
  simpa [sub_eq_add_neg] using this

theorem icc_subset_icc : (icc ρ hρ c d h).carrier ⊆ (icc ρ hρ c' d' h').carrier ↔ c' ≤ c ∧ d ≤ d' := by
  refine ⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩,
    fun ⟨h1, h2⟩ x hx => ?_⟩
  obtain ⟨a, h3, h4, rfl⟩ := mem_icc.1 hx
  exact nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩

theorem exists_carrier_eq_union_icc :
    (∃ Γ : Segment k, Γ.carrier = (icc ρ hρ c d h).carrier ∪ (icc ρ hρ c' d' h').carrier) ↔
      c' ≤ d + 1 ∧ c ≤ d' + 1 := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    obtain ⟨e, f, hef, rfl⟩ := exists_eq_icc_of_mem (Δ := Γ) hρ (a := c)
      (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))
    have key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d') := fun a => by
      simpa only [Set.mem_union, nu_mem_icc] using Set.ext_iff.1 hΓ (ρ.nu a)
    have := key c; have := key d'; have := key c'; have := key d; have := key (d + 1); have := key (d' + 1)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩
    simp only [Set.mem_union, mem_icc]
    constructor
    · rintro ⟨a, h3, h4, rfl⟩
      by_cases ha : c ≤ a ∧ a ≤ d
      · exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
      · exact Or.inr ⟨a, by omega, by omega, rfl⟩
    · rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩

theorem linked_icc : (icc ρ hρ c d h).Linked (icc ρ hρ c' d' h') ↔
    (c < c' ∧ c' ≤ d + 1 ∧ d < d') ∨ (c' < c ∧ c ≤ d' + 1 ∧ d' < d) := by
  rw [Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]
  omega

theorem precedes_icc : (icc ρ hρ c d h).Precedes (icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d' := by
  have key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c' := by
    have e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j := fun j => by
      rw [← IrrGL.nu_intCast_inj hρ.1]
      simp [icc]
    simp only [e]
    exact ⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩
  rw [Precedes, linked_icc, key]
  omega

theorem Linked.exists_eq_icc (H : Linked Δ Δ') : ∃ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
    Δ = icc ρ hρ c d h ∧ Δ' = icc ρ hρ c' d' h' := by
  obtain ⟨⟨Γ, hΓ⟩, -⟩ := H
  have key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h :=
    fun D hD => by
      obtain ⟨a, -, ha⟩ := mem_carrier.1 (hD D.first_mem_carrier)
      exact ⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩
  obtain ⟨c, d, h, e⟩ := key Δ (hΓ ▸ Set.subset_union_left)
  obtain ⟨c', d', h', e'⟩ := key Δ' (hΓ ▸ Set.subset_union_right)
  exact ⟨_, _, c, d, c', d', h, h', e, e'⟩

theorem linked_iff_precedes : Linked Δ Δ' ↔ Precedes Δ Δ' ∨ Precedes Δ' Δ := by
  refine ⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩
  obtain ⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩ := H.exists_eq_icc
  simpa only [precedes_icc] using linked_icc.1 H

theorem precedes_iff : Precedes Δ Δ' ↔
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len ∧ Δ'.first = Δ.first.nu j := by
  have key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len) := fun j e => by
    have e1 := eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)
    have e2 := eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)
    refine (iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)
    omega
  refine ⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨j, -, e⟩ := H.2
  obtain ⟨h1, h2, h3⟩ := (key j e).1 H
  exact ⟨j, h1, h2, h3, e⟩

theorem exists_first_eq_of_transGen (H : Relation.TransGen Precedes Δ Δ') :
    ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j := by
  induction H with
  | single H => exact H.2
  | tail _ H ih =>
    obtain ⟨i, hi, e⟩ := ih
    obtain ⟨j, -, e'⟩ := H.2
    exact ⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩

theorem not_transGen_precedes_self (Δ : Segment k) : ¬ Relation.TransGen Precedes Δ Δ := fun H => by
  obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H
  exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))

theorem Precedes.asymm (H : Precedes Δ Δ') : ¬ Precedes Δ' Δ := fun H' =>
  not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')

theorem lt_of_precedes_nu {x y : ℝ} (H : (Δ.nu x).Precedes (Δ.nu y)) : x < y := by
  obtain ⟨-, j, hj, e⟩ := H
  have e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ) := by
    push_cast
    exact e.trans (Δ.first.nu_nu x j)
  have : (0 : ℝ) < j := Nat.cast_pos.2 hj
  rw [(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']
  linarith

theorem not_precedes_nu (Δ : Segment k) {x y : ℝ} (hxy : y < x) : ¬ (Δ.nu x).Precedes (Δ.nu y) := fun H =>
  hxy.asymm (lt_of_precedes_nu H)

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem exists_list_pairwise_not_rel {α : Type*} {r : α → α → Prop} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (m : Multiset α) : ∃ l : List α, (l : Multiset α) = m ∧ l.Pairwise fun a b => ¬ r a b := by
  classical
  let p : α → α → Prop := fun a b => Relation.ReflTransGen r b a
  haveI : IsPartialOrder α p :=
    { refl := fun _ => .refl
      trans := fun _ _ _ h h' => h'.trans h
      antisymm := fun a b h h' => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h
        · exact e
        · exact absurd (h.trans_left h') (hr _) }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  refine ⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩
  obtain rfl : a = b := antisymm hab (hps _ _ (.single h))
  exact hr a (.single h)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOrderedForm (𝔪 : Multiset (Segment k)) :
    ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪 := by
  obtain ⟨l, rfl, hl⟩ := exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪
  exact ⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩

theorem isOrderedForm_tw_iff {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪 :=
  ⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv,
    fun H => H.tw χ hχ⟩

theorem precedes_and_orderedForms (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ((∀ Δ Δ' : Segment k, Δ.Precedes Δ' → ¬ Δ'.Precedes Δ) ∧
      (∀ Δ : Segment k, ¬ Relation.TransGen Segment.Precedes Δ Δ) ∧
      ∀ 𝔪 : Multiset (Segment k), ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪) ∧
    ((∀ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
        (Segment.icc ρ hρ c d h).Precedes (Segment.icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d') ∧
      ∀ Δ Δ' : Segment k, Δ.Linked Δ' ↔ Δ.Precedes Δ' ∨ Δ'.Precedes Δ) ∧
    (∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Linked (Δ'.tw χ hχ) ↔ Δ.Linked Δ') ∧
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Precedes (Δ'.tw χ hχ) ↔ Δ.Precedes Δ') ∧
      ∀ (h : ℕ) (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)),
        IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪) ∧
    ∀ (Δ : Segment k) (x y : ℝ), y < x → ¬ (Δ.nu x).Precedes (Δ.nu y) :=
  ⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩,
    ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩,
    fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ,
      fun _ _ _ => isOrderedForm_tw_iff χ hχ⟩,
    fun Δ _ _ h => Δ.not_precedes_nu h⟩

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalUnitaryEmbeddingDefiniteUnitaryNonspl
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG

namespace GlobalTheory.UnitaryBC.NonSplit

variable {E : Type} [Field E] [NumberField E]

theorem matrix_ext_pLoc {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Af E)}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), A.map (pLoc E u) = B.map (pLoc E u)) : A = B :=
  Matrix.ext fun i j => FiniteAdeleRing.ext E fun u => congrFun₂ (H u) i j

theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem eq_conjSrc_self (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) :
    w = conjSrc c w := by
  refine eq_conjSrc fun k => ?_
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
    w.valuedAdicCompletion_eq_valuation' _
  rw [← h1, ← h2, ← hs, hv]

theorem cT_locGL_mul (c : E ≃+* E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    cT (conjFin c) (locGL E n w g).val * (locGL E n w g).val = 1 := by
  refine matrix_ext_pLoc fun u => ?_
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  by_cases hu : u = w
  · subst hu
    have e1 : (locGL E n u g).val.map (pLoc E u) = g.val := congrArg Units.val (pLoc_locGL u g)
    have e2 : (cT (conjFin c) (locGL E n u g).val).map (pLoc E u) = cT s g.val := by
      ext1 i j
      change pLoc E u (conjFin c ((locGL E n u g).val j i)) = s (g.val j i)
      rw [← e1]
      exact pLoc_conjFin_eq c u s hs hv _
    rw [e1, e2, hg]
  · have hne : conjSrc c u ≠ w := fun e =>
      hu (conjSrc_injective c (e.trans (eq_conjSrc_self c w s hs hv)))
    have e1 : (locGL E n w g).val.map (pLoc E u) = 1 := congrArg Units.val (pLoc_locGL_of_ne hu g)
    have e3 : (locGL E n w g).val.map (pLoc E (conjSrc c u)) = 1 := congrArg Units.val (pLoc_locGL_of_ne hne g)
    have e2 : (cT (conjFin c) (locGL E n w g).val).map (pLoc E u) = 1 := by
      ext1 i j
      change conjLoc c u (((locGL E n w g).val.map (pLoc E (conjSrc c u))) j i) = _
      rw [e3]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, Ne.symm hij]
    rw [e1, e2, Matrix.mul_one]

variable [IsCMField E]

theorem finGL_locGL_mem_UA {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  have h1 : (finGL E n (locGL E n w g)).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL (locGL E n w g))
  have h2 : (finGL E n (locGL E n w g)).val.map (pFin E) = (locGL E n w g).val :=
    congrArg Units.val (pFin_finGL (locGL E n w g))
  have h3 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pInf E) = 1 := by
    ext1 i j
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) (pInf E ((finGL E n (locGL E n w g)).val j i)))) = _
    rw [RingEquiv.symm_apply_apply]
    change starRingEnd (Cinf E) (((finGL E n (locGL E n w g)).val.map (pInf E)) j i) = _
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  have h4 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pFin E) =
      cT (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E n w g).val := by
    ext1 i j
    change conjFin _ (((finGL E n (locGL E n w g)).val.map (pFin E)) j i) = _
    rw [h2]
    rfl
  have h5 := cT_locGL_mul (IsCMField.complexConj E).toRingEquiv w s hs hv g hg
  have h6 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pInf E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) := by
    rw [Matrix.map_mul, h3, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have h7 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pFin E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) := by
    rw [Matrix.map_mul, h4, h2, h5, Matrix.map_one _ (map_zero _) (map_one _)]
  ext1 i j
  exact ad_ext (congrFun₂ h6 i j) (congrFun₂ h7 i j)

end GlobalTheory.UnitaryBC.NonSplit


open GlobalTheory.UnitaryBC.NonSplit in
theorem GlobalTheory.UnitaryBC.exists_locUnitary_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w →
    ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧
      (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧
      ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  intro E _ _ _ n w s hs hv hns
  have hU : ∀ g : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      finGL E n (locGL E n w g.1) ∈ UA E n := fun g => by
    refine finGL_locGL_mem_UA w s hs hv g.1 ?_
    have h : cT s g.1.val * 1 * g.1.val = 1 := g.2
    rwa [Matrix.mul_one] at h
  refine ⟨((finGL E n).comp ((locGL E n w).comp (Formalism.UG.UJ s 1).subtype)).codRestrict (UA E n) hU,
    Continuous.subtype_mk (((continuous_finGL' n).comp (CuspSub.continuous_locGL w)).comp continuous_subtype_val) _,
    fun g => ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, ?_⟩, fun x hx h1 => ?_, fun x g h1 => ?_⟩
  · change GeneralLinearGroup.map (pInf E) (finGL E n (locGL E n w g.1)) = 1
    exact pInf_finGL _
  · change GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = 1
    rw [pFin_finGL]
    exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = g.1
    rw [pFin_finGL, pLoc_locGL]
  · obtain ⟨hxf, hxi⟩ := Subgroup.mem_inf.1 hx
    have hinf : GeneralLinearGroup.map (pInf E) x.1 = 1 := MonoidHom.mem_ker.1 hxf
    have hloc : ∀ u, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) x.1) = 1 := fun u => by
      by_cases hu : u = w
      · subst hu; exact h1
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hns ⟨u, hu, e⟩
        exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxi u) hu')
    refine Subtype.ext (ga_ext (hinf.trans (map_one _).symm) ?_)
    change _ = GeneralLinearGroup.map (pFin E) 1
    rw [map_one]
    exact LocUniq.gl_ext fun u => by rw [hloc u, map_one]
  · have hk : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x.1) = 1 := h1
    apply Subtype.ext
    change x.1 * finGL E n (locGL E n w g.1) = finGL E n (locGL E n w g.1) * x.1
    obtain ⟨y, k, hx, hk'⟩ : ∃ y k, x.1 = infGL E n y * finGL E n k ∧ GeneralLinearGroup.map (pLoc E w) k = 1 :=
      ⟨_, _, (infGL_mul_finGL x.1).symm, hk⟩
    rw [hx, mul_assoc, ← map_mul, LocUniq.comm_locGL w hk' g.1, map_mul, ← mul_assoc, infGL_comm, mul_assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmoothForm

theorem exists_smooth_form_ne_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  intro G V _ _ _ _ _ ρ hK hρ v hv
  obtain ⟨K, hKo, hKc, hKU⟩ := hK {g | ρ g v = v} ((hρ v).mem_nhds (by simp))
  have hfix : v ∈ fixed ρ K := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => hKU hh
  have hnot : v ∉ twKer ρ K 1 := fun h => hv (GlobalTheory.IwahoriInj.eq_zero_of_fixed hρ hKc hfix h)
  have hq : (twKer ρ K 1).mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (V ⧸ twKer ρ K 1), f ((twKer ρ K 1).mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨f ∘ₗ (twKer ρ K 1).mkQ, ?_, hf⟩
  have hinv : ∀ g ∈ K, ρ.dual g (f ∘ₗ (twKer ρ K 1).mkQ) = f ∘ₗ (twKer ρ K 1).mkQ := by
    intro g hg
    refine LinearMap.ext fun x => ?_
    rw [Representation.dual_apply]
    show f ((twKer ρ K 1).mkQ (ρ g⁻¹ x)) = f ((twKer ρ K 1).mkQ x)
    congr 1
    exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer (inv_mem hg) x)
  exact GlobalTheory.SmGL.mem_smoothPart_of_nhds
    (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun g hg => hinv g hg)

end GlobalTheory.SmoothForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelForms
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finU_mul_infU_comm (k y : UA E n) (hk : k ∈ finU (E := E) (n := n)) (hy : y ∈ infU E n) : k * y = y * k := by
  have hk' : Matrix.GeneralLinearGroup.map (pInf E) (k : GA E n) = 1 := MonoidHom.mem_ker.1 hk
  have hy' : Matrix.GeneralLinearGroup.map (pFin E) (y : GA E n) = 1 := MonoidHom.mem_ker.1 hy
  apply Subtype.ext
  apply ga_ext
  · simp only [Subgroup.coe_mul, map_mul, hk', one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, hy', one_mul, mul_one]

def levelForms (L : Subgroup (finU (E := E) (n := n))) (C : Submodule ℂ (infU E n → ℂ)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
    ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, a1 γ hγ g, b1 γ hγ g]
    · simp only [Pi.add_apply, a2 k hk g, b2 k hk g]
    · exact C.add_mem (a3 g) (b3 g)
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => C.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨a1, a2, a3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, a1 γ hγ g]
    · simp only [Pi.smul_apply, a2 k hk g]
    · exact C.smul_mem c (a3 g)

end GlobalTheory.UnitaryBC


open GlobalTheory.UnitaryBC in
theorem GlobalTheory.UnitaryBC.finiteDimensional_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  intro E _ _ _ n hS L hL C _
  obtain ⟨S, hS⟩ := hS L hL
  let M := levelForms L C
  have hle : Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} ≤ M :=
    Submodule.span_le.2 fun ψ h => h

  have key : ∀ ψ ∈ M, ∀ g, ∃ s ∈ S, ∃ y ∈ infU E n, ψ g = ψ (s * y) := by
    rintro ψ ⟨h1, h2, -⟩ g
    obtain ⟨γ, hγ, s, hs, k, hk, y, hy, rfl⟩ := hS g
    refine ⟨s, hs, y, hy, ?_⟩
    rw [mul_assoc, mul_assoc, h1 γ hγ, finU_mul_infU_comm _ _ k.2 hy, ← mul_assoc, h2 k hk]
  let f : M →ₗ[ℂ] (S → C) :=
    { toFun := fun ψ s => ⟨fun y : infU E n => ψ.1 ((s : UA E n) * (y : UA E n)), ψ.2.2.2 s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext g
    obtain ⟨s, hs, y, hy, e⟩ := key (a.1 - b.1) (M.sub_mem a.2 b.2) g
    have := congrArg (fun F : S → C => ((F ⟨s, hs⟩ : C) : infU E n → ℂ) ⟨y, hy⟩) hab
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
    have e' : a.1 g - b.1 g = a.1 (s * y) - b.1 (s * y) := e
    rw [this, sub_self, sub_eq_zero] at e'
    exact e'
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective f hf
  exact Submodule.finiteDimensional_of_le hle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem h1f_generators_of_record : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  intro D l _ K LL _ T _
  exact _root_.GlobalTheory.H1fGeneration.h1fGen_tied l (D.loc l) (D.locA l) (D.locT l) K LL T

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  first | exact @GlobalTheory.IntConnTaylor.main | exact GlobalTheory.IntConnTaylor.main | (intros; apply GlobalTheory.IntConnTaylor.main <;> assumption)
end

