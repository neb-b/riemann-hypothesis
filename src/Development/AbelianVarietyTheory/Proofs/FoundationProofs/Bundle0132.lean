module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit :
    ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' →
        (Cong (p := p) k x 0 ↔ ∀ r, Cong (p := p) k (c r) 0) ∧
          ((∃ r, c r ≠ 0 ∧ IsInt (p := p) (c r)⁻¹) → x ≠ 0 ∧ IsInt (p := p) x⁻¹) :=
  GlobalTheory.Glue.ev_cong_iff_and_unit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjugateFamilyOfInjective
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.Lag

theorem mdiff_of_hasQ {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  obtain ⟨a, ha⟩ := h
  exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).1

theorem hasQ_of_qConj {g : ℂ ≃+* ℂ} {N : ℕ} {f f' : ℍ → ℂ} (h : QConj g N f f') :
    (∃ a, HasQ N f a) ∧ ∃ a, HasQ N f' a := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨⟨a, ha⟩, ⟨_, hb⟩⟩

theorem qConj_refl {N : ℕ} {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) : QConj (RingEquiv.refl ℂ) N f f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, by simpa using ha⟩

theorem hasQ_zero (N : ℕ) : HasQ N (0 : ℍ → ℂ) (fun _ => 0) := by
  intro τ
  simp only [zero_mul, Pi.zero_apply]
  exact hasSum_zero

theorem qConj_ne_zero {g : ℂ ≃+* ℂ} {N : ℕ} (hN : 0 < N) {f f' : ℍ → ℂ} (h : QConj g N f f') (hf : f ≠ 0) :
    f' ≠ 0 := by
  obtain ⟨a, ha, hb⟩ := h
  rintro rfl
  have h1 := (_root_.GlobalTheory.QFam.hasQ_unique_both).1 N 0 _ _ hN hb (hasQ_zero N)
  have h2 : a = fun _ => 0 := funext fun n => by
    have := congrFun h1 n
    simpa using this
  subst h2
  exact hf ((_root_.GlobalTheory.QFam.hasQ_unique_both).2 N f 0 _ ha (hasQ_zero N))

theorem prod_ne_zero {N : ℕ} (hN : 0 < N) {κ : Type} (s : Finset κ) (u : κ → ℍ → ℂ)
    (hu : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a) : (fun τ => ∏ l ∈ s, u l τ) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    have := congrFun h UpperHalfPlane.I
    simp at this
  | insert x s hx ih =>
    have hs : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a := fun l hl => hu l (Finset.mem_insert_of_mem hl)
    have hQ : ∃ b, HasQ N (fun τ => ∏ l ∈ s, u l τ) b :=
      (hasQ_of_qConj ((_root_.GlobalTheory.QFam.qConj_ring (RingEquiv.refl ℂ) N hN).2.2.2.2.2 κ s u u
        fun l hl => qConj_refl (hs l hl).2).2).1
    intro h
    have hprod : ∀ τ, u x τ * (∏ l ∈ s, u l τ) = 0 := fun τ => by
      have := congrFun h τ
      simpa [Finset.prod_insert hx] using this
    rcases _root_.GlobalTheory.fn_mul_eq_zero_dom (u x) _ (mdiff_of_hasQ hN (hu x (Finset.mem_insert_self x s)).2)
      (mdiff_of_hasQ hN hQ) hprod with h1 | h1
    · exact (hu x (Finset.mem_insert_self x s)).1 h1
    · exact ih hs h1

end GlobalTheory.FN.Lag

namespace GlobalTheory.FN.Lag


open Finset in
theorem conj_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hb hb' ht ht' hF hinj htt' hFq
  classical
  have hR := _root_.GlobalTheory.QFam.qConj_ring g N hN
  have hRr := _root_.GlobalTheory.QFam.qConj_ring (RingEquiv.refl ℂ) N hN
  have hA := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act'

  obtain ⟨c, hc, hlag⟩ := _root_.GlobalTheory.QFam.LagrangeFam.lagrange_fam ι act m k N t F hN hb ht hF (fun i => (hasQ_of_qConj (htt' i)).1) hFq
  choose c' hc' using fun j => _root_.GlobalTheory.FN.exists_conj_level_one g (k + m * j) N (c j) hN (hc j).1 (hc j).2

  obtain ⟨s, hs, hmin⟩ := _root_.GlobalTheory.QFam.minpoly_coeff_invariant ι act k N F ⊤ hN hb hF
    (fun i => let ⟨a, ha⟩ := hFq i; ⟨a, ha, fun _ => Subring.mem_top _⟩)
  choose s' hs' using fun j : Fin (Fintype.card ι) => _root_.GlobalTheory.FN.exists_conj_level_one g (k * (Fintype.card ι - j)) N (s j) hN (hs j).1
    (let ⟨a, ha, _⟩ := (hs j).2; ⟨a, ha⟩)

  obtain ⟨D, hD⟩ : ∃ D : ι → ℍ → ℂ, ∀ i, D i = fun τ => ∏ l ∈ univ.erase i, (t i τ - t l τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ι → ℍ → ℂ, ∀ i, D' i = fun τ => ∏ l ∈ univ.erase i, (t' i τ - t' l τ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ι → ℍ → ℂ, ∀ i, A i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  obtain ⟨A', hA'd⟩ : ∃ A' : ι → ℍ → ℂ, ∀ i, A' i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c' j τ * t' i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  have hDD : ∀ i, QConj g N (D i) (D' i) := fun i => by
    rw [hD i, hD' i]
    exact (hR.2.2.2.2.2 ι (univ.erase i) (fun l τ => t i τ - t l τ) (fun l τ => t' i τ - t' l τ)
      (fun l _ => hR.2.2.1 _ _ _ _ (htt' i) (htt' l))).2
  have hAA : ∀ i, QConj g N (A i) (A' i) := fun i => by
    rw [hAd i, hA'd i]
    exact (hR.2.2.2.2.2 ℕ (range (Fintype.card ι)) (fun j τ => c j τ * t i τ ^ (Fintype.card ι - 1 - j))
      (fun j τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j))
      (fun j _ => hR.2.2.2.1 _ _ _ _ (hc' j).2 (hR.2.2.2.2.1 _ _ _ (htt' i)))).1
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD i]
    refine prod_ne_zero hN (univ.erase i) (fun l τ => t i τ - t l τ) fun l hl => ⟨?_, ?_⟩
    · intro h
      apply Finset.ne_of_mem_erase hl
      apply hinj
      funext τ
      have := congrFun h τ
      simp only [Pi.zero_apply] at this
      exact (sub_eq_zero.mp this).symm
    · exact (hasQ_of_qConj (hRr.2.2.1 _ _ _ _ (qConj_refl (hasQ_of_qConj (htt' i)).1)
        (qConj_refl (hasQ_of_qConj (htt' l)).1))).1
  have hD'ne : ∀ i, D' i ≠ 0 := fun i => qConj_ne_zero hN (hDD i) (hDne i)

  choose F' hF'1 hF'2 using fun i => _root_.GlobalTheory.FN.conj_exists g N (Fintype.card ι) (F i) (D i) (D' i) (A i) (A' i) s s' hN
    (hFq i) (hDD i) (hAA i) (fun j => (hs' j).2) (hDne i)
    (fun τ => by simp only [hD, hAd]; exact hlag i τ) (fun τ => hmin i τ)
  refine ⟨F', ?_, hF'1⟩

  have hv := (_root_.GlobalTheory.QFam.isFam_iff_values ι act' m t').1 ht'
  have hD'fam : IsFam act' ((m * (Fintype.card ι - 1) : ℕ) : ℤ) D' := by
    rw [_root_.GlobalTheory.QFam.isFam_iff_values]
    intro i γ τ
    simp only [hD', hv]
    set X : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)
    have e : ∀ l ∈ univ.erase i, X ^ (m : ℤ) * t' (act' i γ) τ - X ^ (m : ℤ) * t' (act' l γ) τ =
        X ^ (m : ℤ) * (t' (act' i γ) τ - t' (act' l γ) τ) := fun _ _ => by ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ]
    congr 1
    · rw [← zpow_natCast, ← zpow_mul]
      push_cast
      ring_nf
    · apply Finset.prod_nbij (fun l => act' l γ)
      · intro l hl
        exact Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hl ((hb' γ).1 h), mem_univ _⟩
      · intro l _ l' _ h
        exact (hb' γ).1 h
      · intro y hy
        obtain ⟨l, hl⟩ := (hb' γ).2 y
        refine ⟨l, ?_, hl⟩
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩)
        subst h
        exact Finset.ne_of_mem_erase (Finset.mem_coe.mp hy) hl.symm
      · intro l _
        rfl
  have hA'fam : IsFam act' ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) A' := by
    have e : A' = fun i τ => ∑ j ∈ range (Fintype.card ι), (fun j i τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j)) j i τ := by
      funext i τ
      rw [hA'd i]
    rw [e]
    refine hA.2.2.2.2.2.1 ℕ _ _ _ fun j hj => ?_
    have hj' : j < Fintype.card ι := Finset.mem_range.mp hj
    have hw : ((k + m * j : ℕ) : ℤ) + ((Fintype.card ι - 1 - j : ℕ) : ℤ) * (m : ℤ) =
        ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hj')
      rw [hr, show j + r - j = r by omega]
      push_cast
      ring
    rw [← hw]
    exact hA.2.2.2.1 _ _ (fun _ => c' j) (fun i τ => t' i τ ^ (Fintype.card ι - 1 - j))
      (fun _ γ => (hc' j).1 γ) (hA.2.2.2.2.1 _ _ _ ht')
  intro i γ
  have e1 : (F' i ∣[(k : ℤ)] γ) * (D' i ∣[((m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ) =
      A' i ∣[((k + m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ := by
    rw [show ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) = (k : ℤ) + ((m * (Fintype.card ι - 1) : ℕ) : ℤ) by push_cast; ring,
      ← ModularForm.mul_slash_SL2]
    congr 1
    funext τ
    exact hF'2 i τ
  rw [hD'fam i γ, hA'fam i γ] at e1
  have hz : ∀ τ, ((F' i ∣[(k : ℤ)] γ) τ - F' (act' i γ) τ) * D' (act' i γ) τ = 0 := fun τ => by
    have := congrFun e1 τ
    simp only [Pi.mul_apply] at this
    rw [sub_mul, this, hF'2, sub_self]
  have hol1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F' i ∣[(k : ℤ)] γ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 i)).2) _ _
  rcases _root_.GlobalTheory.fn_mul_eq_zero_dom _ _ (hol1.sub (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 (act' i γ))).2))
    (mdiff_of_hasQ hN (hasQ_of_qConj (hDD (act' i γ))).2) hz with h | h
  · funext τ
    exact sub_eq_zero.mp (congrFun h τ)
  · exact absurd h (hD'ne _)

end GlobalTheory.FN.Lag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowNStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 → ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  first | exact @GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | exact GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | (intros; apply GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDomGauss
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_dom_gauss : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ V : ValuationSubring Ω, ∃ W : ValuationSubring X.K, Dom X V W ∧ Gauss X.jK V W := by
  intro Ω _ _ _ ε X V
  classical
  open GaussDom in
  haveI : (RingHom.ker (redA V X.exp)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hA, hinv, hlt⟩ :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (GaussDom.intA V X.exp) (RingHom.ker (GaussDom.redA V X.exp))
  have hker : ∀ x : GaussDom.intA V X.exp, x ∈ RingHom.ker (GaussDom.redA V X.exp) ↔
      ∀ r, (X.exp x).coeff r ∈ V.nonunits :=
    fun x => (RingHom.mem_ker).trans (GaussDom.redA_eq_zero V X.exp x)
  have hone : ∀ x : GaussDom.intA V X.exp, x ∉ RingHom.ker (GaussDom.redA V X.exp) → W.valuation (x : X.K) = 1 := by
    intro x hx
    have hx0 : (x : X.K) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this]
      exact Ideal.zero_mem _
    have h1 := (W.valuation_le_one_iff _).2 (hA x)
    have h2 := (W.valuation_le_one_iff _).2 (hinv x hx)
    rw [map_inv₀] at h2
    have hv0 : W.valuation (x : X.K) ≠ 0 := by simpa using hx0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)
  have hj3 : ∀ r, (X.exp X.jK).coeff r ∈ V := fun r => by
    obtain ⟨n, hn⟩ := X.j_exp.2.2 r
    rw [hn]
    exact intCast_mem V n
  have hj1 : (X.exp X.jK).coeff (-1) = 1 := X.j_exp.1
  have hj2 : ∀ r : ℚ, r < -1 → (X.exp X.jK).coeff r = 0 := X.j_exp.2.1
  refine ⟨W, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    exact hA ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
  · intro f hf
    have hfi : f ∈ GaussDom.intA V X.exp :=
      (GaussDom.mem_intA V X.exp f).2 (fun r => V.valuation_le_one_iff _ |>.1 (le_of_lt
        ((ValuationSubring.mem_nonunits_iff _).1 (hf r))))
    exact hlt ⟨f, hfi⟩ ((hker _).2 hf)
  · rintro f ⟨hf, r, hr⟩
    apply hone ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
    intro hk
    have := (hker _).1 hk r
    rw [ValuationSubring.mem_nonunits_iff] at this
    exact absurd hr (ne_of_lt this)
  · intro a
    constructor
    · intro ha
      by_contra hnot
      have ha0 : a ≠ 0 := fun h => hnot (h ▸ V.zero_mem)
      have hinvV : a⁻¹ ∈ V := (V.mem_or_inv_mem a).resolve_left hnot
      have hnu : a⁻¹ ∈ V.nonunits := by
        rw [ValuationSubring.mem_nonunits_iff]
        refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_
        intro h1
        apply hnot
        rw [map_inv₀, inv_eq_one] at h1
        exact (V.valuation_le_one_iff a).1 (le_of_eq h1)
      have hm : algebraMap Ω X.K a⁻¹ ∈ GaussDom.intA V X.exp := GaussDom.const_mem V X.exp _ hinvV
      have hk : (⟨_, hm⟩ : GaussDom.intA V X.exp) ∈ RingHom.ker (GaussDom.redA V X.exp) := by
        rw [hker]
        intro r
        show (X.exp (algebraMap Ω X.K a⁻¹)).coeff r ∈ V.nonunits
        rw [GaussDom.coeff_const]
        split_ifs
        · exact hnu
        · exact GaussDom.zero_mem_nonunits V
      have h3 : W.valuation (algebraMap Ω X.K a⁻¹) < 1 := hlt _ hk
      have h4 := (W.valuation_le_one_iff _).2 ha
      have h5 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have h6 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) ≤
          1 * W.valuation (algebraMap Ω X.K a⁻¹) := by gcongr
      rw [h5, one_mul] at h6
      exact absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)
    · intro ha
      exact hA ⟨_, GaussDom.const_mem V X.exp a ha⟩
  · rintro P hP ⟨i0, hne, hi0, hi0'⟩
    have hjA : X.jK ∈ GaussDom.intA V X.exp := (GaussDom.mem_intA V X.exp X.jK).2 hj3
    obtain ⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P :=
      (Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)
    let ι : V →+* GaussDom.intA V X.exp :=
      ((algebraMap Ω X.K).comp V.subtype).codRestrict (GaussDom.intA V X.exp)
        (fun v => GaussDom.const_mem V X.exp v v.2)
    have hx : Polynomial.aeval X.jK P = (GaussDom.intA V X.exp).subtype (P'.eval₂ ι ⟨X.jK, hjA⟩) := by
      rw [Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hx]
    apply hone
    intro hk
    rw [RingHom.mem_ker, Polynomial.hom_eval₂] at hk
    have hc : (GaussDom.redA V X.exp).comp ι =
        (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp
          (IsLocalRing.residue V) := by
      apply RingHom.ext
      intro v
      exact GaussDom.redA_const V X.exp v
    rw [hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hk
    set J := GaussDom.redA V X.exp ⟨X.jK, hjA⟩ with hJdef
    have hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ) := by
      apply HahnSeries.orderTop_eq_of_le
      · rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff]
        have h1 : (⟨(X.exp X.jK).coeff (-1), (GaussDom.mem_intA V X.exp X.jK).1 hjA (-1)⟩ : V) = 1 :=
          Subtype.ext hj1
        rw [h1, map_one]
        exact one_ne_zero
      · intro g hg
        rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff] at hg
        by_contra hlt'
        apply hg
        have h0 : (⟨(X.exp X.jK).coeff g, (GaussDom.mem_intA V X.exp X.jK).1 hjA g⟩ : V) = 0 :=
          Subtype.ext (hj2 g (lt_of_not_ge hlt'))
        rw [h0, map_zero]
    have hQ : P'.map (IsLocalRing.residue V) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun Q => Q.coeff i0) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0
      have hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0 := by
        rw [← hP', Polynomial.coeff_map]
        rfl
      have hu : IsUnit (P'.coeff i0) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩
        show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1
        rw [hPi, mul_inv_cancel₀ hne]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at hc0
      exact hc0 hu
    have hot := GaussDom.orderTop_aeval J hJ _ _ hQ rfl
    rw [hk, HahnSeries.orderTop_zero] at hot
    exact WithTop.top_ne_coe hot

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMemStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
        (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) →
        ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
          (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
          ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
            (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t →
            ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  let : Algebra ℤ_[p] Ω := zpAlg (p := p) (Ω := Ω)
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hAlg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsmul (c : ℤ_[p]) (x : Ω) : c • x = zp Ω c * x := by
    rw [Algebra.smul_def]
    congr 1
    change algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) c) = zp Ω c
    rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hxInt, hxS⟩ ⟨hyInt, hyS⟩
        exact ⟨IsIntegral.add hxInt hyInt, by rw [mul_add]; exact S.add_mem hxS hyS⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hxInt, hxS⟩
        refine ⟨?_, ?_⟩
        · change IsIntegral (O0 p) (c • x)
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hxInt
        · change (p : Ω) ^ v * (c • x) ∈ S
          rw [mul_smul_comm]
          exact S.smul_mem c hxS }
  let U := Submodule.span ℤ_[p] (Set.range fun t => E t / (p : Ω) ^ v)
  have hle : S' ≤ U := by
    rintro y ⟨_, hy⟩
    change (p : Ω) ^ v * y ∈ Submodule.span ℤ_[p] (Set.range E) at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    apply (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2
    refine ⟨c, ?_⟩
    calc
      ∑ t, c t • (E t / (p : Ω) ^ v) = (∑ t, c t • E t) / (p : Ω) ^ v := by
        simp only [Finset.sum_div, smul_div_assoc]
      _ = y := (div_eq_iff hpv).2 (hc.trans (mul_comm _ _))
  have hnoeth : IsNoetherian ℤ_[p] U :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem (j : Fin m) : IsInt (p := p) (f j) ∧ (p : Ω) ^ v * f j ∈ S := by
    change f j ∈ S'
    rw [← hf]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hAlgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    change x ∈ Submodule.span ℤ_[p] (Set.range E) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (hAlg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · apply (hAlg _).2
    have hInv : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) :=
      ((isAlgebraic_natCast p : IsAlgebraic ℤ_[p] (p : Ω)).pow v).inv
    have h := hInv.mul (hAlgS _ (hfmem j).2)
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at h
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsmul]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by simpa only [hsmul] using hμ.symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosureStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  first | exact @GlobalTheory.AlmostEt.QDer.exists_qDer | exact GlobalTheory.AlmostEt.QDer.exists_qDer | (intros; apply GlobalTheory.AlmostEt.QDer.exists_qDer <;> assumption)
end

