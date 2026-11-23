module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnitConjugateNormTwoPowerTwoAdic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.DoubleCosetComm

variable {G : Type} [Group G]

def InDC (J : Subgroup G) (x g : G) : Prop := ∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂

theorem InDC.mul {J : Subgroup G} {x g a b : G} (h : InDC J x g) (ha : a ∈ J) (hb : b ∈ J) :
    InDC J x (a * g * b) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨⟨a, ha⟩ * u, v * ⟨b, hb⟩, by simp [mul_assoc]⟩

theorem InDC.inv {J : Subgroup G} {x g : G} (h : InDC J x g) : InDC J x⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp [mul_assoc]⟩


open Classical in
theorem card_filter_le {J : Subgroup G} {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B)
    (P Q : G → Prop) (ψ : G → G) (h1 : ∀ a ∈ A, P a → InDC J y (ψ a))
    (h2 : ∀ a ∈ A, P a → ∀ k ∈ J, Q (ψ a * k))
    (h3 : ∀ a ∈ A, ∀ a' ∈ A, (ψ a)⁻¹ * ψ a' ∈ J → a⁻¹ * a' ∈ J) :
    (A.filter P).card ≤ (B.filter Q).card := by
  have hex : ∀ a : G, ∃ b : G, a ∈ A → P a → b ∈ B ∧ b⁻¹ * ψ a ∈ J := by
    intro a
    by_cases h : a ∈ A ∧ P a
    · obtain ⟨b, hb, -⟩ := hB.2 _ (h1 a h.1 h.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨1, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose r hr using hex
  refine Finset.card_le_card_of_injOn r ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hb, hj⟩ := hr a ha.1 ha.2
    refine ⟨hb, ?_⟩
    have := h2 a ha.1 ha.2 _ (J.inv_mem hj)
    simpa [mul_assoc] using this
  · intro a ha a' ha' e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have hj := (hr a ha.1 ha.2).2
    have hj' := (hr a' ha'.1 ha'.2).2
    rw [← e] at hj'
    have h4 : (ψ a)⁻¹ * ψ a' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hj) hj'
    exact (hA.2 a' (hA.1 a' ha'.1)).unique ⟨ha.1, h3 a ha.1 a' ha'.1 h4⟩ ⟨ha'.1, by simp⟩

section Theta

variable {J L : Subgroup G} {θ : G → G}
  (hm : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (hi : ∀ x ∈ L, θ (θ x) = x)
  (hK : ∀ k ∈ J ⊓ L, θ k ∈ J) (hL : ∀ g ∈ L, θ g ∈ L)
  (hdc : ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)

include hm in
theorem theta_inv {g : G} (hg : g ∈ L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h1 : θ 1 = 1 := by
    have h := hm 1 L.one_mem 1 L.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h'
  apply eq_inv_of_mul_eq_one_left
  rw [← hm _ hg _ (L.inv_mem hg), mul_inv_cancel, h1]

include hm hi hK hL in
theorem theta_coset {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L) (h : θ a * (θ a')⁻¹ ∈ J) : a⁻¹ * a' ∈ J := by
  have hl : a'⁻¹ * a ∈ L := L.mul_mem (L.inv_mem ha') ha
  have e : θ (a'⁻¹ * a) = θ a * (θ a')⁻¹ := by
    rw [hm _ (L.inv_mem ha') _ ha, theta_inv hm ha']
  have := hK (θ (a'⁻¹ * a)) ⟨e ▸ h, hL _ hl⟩
  rw [hi _ hl] at this
  simpa using J.inv_mem this

include hdc in
theorem InDC.theta {x g : G} (h : InDC J x g) (hg : g ∈ L) : InDC J x (θ g) := by
  obtain ⟨a, ha, b, hb, e⟩ := hdc g hg
  rw [e]
  exact h.mul ha.1 hb.1

include hm hi hK hL hdc in
theorem card_le_inv {x : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x⁻¹ A') (hAL : ∀ a ∈ A, a ∈ L) :
    A.card ≤ A'.card := by
  classical
  have := card_filter_le hA hA' (fun _ => True) (fun _ => True) (fun a => (θ a)⁻¹)
    (fun a ha _ => (InDC.theta hdc (hA.1 a ha) (hAL a ha)).inv) (fun _ _ _ _ _ => trivial)
    (fun a ha a' ha' h => theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa using h))
  simpa using this

open Classical in
include hm hi hK hL hdc in
theorem card_conv_le {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    {z : G} (hz : z ∈ L) :
    (A.filter fun a => InDC J y (a⁻¹ * z)).card ≤ (B.filter fun b => InDC J x (b⁻¹ * z)).card := by
  obtain ⟨k, hk, k', hk', e⟩ := hdc z hz
  refine card_filter_le hA hB _ _ (fun a => z * k' * (θ a)⁻¹) ?_ ?_ ?_
  · intro a ha hP
    have hl := L.inv_mem (hAL a ha)
    have h1 := InDC.theta hdc hP (L.mul_mem hl hz)
    rw [hm _ hl _ hz, theta_inv hm (hAL a ha), e] at h1
    simpa [mul_assoc] using h1.mul (J.inv_mem hk.1) J.one_mem
  · intro a ha _ c hc
    have h1 := InDC.theta hdc (hA.1 a ha) (hAL a ha)
    simpa [mul_assoc] using h1.mul (J.inv_mem hc) (J.inv_mem hk'.1)
  · intro a ha a' ha' h
    exact theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa [mul_assoc] using h)

end Theta


open Classical in
theorem card_pairs {J L : Subgroup G} {y : G} {A B : Finset G} (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L) {z : G} (hz : z ∈ L) :
    ((A ×ˢ B).filter fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))).card =
      (A.filter fun a => InDC J y (a⁻¹ * z)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h1 : InDC J y b := hB.1 b hp.1.2
    simpa [mul_assoc] using h1.mul J.one_mem (J.inv_mem hp.2.1)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' e
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp hp' e
    subst e
    have h4 : b⁻¹ * b' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hp.2.1) hp'.2.1
    have := (hB.2 b' (hB.1 b' hp'.1.2)).unique ⟨hp.1.2, h4⟩ ⟨hp'.1.2, by simp⟩
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨b, ⟨hb, hj⟩, -⟩ := hB.2 _ ha.2
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨ha.1, hb⟩, ?_, L.mul_mem (L.inv_mem hz) (L.mul_mem (hAL a ha.1) (hBL b hb))⟩
    simpa [mul_assoc] using J.inv_mem hj

theorem dcOp_comm_and_card : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  classical
  intro G W _ _ _ J L χ x y A B A' F _ hχ ⟨θ, hL, hm, hi, hK, hdc⟩ hAL hBL hAL' hA hB hA' hF
  refine ⟨?_, le_antisymm (card_le_inv hm hi hK hL hdc hA hA' hAL)
    (card_le_inv hm hi hK hL hdc hA' (by rwa [inv_inv]) hAL')⟩
  have hFK : ∀ g g' : G, (g : G ⧸ (J ⊓ L)) = g' → ∀ h, F (h * g) = F (h * g') := by
    intro g g' e h
    rw [QuotientGroup.eq] at e
    have := hF ⟨_, e.1⟩ (h * g)
    rw [hχ ⟨_, e.1⟩ e.2] at this
    simpa [mul_assoc] using this.symm
  have hms : (A ×ˢ B).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) =
      (B ×ˢ A).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hz : z ∈ L
      · have e1 := card_pairs (A := A) hB hAL hBL hz
        have e2 := card_pairs (A := B) hA hBL hAL hz
        have e3 := le_antisymm (card_conv_le hm hi hK hL hdc hA hB hAL hz)
          (card_conv_le hm hi hK hL hdc hB hA hBL hz)
        have := e1.trans (e3.trans e2.symm)
        rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val] at this
        convert this
      · have hz' : ∀ C D : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ D, a ∈ L) →
            Multiset.filter (fun p : G × G => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) (C ×ˢ D).val = 0 := by
          intro C D hC hD
          rw [Multiset.filter_eq_nil]
          intro p hp e
          rw [Finset.mem_val, Finset.mem_product] at hp
          rw [QuotientGroup.eq] at e
          apply hz
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (hC _ hp.1) (hD _ hp.2)) (L.inv_mem e.2)
        rw [hz' A B hAL hBL, hz' B A hBL hAL]
  funext h
  have key : ∀ C D : Finset G, dcOp C (dcOp D F) h =
      (((C ×ˢ D).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L)))).map fun q => F (h * q.out)).sum := by
    intro C D
    rw [Multiset.map_map]
    change _ = ∑ p ∈ C ×ˢ D, _
    rw [Finset.sum_product]
    simp only [dcOp, Function.comp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
    exact hFK _ _ (QuotientGroup.out_eq' _).symm h
  rw [key, key, hms]

end GlobalTheory.DoubleCosetComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertConj

theorem conj_mem_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    (h : IsInertAt (maximalRealSubfield E) E v P) {x : 𝓞 E} (hx : x ∈ P.asIdeal) :
    IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal := by
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have key : P.asIdeal ≤ Ideal.comap
      (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) P.asIdeal := by
    conv_lhs => rw [← h']
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change IsCMField.ringOfIntegersComplexConj E _ ∈ _
    rw [AlgEquiv.commutes, ← h']
    exact Ideal.mem_map_of_mem _ hs
  exact key hx

theorem exists_conj_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  intro E _ _ _ _ v P h
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv P P := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv P _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
      algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ P.asIdeal ^ 2 := by
    by_contra hn
    push Not at hn
    have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ P.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (a : E)) =
      P.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  refine ⟨σ, algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E), σ2', ?_, σ3,
    ?_, ?_, ?_⟩
  · intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous P (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2', ReciprocityTheory.ChartRestriction.G.FD.cc]
  · obtain ⟨x, hx⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact P.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hx)
  · change σ _ = _
    rw [σ2', cc_algebraMap]
  · unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq P hs1 hs2

end GlobalTheory.InertConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodOrdinaryModelAtTwoCmLatticeSevenModEight
section
namespace GlobalTheory.ThLoc

theorem goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight : Formalism.L2.Th1.Top.GoodModelTwo :=
  GlobalTheory.ThLoc.GoodTwo.goodModelTwo

end GlobalTheory.ThLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.FormsDescent

section General

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

def coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) : V :=
  ∑ i, φ (b.repr v i) • b i

theorem repr_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) (i : ι) :
    b.repr (coordMap F b φ v) i = φ (b.repr v i) := by
  unfold coordMap
  rw [b.repr_sum_self]

theorem coordMap_sum (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) {α : Type} [Fintype α]
    (x : α → K) (w : α → V) (hw : ∀ a i, b.repr (w a) i ∈ F) :
    coordMap F b φ (∑ a, x a • w a) = ∑ a, φ (x a) • w a := by
  apply b.repr.injective
  ext i
  rw [repr_coordMap]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply', Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := φ.map_smul (⟨b.repr (w a) i, hw a i⟩ : F) (x a)
  simp only [Subfield.smul_def, smul_eq_mul] at h
  rw [mul_comm (x a), h, mul_comm]

theorem map_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (g : V →ₗ[K] V)
    (hg : ∀ i j, b.repr (g (b j)) i ∈ F) (v : V) :
    g (coordMap F b φ v) = coordMap F b φ (g v) := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h1, coordMap_sum F b φ _ _ (fun a i => hg i a)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordMap, map_sum, map_smul]

theorem exists_retraction (F : Subfield K) :
    ∃ φ : K →ₗ[F] K, (∀ x, φ x ∈ F) ∧ ∀ x ∈ F, φ x = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F K)
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  refine ⟨(Algebra.linearMap F K).comp g, fun x => (g x).2, fun x hx => ?_⟩
  have h := LinearMap.congr_fun hg ⟨x, hx⟩
  have h' : g x = ⟨x, hx⟩ := h
  show ((g x : F) : K) = x
  rw [h']

end General

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem hasRatBasis_of_act
    (h : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) : S.HasRatBasis := by
  classical
  haveI : Module.Finite (cmMax K) K := Module.Finite.of_restrictScalars_finite ℚ (cmMax K) K
  let e := Module.finBasis (cmMax K) K
  let s : Set S.Forms := {f | S.IsRat (f : S.Cl → S.V)}
  have hs : ⊤ ≤ Submodule.span K s := by
    intro f _
    let φ : Fin (Module.finrank (cmMax K) K) → (K →ₗ[cmMax K] K) :=
      fun k => (Algebra.linearMap (cmMax K) K).comp (e.coord k)
    let g : Fin (Module.finrank (cmMax K) K) → S.Forms := fun k =>
      ⟨fun c => coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c), fun c γ => by
        rw [map_coordMap (cmMax K) S.bV (φ k) (S.ρ c γ) (h c γ), f.2 c γ]⟩
    have hf : f = ∑ k, e k • g k := by
      apply Subtype.ext
      funext c
      apply S.bV.repr.injective
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
        Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, g, repr_coordMap]
      conv_lhs => rw [← e.sum_repr (S.bV.repr ((f : S.Cl → S.V) c) i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
      rfl
    rw [hf]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro c i
    show S.bV.repr (coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c)) i ∈ cmMax K
    rw [repr_coordMap]
    exact (e.coord k _).2
  let b := Module.Basis.ofSpan hs
  refine ⟨b.reindex (b.indexEquiv (Module.finBasis K S.Forms)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset hs ⟨_, rfl⟩

theorem repr_mem_of_isRat (h : S.HasRatBasis) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V)) (a : Fin S.dim) :
    S.basis.repr f a ∈ cmMax K := by
  have hb : ∀ i, S.IsRat (S.basis i : S.Cl → S.V) := by
    have : S.basis = h.choose := by
      unfold CSD.basis
      exact dif_pos h
    rw [this]
    exact h.choose_spec
  obtain ⟨φ, h1, h2⟩ := exists_retraction (cmMax K)
  have key : f = ∑ a, φ (S.basis.repr f a) • S.basis a := by
    apply Subtype.ext
    funext c
    have e1 : (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
      conv_lhs => rw [← S.basis.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    have e2 : coordMap (cmMax K) S.bV φ ((f : S.Cl → S.V) c) = (f : S.Cl → S.V) c := by
      apply S.bV.repr.injective
      ext i
      rw [repr_coordMap, h2 _ (hf c i)]
    rw [← e2, e1, coordMap_sum (cmMax K) S.bV φ _ _ (fun a i => hb a c i)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have : S.basis.repr f a = φ (S.basis.repr f a) := by
    conv_lhs => rw [key]
    rw [S.basis.repr_sum_self]
  rw [this]
  exact h1 _

end GlobalTheory.FormsDescent

namespace GlobalTheory

theorem forms_rat : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K), ((∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) → S.HasRatBasis) ∧ ∀ T : Module.End K S.Forms, S.HasRatBasis → (∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat ((T f : S.Forms) : S.Cl → S.V)) → ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro K _ _ _ S
  refine ⟨FormsDescent.hasRatBasis_of_act S, fun T h hT a b => ?_⟩
  rw [LinearMap.toMatrix_apply]
  refine FormsDescent.repr_mem_of_isRat S h _ (hT _ ?_) a
  have : S.basis = h.choose := by
    unfold CSD.basis
    exact dif_pos h
  rw [this]
  exact h.choose_spec b

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOne
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := _root_.GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := _root_.GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite F E χ hχ hdeg hinf
  ext1 x
  have hfact := (_root_.GlobalTheory.HeckeSplit.continuous_char_factor E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets
section
open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
end

