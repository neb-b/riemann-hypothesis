module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormaliseAtSmoothPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothNormalise

theorem inv_mem_of_isField {κ' : Type} [Field κ'] {O : Subring κ'} (hF : IsField O) {f : κ'}
    (hf : f ∈ O) (h0 : f ≠ 0) : f⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel (a := (⟨f, hf⟩ : O)) (fun e => h0 (congrArg Subtype.val e))
  have : f * (y : κ') = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right this]; exact y.2

theorem const_of_isField {κ' : Type} [Field κ'] [Algebra ℂ κ'] {O : Subring κ'}
    (hO : IsLocModel (algebraMap ℂ κ') O) (hR : RatRes (algebraMap ℂ κ') O) (hF : IsField O) :
    ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α := by
  have hc : ∀ f ∈ O, ∃ α : ℂ, f = algebraMap ℂ κ' α := by
    intro f hf
    obtain ⟨α, hα, h⟩ := hR f hf
    refine ⟨α, ?_⟩
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · by_contra hne
      exact h (inv_mem_of_isField hF hα (sub_ne_zero.2 hne))
  intro x
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
  obtain ⟨α, rfl⟩ := hc a ha
  obtain ⟨β, rfl⟩ := hc b hb
  refine ⟨α / β, ?_⟩
  rw [map_div₀, eq_div_iff hb0, e]

theorem top_model_of_const {κ' : Type} [Field κ'] [Algebra ℂ κ']
    (hc : ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α) :
    ∃ (hB : IsLocModel (algebraMap ℂ κ') ⊤), RatRes (algebraMap ℂ κ') ⊤ ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal (⊤ : Subring κ') = Ideal.span (Set.range (Fin.elim0 : Fin 0 → (⊤ : Subring κ')))) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')) := by
  have hsurj : Function.Surjective ((algebraMap ℂ κ').codRestrict (⊤ : Subring κ') (fun _ => trivial)) :=
    fun x => by obtain ⟨α, hα⟩ := hc x; exact ⟨α, Subtype.ext hα.symm⟩
  let hB : IsLocModel (algebraMap ℂ κ') ⊤ :=
    { const_mem := fun _ => trivial
      isLocalRing := (Subring.topEquiv (R := κ')).symm.isLocalRing
      essFiniteType := (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
      frac := fun f => ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩ }
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro r _
    obtain ⟨α, hα⟩ := hc r
    exact ⟨α, by rw [hα, sub_self]; exact nonUnit_zero _⟩
  · letI := hB.isLocalRing
    have hfield : IsField (⊤ : Subring κ') := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      have ha' : (a : κ') ≠ 0 := fun e => ha (Subtype.ext e)
      exact ⟨⟨(a : κ')⁻¹, trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield
  · have hb : Function.Bijective (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))) := by
      refine ⟨fun P Q e => ?_, fun x => ?_⟩
      · rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q] at e ⊢
        simp only [MvPolynomial.eval₂Hom_C] at e
        exact congrArg _ (((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem).injective e)
      · obtain ⟨α, hα⟩ := hsurj x
        exact ⟨MvPolynomial.C α, by simpa using hα⟩
    letI := (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).toAlgebra
    exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)
  · have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_empty_type, ⟨fun x => ?_⟩⟩
    obtain ⟨α, rfl⟩ := hc x
    exact isAlgebraic_algebraMap (algebraMap ℂ (Algebra.adjoin ℂ (Set.range (fun i : Fin 0 => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')))) α)

theorem inv_not_mem {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ'))
    {B : Subring κ'} (hBF : B ≤ F.ring.toSubring) {f : κ'} (hf : f ≠ 0) (hp : 0 < F.ord f) :
    f⁻¹ ∉ B := by
  intro h
  have := (F.ord_nonneg_iff (inv_ne_zero hf)).2 (hBF h)
  rw [F.ord_inv] at this
  omega

theorem nonUnit_sub {κ' : Type} [Field κ'] {B : Subring κ'} [IsLocalRing B] {x y : κ'}
    (hx : NonUnit B x) (hy : NonUnit B y) : NonUnit B (x - y) := by
  have hx' := (nonUnit_iff (R := B) ⟨x, hx.1⟩).1 hx
  have hy' := (nonUnit_iff (R := B) ⟨y, hy.1⟩).1 hy
  have h := (nonUnit_iff (R := B) (⟨x, hx.1⟩ - ⟨y, hy.1⟩)).2
  exact h ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.sub_mem _
    ((IsLocalRing.mem_maximalIdeal _).2 hx') ((IsLocalRing.mem_maximalIdeal _).2 hy')))

theorem normalise_at_smooth_point : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (O : Subring κ') (l : ℕ) (a : Fin l → κ'),
  IsLocModel (algebraMap ℂ κ') O → RatRes (algebraMap ℂ κ') O → a ≠ 0 →
  ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B) (r : ℕ) (τ : Fin r → B),
    RatRes (algebraMap ℂ κ') B ∧ Dominates (RingHom.id κ') B O ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) ∧ ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ B := by
  classical
  intro κ' _ _ O l a hO hR ha
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  by_cases hF : IsField O
  · have hc := const_of_isField hO hR hF
    obtain ⟨hB, h1, h2, h3, h4⟩ := top_model_of_const hc
    refine ⟨⊤, hB, 0, Fin.elim0, h1, fun f hf => ⟨trivial, fun hn => ?_⟩, h2, h3, h4, j, hj,
      fun _ => trivial⟩
    refine ⟨trivial, Or.inl ?_⟩
    by_contra h0
    rcases hn.2 with h | h
    · exact h0 h
    · exact h (inv_mem_of_isField hF hf h0)
  · obtain ⟨F, hFO, hpos⟩ := GlobalTheory.T.exists_place_dominating_local_domain_complex O hO hF
    obtain ⟨j₀, hj₀, hdiv⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ F.ring := by
      obtain ⟨j₀, hj₀s, hmin⟩ := (Finset.univ.filter (fun i => a i ≠ 0)).exists_min_image
        (fun i => F.ord (a i)) ⟨j, by simpa using hj⟩
      have hj₀ : a j₀ ≠ 0 := (Finset.mem_filter.1 hj₀s).2
      refine ⟨j₀, hj₀, fun i => ?_⟩
      by_cases hi : a i = 0
      · rw [hi, zero_div]; exact zero_mem _
      · have hne : a i / a j₀ ≠ 0 := div_ne_zero hi hj₀
        rw [← F.ord_nonneg_iff hne, div_eq_mul_inv, F.ord_mul hi (inv_ne_zero hj₀), F.ord_inv]
        have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        omega
    letI : Algebra ℂ O := ((algebraMap ℂ κ').codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ O).1 inferInstance
    let S : Finset κ' := σ.image (fun x : O => (x : κ')) ∪ Finset.univ.image (fun i => a i / a j₀)
    have hS : ∀ x ∈ S, x ∈ F.ring := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
        exact hFO _ y.2
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdiv i
    obtain ⟨A, hAs, hAF, hSA, hAfrac⟩ := _root_.GlobalTheory.FieldPair.Place.exists_smooth_subalgebra F S hS
    obtain ⟨B, hB, hRB, hAB, hBF, hsm⟩ := _root_.GlobalTheory.FieldPair.exists_locRing_closedPoint_centre F A hAs hAF hAfrac
    obtain ⟨r, τ, hm, het, htr⟩ := GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex B hB hRB hsm
    have hSB : ∀ x ∈ S, x ∈ B := fun x hx => hAB (hSA x hx)
    letI := hB.isLocalRing
    letI := hO.isLocalRing

    have hadj : ∀ t : O, t ∈ Algebra.adjoin ℂ (σ : Set O) → (t : κ') ∈ B := by
      intro t ht
      induction ht using Algebra.adjoin_induction with
      | mem x hx => exact hSB _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      | algebraMap α => exact hB.const_mem α
      | add x y _ _ hx hy => exact B.add_mem hx hy
      | mul x y _ _ hx hy => exact B.mul_mem hx hy

    have hnon : ∀ f ∈ B, NonUnit O f → NonUnit B f := by
      intro f hfB hn
      refine ⟨hfB, ?_⟩
      by_cases h0 : f = 0
      · exact Or.inl h0
      · refine Or.inr (inv_not_mem F hBF h0 (hpos ⟨f, hn.1⟩ ?_ h0))
        exact (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := O) ⟨f, hn.1⟩).1 hn)

    have hunit : ∀ t : O, IsUnit t → (t : κ') ∈ B → (t : κ')⁻¹ ∈ B := by
      intro t ht htB
      by_contra hinv
      have htn : NonUnit B (t : κ') := ⟨htB, Or.inr hinv⟩
      obtain ⟨α, hα⟩ := hR t t.2
      have hαB : algebraMap ℂ κ' α ∈ B := hB.const_mem α
      have hu : NonUnit B ((t : κ') - algebraMap ℂ κ' α) := hnon _ (B.sub_mem htB hαB) hα
      have hc : NonUnit B (algebraMap ℂ κ' α) := by
        simpa using nonUnit_sub htn hu
      by_cases hα0 : α = 0
      · subst hα0
        simp only [map_zero, sub_zero] at hα
        exact (nonUnit_iff (R := O) t).1 hα ht
      · rcases hc.2 with h | h
        · exact hα0 ((map_eq_zero_iff _ (algebraMap ℂ κ').injective).1 h)
        · exact h (by rw [← map_inv₀]; exact hB.const_mem _)
    refine ⟨B, hB, r, τ, hRB, fun f hf => ?_, hm, het, htr, j₀, hj₀,
      fun i => hSB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
    obtain ⟨t, htA, htu, hft⟩ := hσ ⟨f, hf⟩
    have htB := hadj t htA
    have hfB : f ∈ B := by
      have h1 := hadj _ hft
      have h2 := hunit t htu htB
      have ht0 : (t : κ') ≠ 0 := fun e => htu.ne_zero (Subtype.ext e)
      have : f = (f * (t : κ')) * (t : κ')⁻¹ := by field_simp
      rw [this]
      exact B.mul_mem h1 h2
    exact ⟨hfB, hnon f hfB⟩

end GlobalTheory.SmoothNormalise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagBundleMetricLine
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem existsUnique_of_openImmersion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (s₀ : Y₀ ⟶ M.X) (s : Y ⟶ M.X) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), IsOpenImmersion i → i ≫ s = s₀ → m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ) → ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₂ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ b N _ _ r w j c M Y₀ Y i s₀ s σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ _ his hsq hfac hU S x o₁ o₁' m₁ ψ₁
    hp hisog htj
  have comp_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
      {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
      {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
      ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
    have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
      constructor
      · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
      · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
    have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
      intro c
      rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
    have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
      intro y
      rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
    exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩
  obtain ⟨y₀, ⟨hy₀, m₀, m₂, hsq₀⟩, huniq⟩ := hU S x o₁ o₁' m₁ ψ₁ hp hisog htj
  obtain ⟨a, ha⟩ := comp_map m₀ m
  obtain ⟨b, hb⟩ := comp_map m₂ m'
  refine ⟨y₀ ≫ i, ⟨by rw [Category.assoc, his, hy₀], a, b, ?_⟩, ?_⟩
  · rw [ha, hb]
    rw [Category.assoc, hsq, ← Category.assoc, hsq₀, Category.assoc]
  · rintro y ⟨hy, n₀, n₂, hsqn⟩
    obtain ⟨f₀, rfl⟩ := hfac S y hp
    obtain ⟨k₀, hk₀⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₀ m
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₂ m'
    have hsqk : k₀.φ ≫ ψ₀.left = ψ₁.left ≫ k₂.φ := by
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hk₀, hsqn, ← hk₂]
      · rw [Category.assoc, Over.w ψ₀, k₀.cart.1.w, Category.assoc, k₂.cart.1.w, ← Category.assoc, Over.w ψ₁]
    have e := huniq f₀ ⟨by rw [← his, ← Category.assoc]; exact hy, k₀, k₂, hsqk⟩
    rw [e]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.DVR

theorem pelOK_of_isPullDeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R'), Function.Injective φ → ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o' : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o' := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hP R' _ _ _ φ hφ D' ⟨hD⟩
  letI := H.starRing
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  letI inst : Module (𝓞 E) D'.toPre.X := hD.xe.module (𝓞 E)
  have hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y := fun a y => hD.xe.apply_symm_apply _
  obtain ⟨o', ho⟩ := ArcPull.exists_oAct hD hG hφ o hx
  obtain ⟨hpq, hp1, hw, hF⟩ := hP
  refine ⟨inst, o', hpq, hp1, ArcPull.traceFormTwistIso_of_pullback hD hφ hx ho hw, fun F _ _ _ => ?_⟩
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (ArcPull.fracMap hφ)).toAlgebra
  have hc : ArcPull.Compat φ F := fun x =>
    congrArg (algebraMap (FractionRing R') F) (ArcPull.fracMap_algebraMap hφ x)
  obtain ⟨hL, hT⟩ := hF F
  refine ⟨fun τ => ?_, fun ζ hζ hζ' => ?_⟩
  · obtain ⟨n, hn, hn'⟩ := hL τ
    refine ⟨n, (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct o.onB.toRingAct) _ (pull_grp hD) ho F _ τ n).2 ?_, ?_⟩
    · rw [← spMap_comp, show ((algebraMap (FractionRing R') F).comp (algebraMap R' _)).comp φ =
        (algebraMap (FractionRing R) F).comp (algebraMap R _) from RingHom.ext fun r => (hc r).symm]
      exact hn
    · rw [(({ hD.xe with map_smul' := hx } : D'.toPre.X ≃ₗ[𝓞 E] D.toPre.X)).finrank_eq]
      exact hn'
  · obtain ⟨I, hI⟩ := hT ζ hζ hζ'
    exact ⟨ArcPull.pullTate hG hD hx ho D.tau_bimult D'.tau_bimult hc I, hI⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

def isoVal {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
    [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B₁.left) → M₁.ι) (J' : (Z ⟶ B.left) → M.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
    fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)))

def IsNormIso {R : Type} [CommRing R] [IsDomain R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over (Sp R)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) : Prop :=
  ∀ z J J', Good M₁ z J → Good M z J' → isoVal w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z J J' = 1

def PeriodRel {o V V₁ W : Type} [CommRing o] [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W]
    [IsLocalRing W] (D : DegPre V) (T : TautBase o W) (f₁ : V →+* V₁) (κ₁ : W →+* V₁) {B' : Over (Sp V₁)} [GrpObj B']
    {β₂ : (G2 B').left ⟶ (G2 D.P.A).left} {β₂' : (G2 B').left ⟶ (G2 T.B).left}
    (w : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (c : (Fin T.r → ℤ) ≃+ D.X)
    (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (n : ℕ) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ) :
    Prop :=
  ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ → ∀ a b z J J', Good T.M.L z J → Good D.P.L z J' →
    val (D.tau (c a) (c b)) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn (q a b)) *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
        val (T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J)

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicSectionsRegularAbelianVariety
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodicSecAlg

open GlobalTheory.CxPts GlobalTheory.HolUnifSec

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (M : LB A.left), M.IsLB → ∀ σ : M.ι → (Fin g → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (σ i) (pre u.ex (M.U i))) →
    (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (M.U i), σ i (z + l) = σ i z) →
    (∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j), σ i z = val u.ex _ (M.g i j).val z * σ j z) →
    ∀ i, IsReg u.ex (M.U i) (σ i) := by
  intro A _ g L u hA M hM σ hσ hper hcomp
  classical
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then σ i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = σ i z := fun i z hz => by
    have := hper i ⟨_, sub_mem_of_pt_eq u (hr (pt u z))⟩ z hz
    simp only [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : σ i z = gv _ _ M i j (pt u z) * σ j z := hcomp i j z hij
      rw [hs i z hi, hs j z hj, e]
    · exact (hσ i).congr fun z hz => hs i z hz
  obtain ⟨τ, hτ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  intro i
  exact ⟨τ.f i, fun z hz => ((congrFun₂ (congrArg Subtype.val hτ) i (pt u z)).trans (hs i z hz)).symm⟩

end GlobalTheory.PeriodicSecAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareGlueLineBundleOfLocalGenerators
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PinchLift

theorem ratio_tele {G : Type*} [CommGroup G] (a b c : G) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  rw [mul_comm c, ← _root_.mul_assoc, mul_comm a b⁻¹, mul_inv_cancel_right, mul_comm]

theorem ratio_cancel_left {G : Type*} [CommGroup G] (w a b : G) : a * b⁻¹ = w * a * (w * b)⁻¹ := by
  rw [mul_inv, ← _root_.mul_assoc, mul_comm w a, mul_inv_cancel_right]

theorem assemble : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z) (hL' : L'.IsLB) (hLZ : LZ.IsLB) (w : LB.Iso (L'.pull i') (LZ.pull p')), w.IsGen → (∀ x : X, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), x ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ) → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = cls L' hL' ∧ GlobalTheory.CechPic.pull i e = cls LZ hLZ := by
  intro X X' Z Z' p i i' p' hsq hG L' LZ hL' hLZ w _ hloc
  have hc : i' ≫ p = p' ≫ i := hsq.w
  have hpt : ∀ z : Z', i (p' z) = p (i' z) := fun z => (congrArg (fun q => q z) hc).symm
  choose W s' sZ hxW hs' hsZ hM using hloc
  have r'e := fun x y => _root_.GlobalTheory.PinchLift.exists_ratio_unit _ L' hL' _ _ (s' y) (s' x) (hs' y) (hs' x)
  choose r' hr' using r'e
  have rZe := fun x y => _root_.GlobalTheory.PinchLift.exists_ratio_unit _ LZ hLZ _ _ (sZ y) (sZ x) (hsZ y) (hsZ x)
  choose rZ hrZ using rZe
  have le' : ∀ x y : X, p ⁻¹ᵁ (W x ⊓ W y) ≤ p ⁻¹ᵁ W y ⊓ p ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have leZ : ∀ x y : X, i ⁻¹ᵁ (W x ⊓ W y) ≤ i ⁻¹ᵁ W y ⊓ i ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have ge := fun x y => _root_.GlobalTheory.PinchLift.exists_unit_of_glues _ _ _ _ p i i' p' hc hG (W x ⊓ W y) (res (le' x y) (r' x y)) (res (leZ x y) (rZ x y)) (by
    intro z hz
    have hz' : i (p' z) ∈ W x ⊓ W y := (hpt z).symm ▸ hz
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
    obtain ⟨j, hj⟩ := exists_chart hLZ (p' z)
    rw [gm_res _ z _ hz, gm_res _ z _ hz', hr' x y Z' i' z k hk hz.2 hz.1, hrZ x y Z' p' z j hj hz'.2 hz'.1,
      hM y z j k hj hk hz'.2 hz.2, hM x z j k hj hk hz'.1 hz.1]
    exact ratio_cancel_left _ _ _)
  choose g hgp hgi using ge
  have Gp : ∀ x y (t : X') (k : L'.ι), p t ∈ W x → p t ∈ W y → t ∈ L'.U k →
      gm p t (W x ⊓ W y) (g x y) = gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W y) (s' y k) * (gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W x) (s' x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgp x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ p ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hr' x y X' (𝟙 X') t k hk hy hx]
  have Gi : ∀ x y (t : Z) (k : LZ.ι), i t ∈ W x → i t ∈ W y → t ∈ LZ.U k →
      gm i t (W x ⊓ W y) (g x y) = gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W y) (sZ y k) * (gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W x) (sZ x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgi x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ i ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hrZ x y Z (𝟙 Z) t k hk hy hx]
  let E : LB X := ⟨X, W, g⟩
  have hE : E.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩, fun x => ?_, fun x y z => ?_⟩
    · refine _root_.GlobalTheory.PinchLift.unit_eq_of_germs_glues _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_one, gm_res _ t _ ht]
        exact (Gp x x t k ht ht hk).trans (mul_inv_cancel _)
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_one, gm_res _ t _ ht]
        exact (Gi x x t k ht ht hk).trans (mul_inv_cancel _)
    · refine _root_.GlobalTheory.PinchLift.unit_eq_of_germs_glues _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm p t (W x ⊓ W y) (g x y) * gm p t (W y ⊓ W z) (g y z) = gm p t (W x ⊓ W z) (g x z)
        rw [Gp x y t k ht.1.1 ht.1.2 hk, Gp y z t k ht.1.2 ht.2 hk, Gp x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm i t (W x ⊓ W y) (g x y) * gm i t (W y ⊓ W z) (g y z) = gm i t (W x ⊓ W z) (g x z)
        rw [Gi x y t k ht.1.1 ht.1.2 hk, Gi y z t k ht.1.2 ht.2 hk, Gi x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p (pull_isLB hE p)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ p L' X W g s' hs' Gp))
  · rw [← cls_pull hE i (pull_isLB hE i)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ i LZ X W g sZ hsZ Gi))

end GlobalTheory.PinchLift
end
end

