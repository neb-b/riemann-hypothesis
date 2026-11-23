module

public import Formalism.LogFactorialIndices.Bundle0001
public import Lemmata.GeneralBFactSecondFurther.Imports
public import Mathlib

@[expose] public section

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
section
noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

namespace LatticeIndexLength

section SlopeTestRemainingChoices

theorem length_quot_ne_top {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    (d : O) (hd : d ≠ 0) (N : Submodule O M) (hN : ∀ m : M, d • m ∈ N) :
    Module.length O (M ⧸ N) ≠ ⊤ := by
  let I : Ideal O := Ideal.span {d}
  have hle : I • (⊤ : Submodule O M) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact N.smul_mem _ (hN m)
  refine ne_top_of_le_ne_top ?_
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))
  have h1 : IsFiniteLength O (O ⧸ I) :=
    isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h1
  obtain ⟨_, h1a⟩ := h1
  have : IsArtinianRing (O ⧸ I) := isArtinian_of_tower O h1a
  have : Module.Finite (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))
  have : IsArtinian (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) := inferInstance
  have : IsArtinian O (M ⧸ I • (⊤ : Submodule O M)) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem length_quotient_tower_add {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (D E P : Submodule O X) (hDE : D ≤ E) (hEP : E ≤ P) :
    Module.length O (P ⧸ D.comap P.subtype) =
      Module.length O (E ⧸ D.comap E.subtype) + Module.length O (P ⧸ E.comap P.subtype) := by
  let f : (E ⧸ D.comap E.subtype) →ₗ[O] (P ⧸ D.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hEP) (by intro x hx; simpa using hx)
  let g : (P ⧸ D.comap P.subtype) →ₗ[O] (P ⧸ E.comap P.subtype) :=
    Submodule.factor (Submodule.comap_mono hDE)
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H e => ?_
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  · exact Submodule.factor_surjective _
  · intro y
    induction y using Submodule.Quotient.induction_on with | H p => ?_
    rw [show g (Submodule.Quotient.mk p) = Submodule.Quotient.mk p from Submodule.factor_mk _ p,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hp
      exact ⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | H e => ?_
      simp only [f, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.eq, Submodule.mem_comap] at hx
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion] at hx
      have : (p : X) = (e : X) - ((e : X) - p) := by abel
      rw [this]
      exact E.sub_mem e.2 (hDE hx)

end SlopeTestRemainingChoices

section Sat

variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]

theorem exists_smul_mem_of_span (B : Submodule O X) (hB : Submodule.span K (B : Set X) = ⊤)
    (x : X) : ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
  first | exact Bl.general_b_fact_second''.goal1 .. | (apply Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB x | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X | exact @Bl.general_b_fact_second''.goal1 O K | exact @Bl.general_b_fact_second''.goal1 O

theorem exists_smul_le (A B : Submodule O X) (hA : A.FG)
    (hB : Submodule.span K (B : Set X) = ⊤) : ∃ d : O, d ≠ 0 ∧ ∀ a ∈ A, d • a ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose f hf0 hf using fun x => exists_smul_mem_of_span (K := K) B hB x
  refine ⟨∏ x ∈ s, f x, Finset.prod_ne_zero_iff.2 (fun x _ => hf0 x), ?_⟩
  intro a ha
  have h : Submodule.span O (s : Set X) ≤ B.comap ((∏ x ∈ s, f x) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hx)
    show ((∏ x ∈ s, f x) • LinearMap.id : X →ₗ[O] X) x ∈ B
    rw [LinearMap.smul_apply, LinearMap.id_apply, hc, mul_comm, mul_smul]
    exact B.smul_mem _ (hf x)
  exact h ha

theorem exists_smul_mem_inf_three (P Q₁ Q₂ Q₃ : Submodule O X) (hP : P.FG)
    (h₁ : Submodule.span K (Q₁ : Set X) = ⊤) (h₂ : Submodule.span K (Q₂ : Set X) = ⊤)
    (h₃ : Submodule.span K (Q₃ : Set X) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ p ∈ P, d • p ∈ Q₁ ⊓ Q₂ ⊓ Q₃ := by
  obtain ⟨d₁, hd₁, e₁⟩ := exists_smul_le P Q₁ hP h₁
  obtain ⟨d₂, hd₂, e₂⟩ := exists_smul_le P Q₂ hP h₂
  obtain ⟨d₃, hd₃, e₃⟩ := exists_smul_le P Q₃ hP h₃
  refine ⟨d₁ * d₂ * d₃, mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₃, fun p hp => ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show d₁ * d₂ * d₃ = (d₂ * d₃) * d₁ by ring, mul_smul]; exact Q₁.smul_mem _ (e₁ p hp)
  · rw [show d₁ * d₂ * d₃ = (d₁ * d₃) * d₂ by ring, mul_smul]; exact Q₂.smul_mem _ (e₂ p hp)
  · rw [mul_smul]; exact Q₃.smul_mem _ (e₃ p hp)

end Sat

section Main

theorem len_ne_top {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] (P D : Submodule O X) (hP : P.FG) (d : O) (hd : d ≠ 0)
    (h : ∀ p ∈ P, d • p ∈ D) : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
  have : Module.Finite O P := Module.Finite.iff_fg.2 hP
  refine length_quot_ne_top d hd _ (fun m => ?_)
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
  exact h m m.2

theorem idx_eq_sub {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (P Q D : Submodule O X) (hD : D ≤ P ⊓ Q)
    (hP : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤)
    (hQ : Module.length O (Q ⧸ D.comap Q.subtype) ≠ ⊤) :
    idx O X P Q = ((Module.length O (P ⧸ D.comap P.subtype)).toNat : ℤ) -
      ((Module.length O (Q ⧸ D.comap Q.subtype)).toNat : ℤ) := by
  have eP := length_quotient_tower_add D (P ⊓ Q) P hD inf_le_left
  have eQ := length_quotient_tower_add D (P ⊓ Q) Q hD inf_le_right
  have cP : Q.comap P.subtype = (P ⊓ Q).comap P.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have cQ : P.comap Q.subtype = (P ⊓ Q).comap Q.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  unfold idx qlen
  rw [cP, cQ]
  rw [eP] at hP ⊢
  rw [eQ] at hQ ⊢
  obtain ⟨h1, h2⟩ := WithTop.add_ne_top.1 hP
  obtain ⟨_, h3⟩ := WithTop.add_ne_top.1 hQ
  rw [ENat.toNat_add h1 h2, ENat.toNat_add h1 h3]
  push_cast
  ring

end Main

end LatticeIndexLength

open LatticeIndexLength

theorem lattice_quotient_finite : LatFinite := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B hA hB
  obtain ⟨d, hd, h⟩ := exists_smul_le (K := K) A B hA.1 hB.2
  exact len_ne_top A B hA.1 d hd h

theorem lattice_index_add : IdxAdd := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B C hA hB hC
  let D := A ⊓ B ⊓ C
  have fin : ∀ P : Submodule O X, IsLat O K X P → Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
    intro P hP
    obtain ⟨d, hd, h⟩ := exists_smul_mem_inf_three (K := K) P A B C hP.1 hA.2 hB.2 hC.2
    exact len_ne_top P D hP.1 d hd h
  have hAB : D ≤ A ⊓ B := inf_le_left
  have hBC : D ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hAC : D ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [idx_eq_sub A C D hAC (fin A hA) (fin C hC), idx_eq_sub A B D hAB (fin A hA) (fin B hB),
    idx_eq_sub B C D hBC (fin B hB) (fin C hC)]
  ring

theorem lattice_has_basis : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Submodule.IsFullLattice K A := { toIsLattice := Submodule.IsLattice.of_fg K hA.1, span_eq_top := hA.2 }
  have := Submodule.IsLattice.finite K A
  have := Submodule.IsLattice.free K A
  let b := Module.Free.chooseBasis O A
  let b' := b.extendOfIsFullLattice K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = finrank K X :=
    (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex]
  have hr : Set.range b' = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [b']
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula
section
noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate
open IsDedekindDomain NumberField

theorem log_product_formula : LogProductFormula := by
  intro L _ _ x hx
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L,
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) x := ⟨_, rfl⟩
  rw [← hIdef]
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hx
  have hfin : (Function.support fun v : HeightOneSpectrum (𝓞 L) => FractionalIdeal.count L v I).Finite :=
    by
      have hev := FractionalIdeal.finite_factors I
      exact Filter.eventually_cofinite.mp hev
  have hR : (∑ᶠ v : HeightOneSpectrum (𝓞 L), (FractionalIdeal.count L v I : ℝ) *
        Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      ∑ v ∈ hfin.toFinset, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hv
    intro h0
    exact hv (by simp [h0])
  have hsub2 : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 L) =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^ FractionalIdeal.count L v I) ⊆
      (hfin.toFinset : Set _) := by
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_mulSupport] at hv
    intro h0
    exact hv (by simp [h0])
  have hfac : ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^
      FractionalIdeal.count L v I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub2]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI
  have hN1 : FractionalIdeal.absNorm I =
      ∏ v ∈ hfin.toFinset, (Ideal.absNorm v.asIdeal : ℚ) ^ FractionalIdeal.count L v I := by
    conv_lhs => rw [← hfac]
    rw [map_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hN2 : FractionalIdeal.absNorm I = |Algebra.norm ℚ x| := by
    rw [hIdef]
    exact FractionalIdeal.absNorm_span_singleton (𝓞 L) x
  have hprod : ∏ σ : L →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun σ => rfl)
  have hne1 : ∀ σ ∈ (Finset.univ : Finset (L →+* ℂ)), ‖σ x‖ ≠ 0 := fun σ _ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero σ).mpr hx
  have hL : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Real.log_prod hne1, ← norm_prod, hprod]
    congr 1
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    simp
  have hne2 : ∀ v ∈ hfin.toFinset, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count L v I ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [hL, hR, ← Rat.cast_abs, ← hN2, hN1]
  push_cast
  rw [Real.log_prod hne2]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Real.log_zpow]

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex
section
open scoped Pointwise

noncomputable section

namespace Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem length_le_of_le {S T A B : Submodule O X} (hST : S ≤ T) (hBA : B ≤ A)
    (hSA : S ⊓ A ≤ B) :
    Module.length O (S ⧸ B.comap S.subtype) ≤ Module.length O (T ⧸ A.comap T.subtype) := by
  let f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢
      exact hBA hx)
  apply Module.length_le_of_injective f
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [f, Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simp only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion]
    at hxy ⊢
  exact hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)

theorem qlen_eq_zero {A B : Submodule O X} (h : A ≤ B) : qlen O X A B = 0 := by
  unfold qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  exact h (a - b).2

end Formalism.LatticeIndexTer.subgroupData

namespace Formalism.LatticeIndexTer

open Formalism.LatticeIndexTer.subgroupData

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
section
noncomputable section

namespace Formalism.LatticeIndexTer

open Finset

lemma ph_zero : ph 0 = 0 := by
  simp [ph]

lemma ph_ge_neg_one {x : ℝ} (hx : 0 ≤ x) : -1 ≤ ph x := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [ph]
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx')
    rw [Real.log_inv] at h1
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx'.ne'
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    rw [mul_sub, h2, mul_one, mul_neg] at h3
    unfold ph
    linarith

lemma le_ph_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log a ≤ ph b - ph a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : b * (a / b - 1) = a - b := by field_simp <;> ring
  rw [h3] at h2
  unfold ph
  linarith

lemma ph_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ph a ≤ ph b := by
  have h1 := le_ph_sub (by linarith : (0 : ℝ) < a) hab
  have h2 : 0 ≤ Real.log a := Real.log_nonneg ha
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) h2]

lemma one_le_log {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

theorem alt_bound {α : Type*} [Preorder α] (f : α → ℝ) (hf : Monotone f) :
    ∀ (k : ℕ) (a : Fin (k + 1) → α) (b : Fin k → α),
      (∀ i : Fin k, b i ≤ a i.castSucc ∧ a i.succ ≤ b i) →
      f (a (Fin.last k)) ≤ (∑ i, f (a i)) - ∑ i, f (b i) ∧
      (∑ i, f (a i)) - ∑ i, f (b i) ≤ f (a 0) := by
  intro k
  induction k with
  | zero =>
    intro a b _
    refine ⟨?_, ?_⟩ <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, sub_zero] <;> exact le_rfl
  | succ k ih =>
    intro a b hab
    have ih' := ih (fun i => a i.castSucc) (fun i => b i.castSucc)
      (fun i => ⟨(hab i.castSucc).1, (hab i.castSucc).2⟩)
    simp only [Fin.castSucc_zero] at ih'
    obtain ⟨h1, h2⟩ := hab (Fin.last k)
    have m1 := hf h1
    have m2 := hf h2
    rw [Fin.succ_last] at m2
    rw [Fin.sum_univ_castSucc (fun i => f (a i)), Fin.sum_univ_castSucc (fun i => f (b i))]
    constructor <;> linarith [ih'.1, ih'.2]

def phm (x : ℝ) : ℝ := ph (max x 1)

lemma phm_mono : Monotone phm := by
  intro x y hxy
  unfold phm
  exact ph_mono (le_max_right _ _) (max_le (le_trans hxy (le_max_left _ _)) (le_max_right _ _))

lemma phm_ge {x : ℝ} : -1 ≤ phm x := ph_ge_neg_one (le_trans zero_le_one (le_max_right x 1))

theorem sumInterlacedBound : Interlace := by
  intro k c c' S w hI hw
  obtain ⟨hc, hc'⟩ := hI
  have hS : 0 ≤ S := le_trans (hc 0).1 (hc 0).2
  have e1 : ∀ x : ℝ, 1 ≤ x → phm x = ph x := fun x hx => by unfold phm; rw [max_eq_left hx]
  have hb : phm (w + c (Fin.last k)) ≤ (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ∧
      (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ≤ phm (w + c 0) :=
    alt_bound phm phm_mono k (fun i => w + c i) (fun i => w + c' i)
      (fun i => ⟨by show w + c' i ≤ w + c i.castSucc; linarith [(hc' i).1],
        by show w + c i.succ ≤ w + c' i; linarith [(hc' i).2]⟩)
  have s1 : (∑ i, phm (w + c i)) = ∑ i, ph (w + c i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc i).1])
  have s2 : (∑ i, phm (w + c' i)) = ∑ i, ph (w + c' i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc' i).2, (hc i.succ).1])
  rw [s1, s2] at hb
  have e0 : phm (w + c 0) = ph (w + c 0) := e1 _ (by linarith [(hc 0).1])
  have up : ph (w + c 0) ≤ ph (w + S) := ph_mono (by linarith [(hc 0).1]) (by linarith [(hc 0).2])
  have lo : -1 ≤ phm (w + c (Fin.last k)) := phm_ge
  have hL : 1 ≤ Real.log (w + S + 2) := one_le_log (by linarith)
  have hphS : ph (w + S) ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    have hl := Real.log_le_log (by linarith : 0 < w + S) (by linarith : w + S ≤ w + S + 2)
    unfold ph
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ w + S),
      mul_nonneg hS (by linarith : 0 ≤ Real.log (w + S + 2))]
  have hp : 1 ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w + 2 * S - 1) (by linarith : 0 ≤ Real.log (w + S + 2) - 1)]
  rw [abs_le]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

end Formalism.LatticeIndexTer
end
end

