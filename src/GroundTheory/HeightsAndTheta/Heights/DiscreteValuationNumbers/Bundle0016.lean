module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthTwoGeneratorQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def plainPolynomialPairNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O) (m : ℕ) (G : MvPolynomial (Fin N) ℤ),
    G.IsHomogeneous m → m ≤ d + 1 →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - m) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) P d
                                (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * pairNum P x x' f g
          (fun i => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) (classList L μ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace Objects

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Ring

variable {R : Type*} [CommRing R]

theorem weight_blockWeight_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • blockWeight ι i) (fun i => zero_smul ℕ _),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight_apply, h m (mem_support_iff.mpr hm) k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal I := by
  classical
  constructor
  · intro h
    refine ⟨{x | x ∈ I ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x a}, fun f hf => hf.2, ?_⟩
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun x hx => hx.1)
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨h f hf b, b, ?_⟩
    exact (isMultiHomog_iff _ b).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hI : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span _ _ fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((isMultiHomog_iff x a).mpr ha)⟩
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hI hf b

theorem isMultiProjPrime_iff (P : Ideal (MRing ι R)) :
    IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩


end Ring

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]



end DVR

end Objects

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordAssocVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}

def assocDeg (a : K ⊕ K' → ℤ) : K ⊕ (K' ⊕ K₂) → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)

def assocVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inl k), i⟩

theorem joinCoord_assocVar {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord z w) (assocVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}

def midDeg (a : K ⊕ K' → ℤ) : K ⊕ (K₂ ⊕ K') → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

def midVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩

theorem joinCoord_midVar {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord w z) (midVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Length
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem lengthFormulaDimTwo : LengthFormulaDimTwo.Statement.{u} :=
  ReciprocityTheory.ChartRestriction.G.AI.length_two_generator_quotient

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace CutByFormField

theorem vecCons_comp_finRotate {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

end CutByFormField

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumIsFieldIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem isMultiProjPrime_of_vocab (h2 : VocabMultiHomogIdeal.Statement.{u})
    {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {V : Ideal (MRing ι F)}
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime V) : IsMultiProjPrime V :=
  ⟨hV.1, (h2 F K ι V).1 hV.2.1, hV.2.2⟩

private theorem finsum_mul_eq_finsupp_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem IntNumIsFieldIntersection.proof (h1 : VocabMultiHomog.Statement.{u})
    (h2 : VocabMultiHomogIdeal.Statement.{u}) (h3 : VocabDivCycle.Statement.{u})
    (h4 : IntNumPoint.Statement.{u}) (h5 : IntNumRatSection.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} := by
  intro F _ K _ _ ι _
  refine ⟨?_, ?_⟩
  · intro V L i hV hi
    have hL : L = (![] : Fin 0 → K → ℤ) := funext fun j => Fin.elim0 j
    subst hL
    exact h4 F K ι V i (isMultiProjPrime_of_vocab h2 hV.1) hV.2 hi
  · intro V n L A f g hV hs
    obtain ⟨α, β, hf, hg, hfV, hgV, hαβ⟩ := hs
    have key := h5 F K ι n V (isMultiProjPrime_of_vocab h2 hV.1) hV.2 L A f g α β
      ((h1 F K ι f α).1 hf) ((h1 F K ι g β).1 hg) hfV hgV hαβ
    refine key.trans ?_
    have hD : ∀ W, ratDiv V f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [h3 F K ι V f W, h3 F K ι V g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact finsum_mul_eq_finsupp_sum _ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open GroundTheory.Heights₂.Heights.FieldNumbers

universe u

theorem relDim_eq_of_ringKrullDim {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    relDim I = (n : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  show ((((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) = _
  push_cast
  simp
  rfl

theorem IntNumRatSection.proof (h : CutRational.Statement.{u}) : IntNumRatSection.Statement.{u} := by
  intro F _ K _ _ ι _ n V hV hdim L A f g α β hf hg hfV hgV hA
  have hrel : relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    relDim_eq_of_ringKrullDim V (n + 1) hdim
  have hAeq : (fun k => (α k : ℤ) - β k) = A := funext hA
  have := h F K ι V hV n hrel α β f g hf hg hfV hgV L
  rw [hAeq] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPowSpanFinrankBounded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing Module

universe u

theorem PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (h : ringKrullDim A = 1) : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hbot
  have h0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)
  rw [h] at h0
  exact absurd h0 (by decide)

theorem PowSpanFinrankBounded.finrank_quotient_eq_length {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (finrank (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) : ℕ∞) =
      length A (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) := by
  have : Module.Finite (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective]
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact (Module.length_eq_finrank (A ⧸ maximalIdeal A) _).symm

theorem PowSpanFinrankBounded.spanFinrank_le_length {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (N : Ideal A) {x : A} (hx : x ∈ maximalIdeal A) :
    (N.spanFinrank : ℕ∞) ≤ length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N x)) := by
  have hle : LinearMap.range (LinearMap.lsmul A ↥N x) ≤ maximalIdeal A • (⊤ : Submodule A ↥N) := by
    rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  rw [spanFinrank_eq_finrank_quotient N (IsNoetherian.noetherian N),
    PowSpanFinrankBounded.finrank_quotient_eq_length]
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

theorem PowSpanFinrankBounded.proof : PowSpanFinrankBounded.Statement.{u} := by
  intro A _ _ _ _ h I
  obtain ⟨x, hxm, hx0⟩ := PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal h
  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (A := A) h
  have hA := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A A x h hx0
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top A hx0
  rw [finrank_self, Nat.cast_one, one_mul] at hA
  have hord : Ring.ord A x ≠ ⊤ := hA ▸ hfin
  refine ⟨(Ring.ord A x).toNat, fun n => ?_⟩
  have hN := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A ↥(I ^ n) x h hx0
  have hr : finrank A ↥(I ^ n) ≤ 1 := (Submodule.finrank_le (I ^ n)).trans_eq (finrank_self A)
  have key : ((I ^ n).spanFinrank : ℕ∞) ≤ ((Ring.ord A x).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat hord]
    calc ((I ^ n).spanFinrank : ℕ∞)
        ≤ length A (↥(I ^ n) ⧸ LinearMap.range (LinearMap.lsmul A ↥(I ^ n) x)) :=
          PowSpanFinrankBounded.spanFinrank_le_length (I ^ n) hxm
      _ = (finrank A ↥(I ^ n) : ℕ∞) * Ring.ord A x := hN
      _ ≤ 1 * Ring.ord A x := by gcongr; exact_mod_cast hr
      _ = Ring.ord A x := one_mul _
  exact_mod_cast key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem VocabDivCycle.proof : VocabDivCycle.Statement := by
  intro R _ _ K _ ι _ P s W
  classical
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [e, divCycle]
  by_cases h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s
  · have h' : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := h
    have hW : W.IsPrime := h'.1.1.1
    rw [if_pos h, dite_eq_left h', ReciprocityTheory.ChartRestriction.G.Geo.multAt, dite_eq_left hW]
    rfl
  · have h' : ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W) := h
    rw [if_neg h, dite_eq_right h']
    rfl
  all_goals rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weight_blockWeight_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem VocabMultiHomog.proof : VocabMultiHomog.Statement := by
  intro R _ K _ _ ι _ s a
  constructor
  · intro h d hd
    funext k
    rw [weight_blockWeight_apply]
    exact h d (MvPolynomial.mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_blockWeight_apply]
    exact congrFun (h (MvPolynomial.mem_support_iff.mp hm)) k

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsConeTrdegFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal fnField)

def ConeTrdegFnField.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Ω : Type) [Field Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
      (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) =
        Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω)) + Fintype.card K

end GroundTheory.Heights₂.Heights.NumbersDVR
end

