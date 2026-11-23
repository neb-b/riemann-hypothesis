module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

universe u

namespace Numbers

abbrev Statement : Prop := IntNumIsFieldIntersection.Statement.{u}

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem agree_of_existsUnique (hN : Statement.{u}) (hU : ExistsUniqueStatement F ι)
    (I : IFamily F ι) (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ)
    (L : Fin n → K → ℤ) (hV : IsProjVarF V n) : I V n L = intNum F V L := by
  obtain ⟨I₀, -, h₀⟩ := hU
  exact (h₀ I hI V n L hV).trans (h₀ _ (hN F K ι) V n L hV).symm

theorem existsUnique_iff (hN : Statement.{u}) :
    ExistsUniqueStatement F ι ↔ ∀ I : IFamily F ι, IsFieldIntersection I →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
        I V n L = intNum F V L :=
  ⟨fun hU I hI V n L hV => agree_of_existsUnique hN hU I hI V n L hV,
    fun h => ⟨fun V _ L => intNum F V L, hN F K ι, h⟩⟩


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem ringKrullDim_eq_of_relDim (V : Ideal (MRing ι F)) (n : ℕ)
    (h : FieldNumbers.relDim V = (n : WithBot (WithTop ℤ))) :
    ringKrullDim (MRing ι F ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold FieldNumbers.relDim at h
  generalize ringKrullDim (MRing ι F ⧸ V) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h₁ : ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) = (n : WithBot (WithTop ℤ)) := h
      have h' : (⊤ : WithTop ℤ) = (n : WithTop ℤ) := by exact_mod_cast h₁
      exact absurd h' (WithTop.top_ne_coe)
    | coe m =>
      have h₁ : ((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) =
          (n : WithBot (WithTop ℤ)) := h
      have h' : (m : ℤ) - Fintype.card K = n := by exact_mod_cast h₁
      have hm : m = n + Fintype.card K := by omega
      rw [hm]
      rfl

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) {I : IFamily F ι}
    (hI : IsFieldIntersection I) : FieldNumbers.IsIntersectionTheory F I := by
  refine ⟨?_, ?_⟩
  · intro P hP h0
    have hdim := ringKrullDim_eq_of_relDim P 0 (by rw [h0]; rfl)
    choose i hi using hP.relevant
    rw [hI.1 P ![] i ⟨(Objects.isMultiProjPrime_iff P).mp hP, hdim⟩ hi,
      ← hPt F K ι P i hP hdim hi]
    obtain ⟨-, h2⟩ := hBase F K ι P hP h0
    rw [h2, FieldNumbers.resDeg, dite_eq_left hP.isPrime]
  · intro P n hP hdim bf bg f g hf hg hfP hgP bs
    have hd := ringKrullDim_eq_of_relDim P (n + 1) hdim
    have hs : IsRatSection P (fun k => (bf k : ℤ) - bg k) f g :=
      ⟨bf, bg, (Objects.isMultiHomog_iff f bf).mp hf, (Objects.isMultiHomog_iff g bg).mp hg,
        hfP, hgP, fun k => rfl⟩
    rw [hI.2 P n bs _ f g ⟨(Objects.isMultiProjPrime_iff P).mp hP, hd⟩ hs]
    have hD : ∀ W, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W = ratDiv P f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ← hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem agree (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  hUq F K ι I (isIntersectionTheory hPt hBase hI) V ((Objects.isMultiProjPrime_iff V).mpr hV.1) n
    (relDim_eq_of_ringKrullDim V n hV.2) L

theorem existsUnique (hN : Statement.{u}) (hUq : FieldNumbers.IntNumUnique.Statement.{u})
    (hPt : IntNumPoint.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u}) :
    ExistsUniqueStatement F ι :=
  (existsUnique_iff hN).mpr (agree hUq hPt hBase)

theorem agree_of (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  agree (FieldNumbers.IntNumUnique.proof hCut hBase hEx hDiv) (IntNumPoint.proof hBase) hBase I hI
    V n L hV

end Numbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]


open scoped Classical in
open Classical in
def locCycle (J W : Ideal R) : ℤ :=
  if h : W ∈ J.minimalPrimes then
    haveI : W.IsPrime := h.1.1
    ((Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))).toNat : ℤ)
  else 0

end Defs

section Lemmas

def LeftTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    ∀ G U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      ratDiv P f g G * divCycle G s U = 0

def RightTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ W U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U = 0

def LocalCoeffRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (P U : Ideal R), P.IsPrime → U.IsPrime → P ≤ U →
    (∀ Q₁ Q₂ : Ideal R, Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False) →
    ∀ f g s u v : R, f ∉ P → g ∉ P → s ∉ P → u ∉ U → u * f - v * g ∈ P →
    (∀ W : Ideal R, W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U =
      ∑ᶠ W, locCycle (P ⊔ Ideal.span {s}) W *
        locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' ≤ divCycle P s G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' ≤
          ratDiv P f g G

def ExceptionalComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
              (liftForm g * newVar (some none)) G' ≤ divCycle P s G ∧
        ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
            (liftForm g * newVar (some none)) G' ≤ ratDiv P f g G

end Lemmas

section Examples

section Simple

variable {A : Type*} [CommRing A]

end Simple

theorem form_mem_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P x W ≠ 0) : x ∈ W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  · exact absurd rfl h

section Constants

set_option linter.unusedSectionVars false

variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]

theorem liftForm_const (a : O) : liftForm (J := J) (C a : MRing ι O) = C a :=
  (liftForm (J := J) (ι := ι) (R := O)).commutes a

end Constants

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LtNatCastOfAddOneLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_natCast_of_add_one_le' {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem TautologicalCase.proof (h3 : IntNumAddFirst.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : TautologicalCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD cf cg hf hg hb L

  have hfin : ∀ x : MRing ι O, (Function.support (divCycle P x)).Finite := fun x =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {x})).subset fun W hW => by
      by_contra hmin
      exact hW (by unfold divCycle; rw [dite_eq_right]; exact fun h => hmin h.1)
  have hZfin : (Function.support (ratDiv P f g)).Finite :=
    ((hfin f).union (hfin g)).subset fun W hW => by
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hW (by simp [ratDiv, h.1, h.2])
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (x : MRing ι O) (e : K → ℕ), IsMultiHomog x e → ∀ W, divCycle P x W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro x e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P x e hPmh he) hW'.1, hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 → vNum W (Matrix.vecCons b L) =
      vNum W (Matrix.vecCons (fun k => (cf k : ℤ)) L) - vNum W (Matrix.vecCons (fun k => (cg k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g cg hg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f cf hf W hWf
    have hdrop := h10 (MRing ι O) P W (lt_of_le_of_ne hPW fun e => hϖP (e ▸ hϖW))
    rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by omega] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      exact lt_natCast_of_add_one_le' hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b (fun k => (cg k : ℤ)) L
    rw [show b + (fun k => (cg k : ℤ)) = fun k => (cf k : ℤ) by rw [← hb]; funext k; simp] at key
    unfold vNum
    rw [key]; ring
  unfold cutIdentityLeftSide cutIdentityRightSide cycEval
  rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
      (hZfin.subset (Function.support_mul_subset_left _ _)),
    ← finsum_sub_distrib ((hfin f).subset (Function.support_mul_subset_left _ _))
      ((hfin g).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  rw [← mul_sub, ← sub_mul]
  change ratDiv P f g W * _ = ratDiv P f g W * _
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [if_pos (hD.vertical W hW), hadd W hW]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundlePullbackVanish

theorem liftDeg_eq_pullDeg {K : Type*} (L : K → ℤ) :
    liftDeg L = FieldNumbers.pullDeg Function.Embedding.some L := by
  funext o
  cases o with
  | none =>
    rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ (by simp)]
    rfl
  | some k =>
    exact (Function.Embedding.some.injective.extend_apply L 0 k).symm

theorem contract_projIdeal {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) {N M : ℕ} {E : Type} [AddCommGroup E]
    [Module Ω E] (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename Option.some).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (map_injective _ (algebraMap Ω Φ).injective)
  ext x
  simp only [FieldNumbers.contractPrime, projIdeal, pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  refine Iff.trans ?_ (map_eq_zero_iff ψ hψ)
  refine Iff.of_eq (congrArg (· = 0) ?_)
  induction x using MvPolynomial.induction_on with
  | C r =>
    simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X, eval₂Hom_X', pointConeMap, aeval_X]
    simp [ψ, FieldNumbers.blockIncl, projCoord]
    exact Or.inl rfl

theorem proof (hPF : FieldNumbers.ProjectionFormulaContracted.Statement.{0})
    (hDim : FlagBundleDim.Statement) : FlagBundlePullbackVanish.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hVdim N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi2 hiN L hL
  obtain ⟨hP, hrel⟩ := hDim F Ω K ι y e hV hVdim N E B w b hflag M a φ hφ Φ t ht i (by omega) hiN
  have hlen : (L.map liftDeg).length = e + i - 1 := by simp; omega
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel, hlen]
  have hrelV : FieldNumbers.relDim (ι := ι) (pointIdeal F y) =
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim, hVdim]
    have : (((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = e := by push_cast; ring
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  have hcontr : FieldNumbers.relDim
      (FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ (truncCoord t i))) <
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [contract_projIdeal]
    show FieldNumbers.relDim (ι := ι) (pointIdeal F y) < _
    rw [hrelV, hlen]
    show (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
      ((((e + i - 1 : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))
  have hzero := hPF F K (Option K) Function.Embedding.some (bundleIdx ι M)
    (projIdeal F y w φ (truncCoord t i)) hP _ hrel' hcontr
    (fun k => L.get (Fin.cast (by simp) k))
  rw [intNumL, ← hzero]
  congr 1
  funext k
  simp [liftDeg_eq_pullDeg]

end FlagBundlePullbackVanish

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

