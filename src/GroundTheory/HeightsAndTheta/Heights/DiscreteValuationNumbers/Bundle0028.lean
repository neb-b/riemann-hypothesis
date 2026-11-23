module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualDisjoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ G'

def ResidualContraction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∀ x : MRing ι O, x ∉ P →
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm x) G' ≤
          divCycle P x (G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem LocalCoefficient.proof (h₁ : LeftTermSupport.Statement.{u})
    (h₂ : RightTermSupport.Statement.{u}) (h₃ : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U
  swap
  ·
    have hl := h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs
    have hr := h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH
    unfold cycEval
    rw [finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]
  obtain ⟨hUp, hUm, hUr, hϖU, hPU⟩ := hU
  have hUdim' := hUdim hUp hUm hUr hϖU
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W := fun W hW k =>
    let ⟨i, hi⟩ := hUr k
    ⟨i, fun h => hi (hW h)⟩
  have hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W := by
    intro J W hW
    unfold idealCycle locCycle
    by_cases hm : W ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hm, hW⟩, dite_eq_left hm]
      rfl
    · rw [dite_eq_right fun h => hm h.1, dite_eq_right hm]
  have hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0 := by
    intro J hJ
    unfold locCycle
    rw [dite_eq_right fun h => hJ h.1.2]
  have hL : ∀ G, ratDiv P f g G * divCycle G s U =
      (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U := by
    intro G
    rw [divCycle_eq_idealCycle, hcyc _ _ hUr]
    by_cases hG : G ≤ U
    · unfold ratDiv
      rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]
    · rw [hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]
  have hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U =
      locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U := by
    intro W
    show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _
    rw [hcyc _ _ hUr]
    by_cases hW : W ≤ U
    · rw [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    · rw [hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]

  have hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U →
      False := by
    intro Q₁ Q₂ _ _ hPQ hQQ hQU
    have e₁ := DimStrictDrop.proof (MRing ι O) P Q₁ hPQ
    have e₂ := DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ
    have e₃ := DimStrictDrop.proof (MRing ι O) Q₂ U hQU
    rw [hP.dim] at e₁
    have key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤
        ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      ((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans
        ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))
    have key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three] using key
    have := WithBot.coe_le_coe.mp key'
    norm_cast at this
    omega

  obtain ⟨u', v', hu', huv⟩ := hD.2 U hUp hPU hUr

  have hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W := by
    intro W hW h
    have hs' : divCycle P s W ≠ 0 := by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    have hr : ratDiv P f g W = 0 := by
      by_cases hϖW : (C ϖ : MRing ι O) ∈ W
      · exact hno W hϖW hs'
      · by_contra h
        exact hϖW (hD.1.vertical W h)
    unfold ratDiv at hr
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW),
      hcyc _ _ (hrel W hW)] at hr
    omega
  unfold cycEval
  rw [finsum_congr hL, finsum_congr hR]
  exact h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu'
    huv hnc

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord pullDeg liftVar ptCoord)

def JoinVerticalDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsVertDiv O (mcIdeal O x) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x z)) (pullDeg (K' := K') b) (rename (liftVar ι') f)
      (rename (liftVar ι') g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Pullback

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem liftForm_mem_blowUpOf_of_mem (P : Ideal (MRing ι R)) (u : J → MRing ι R) {p : MRing ι R}
    (hp : p ∈ P) : liftForm (J := J) p ∈ blowUpOf P u := by
  let φ : MRing ι R →ₐ[R] Polynomial (MRing ι R ⧸ P) :=
    (Polynomial.CAlgHom (R := R) (A := MRing ι R ⧸ P)).comp (Ideal.Quotient.mkₐ R P)
  have hcomp : (aeval (blowUpSubst P u)).comp (liftForm (ι := ι) (J := J) (R := R)) = φ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, liftForm, rename_X, aeval_X]
    rfl
  have h := DFunLike.congr_fun hcomp p
  rw [AlgHom.comp_apply] at h
  unfold blowUpOf
  rw [RingHom.mem_ker, h]
  show Polynomial.C (Ideal.Quotient.mk P p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end Pullback

section Sums

open scoped Classical in
open Classical in
theorem finsum_sub_mul_eq_of_support {α : Type*} (Z₁ Z₂ n : α → ℤ) (p : α → Prop)
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite)
    (hv : ∀ W, Z₁ W - Z₂ W ≠ 0 → p W) :
    ∑ᶠ W, (Z₁ W - Z₂ W) * n W =
      ∑ᶠ W, Z₁ W * (if p W then n W else 0) - ∑ᶠ W, Z₂ W * (if p W then n W else 0) := by
  have e : ∀ W, (Z₁ W - Z₂ W) * n W =
      Z₁ W * (if p W then n W else 0) - Z₂ W * (if p W then n W else 0) := by
    intro W
    by_cases h : Z₁ W - Z₂ W = 0
    · rw [h, zero_mul, sub_eq_zero.mp h, sub_self]
    · rw [ite_eq_left (hv W h), ← sub_mul]
  rw [finsum_congr e, finsum_sub_distrib]
  · exact h₁.subset fun W hW => left_ne_zero_of_mul hW
  · exact h₂.subset fun W hW => left_ne_zero_of_mul hW

end Sums

theorem BlowUpDivisorPush.proof (hvert : BlowUpVerticalPush.Statement.{u}) :
    BlowUpDivisorPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP b f g hD N u hu hu' a
  have hfin := DivCycleFiniteSupport.proof.{u}
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees

  have hvertB : ∀ W, divCycle (blowUpOf P u) (liftForm (J := J) f) W -
      divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 → (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W hW
    by_contra hϖW
    have hsupp : W.IsPrime ∧ blowUpOf P u ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle (blowUpOf P u) (liftForm (J := J) f) W = 0
      · have h2 : divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 := by
          intro h2; apply hW; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨hWp, hBW, hWrel⟩ := hsupp
    let W₀ : Ideal (MRing ι O) := W.comap (liftForm (ι := ι) (J := J) (R := O))
    have hW₀ : W₀.IsPrime := Ideal.comap_isPrime _ _
    have hPW₀ : P ≤ W₀ := fun p hp => hBW (liftForm_mem_blowUpOf_of_mem P u hp)
    have hrel₀ : IsRelevant W₀ := by
      intro k
      obtain ⟨i, hi⟩ := hWrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have h' : liftForm (ι := ι) (J := J) (R := O) (X ⟨k, i⟩) ∈ W := h
      rwa [liftForm, rename_X] at h'
    have hϖ₀ : (C ϖ : MRing ι O) ∉ W₀ := by
      intro h
      have h' : liftForm (ι := ι) (J := J) (R := O) (C ϖ) ∈ W := h
      rw [liftForm, rename_C] at h'
      exact hϖW h'
    obtain ⟨s, t, hs, ht, hst⟩ := hD.unit_off_special W₀ hW₀ hPW₀ hrel₀ hϖ₀
    apply hW
    rw [divCycle_eq_of_mul_sub_mem (u := liftForm (J := J) s) (v := liftForm (J := J) t) hs ht ?_,
      sub_self]
    have := liftForm_mem_blowUpOf_of_mem (J := J) P u hst
    rwa [map_sub, map_mul, map_mul] at this
  have e₁ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bf f hbf hD.num_not_mem a
  have e₂ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bg g hbg hD.den_not_mem a
  unfold cycEval at e₁ e₂
  unfold cycEval ratDiv
  rw [finsum_sub_mul_eq_of_support (divCycle (blowUpOf P u) (liftForm (J := J) f))
      (divCycle (blowUpOf P u) (liftForm (J := J) g)) _ _ (hfin _ _ _ _ _) (hfin _ _ _ _ _) hvertB,
    finsum_sub_mul_eq_of_support (divCycle P f) (divCycle P g) _ _ (hfin _ _ _ _ _)
      (hfin _ _ _ _ _) hD.vertical, e₁, e₂]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleCutProof

theorem intNumL_cons_eq_snoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type} [Field F] (P : Ideal (MRing ι F)) (x : K → ℤ)
    (L : List (K → ℤ)) :
    intNumL F P (x :: L) = intNum F P (Fin.snoc (α := fun _ => K → ℤ) L.get x) := by
  have hget : (x :: L).get = Fin.cons (α := fun _ => K → ℤ) x L.get := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have h := FieldNumbers.IntNumSymm.proof F K ι P (L.length + 1)
    (Fin.cons (α := fun _ => K → ℤ) x L.get) (finRotate _)
  rw [intNumL, hget, Fin.snoc_eq_cons_rotate, ← h]
  rfl

theorem cycEval_single {K : Type} {ι : K → Type} {F : Type} [Field F]
    (n : Ideal (MRing ι F) → ℤ) (Z : Ideal (MRing ι F)) :
    cycEval n (fun W => by classical exact if W = Z then 1 else 0) = n Z := by
  classical
  unfold cycEval
  rw [finsum_eq_single _ Z (fun W hW => by simp [hW])]
  simp

end FlagBundleCutProof


open FlagBundleCutProof in
theorem FlagBundleCut.proof (hDim : FlagBundleDim.Statement)
    (hForms : FlagBundleSectionForms.Statement) (hDiv : FlagBundleSectionDiv.Statement)
    (hCut : FieldNumbers.CutRational.Statement.{0}) : FlagBundleCut.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi L hL
  obtain ⟨bf, bg, f, g, hf, hg, hdeg, hfP, hgP, hval⟩ :=
    hForms F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i
  have hdiv := hDiv F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi bf bg f g hf hg hdeg hgP hval
  obtain ⟨hP, hrel⟩ :=
    hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) =
      ((L.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hrel]
    congr 2
    omega
  have h := hCut F (Option K) (bundleIdx ι M) _ hP L.length hrel' bf bg f g hf hg hfP hgP L.get
  rw [intNumL_cons_eq_snoc, ← hdeg, h, funext hdiv, intNumL]
  classical
  convert cycEval_single (fun W => intNum F W L.get) (projIdeal F y w φ (truncCoord t i))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem FlagBundleDim.proof (hspan : TwistedDualGensSpan.Statement)
    (hdim : SpanBundleDim.Statement) : FlagBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi1 hiN

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hsp := hspan F Ω K ι y N E B a M φ hφ c hyc

  have hv : ∀ m : Fin N, ∃ v ∈ B.lat c, (∀ j, m < j → w.repr v j = 0) ∧
      w.repr v m = ∏ k, y ⟨k, c k⟩ ^ b m k := by
    intro m
    have hmem : (∏ k, y ⟨k, c k⟩ ^ b m k) ∈ degLat F y (b m) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hflag.graded c hyc m] at hmem
    exact hmem
  choose v hvl hvz hvd using hv
  obtain ⟨ι', hι'⟩ : ∃ ι' : Fin i → Fin N, ι' = Fin.castLE hiN := ⟨_, rfl⟩
  have hsum : ∀ {β : Type} [AddCommMonoid β] (f : Fin N → β), (∀ j : Fin N, i ≤ (j : ℕ) → f j = 0) →
      ∑ j, f j = ∑ j : Fin i, f (ι' j) := by
    intro β _ f hf
    have hm : ∑ j : Fin i, f (ι' j) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hiN), f j := by
      rw [Finset.sum_map, hι']
      rfl
    rw [hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
    by_contra h
    exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : Fin M → Fin i → Ω, G = fun l j => φ l (w (ι' j)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin i) (Fin i) Ω, H = Matrix.of fun j m => w.repr (v (ι' m)) (ι' j) :=
    ⟨_, rfl⟩
  have hinj : Function.Injective ι' := by
    rw [hι']
    exact Fin.castLE_injective hiN
  have hval : ∀ m : Fin i, ((ι' m : Fin N) : ℕ) = m := fun m => by
    rw [hι', Fin.val_castLE]
  have hlt : ∀ m j : Fin i, m < j → ι' m < ι' j := fun m j h => by
    rw [Fin.lt_def, hval, hval]
    exact Fin.lt_def.mp h
  have hGH : ∀ l m, (Matrix.of G * H) l m = φ l (v (ι' m)) := by
    intro l m
    conv_rhs => rw [← w.sum_repr (v (ι' m))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hsum]
    · simp [Matrix.mul_apply, hG, hH, mul_comm]
    · intro j hj
      have hm := m.isLt
      rw [map_smul, hvz _ j (by rw [Fin.lt_def, hval]; omega), zero_smul]
  have hdet : IsUnit H.det := by
    rw [Matrix.det_of_isUpperTriangular (M := H) fun j m hjm => by
      rw [hH, Matrix.of_apply]
      exact hvz _ _ (hlt m j hjm)]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m _ => ?_)
    simp only [hH, Matrix.of_apply, hvd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hlin : LinearIndependent Ω (fun j l => G l j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hall : ∀ ψ ∈ Submodule.span Ω (Set.range φ), ψ (∑ j, g j • w (ι' j)) = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        have := congrFun hg l
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [hG, map_sum, Finset.sum_apply, mul_comm] using this
      | zero => simp
      | add x z _ _ hx hz => rw [LinearMap.add_apply, hx, hz, add_zero]
      | smul r x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
    rw [hsp] at hall
    have hw := (Module.forall_dual_apply_eq_zero_iff Ω _).mp fun ψ => hall ψ Submodule.mem_top
    exact Fintype.linearIndependent_iff.mp (w.linearIndependent.comp ι' hinj) g hw
  have hcoord : projCoord y w φ (truncCoord t i) =
      projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    funext p
    rcases p with ⟨_ | k, l⟩
    · show ∑ j, truncCoord t i j * _ = ∑ j, _
      rw [hsum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((ι' j : Fin N) : ℕ) < i := by rw [hval]; exact j.isLt
        simp only [truncCoord, hj, if_true, hG, Function.comp_apply, Pi.basisFun_apply]
        rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        rfl
      · intro j hj
        simp [truncCoord, not_lt.mpr hj]
    · rfl
  have hproj : projIdeal F y w φ (truncCoord t i) = projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    unfold projIdeal
    rw [hcoord]
  rw [hproj]
  exact hdim F Ω K ι y e hV hdimV M i G (by omega) hlin c a H hyc hdet
    (fun l m => by rw [hGH]; exact hφ.sections c hyc l _ (hvl _)) Φ (t ∘ ι')
    (ht.comp ι' hinj)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

