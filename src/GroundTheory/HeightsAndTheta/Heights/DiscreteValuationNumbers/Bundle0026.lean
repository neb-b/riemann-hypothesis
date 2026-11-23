module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (M i : ℕ) (G : Fin M → Fin i → Ω), 0 < i → LinearIndependent Ω (fun j l => G l j) →
    ∀ (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ∧
        FieldNumbers.relDim (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section General

variable {A : Type*} [CommRing A]

theorem localizedQuot_nontrivial_of_le (J W : Ideal A) [W.IsPrime] (h : J ≤ W) :
    Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk 1 1, 0, fun e => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at e
  obtain ⟨u, hu⟩ := e
  simp only [one_smul, smul_zero] at hu
  rw [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
    Ideal.Quotient.eq_zero_iff_mem] at hu
  exact u.2 (h hu)

theorem withBot_lt_natCast_of_add_one_le (x : WithBot ℕ∞) (N : ℕ) (h : x + 1 ≤ (N : WithBot ℕ∞)) :
    x < (N : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (N : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := by
      rintro rfl
      simp at h'
    exact_mod_cast (ENat.add_one_le_iff hy).mp h'

end General

theorem LeftExpansion.proof (hcut : VNumCut.Statement.{u}) : LeftExpansion.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hno L
  classical
  have : P.IsPrime := hP.multiProj.isPrime

  have key : ∀ G, ratDiv P f g G ≠ 0 →
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L) = cycEval (fun U => vNum U L) (divCycle G s) := by
    intro G hG
    have hmin : ∃ h : MRing ι O, h ∉ P ∧ (∃ e : K → ℕ, IsMultiHomog h e) ∧
        G ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant G := by
      obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
      by_cases hfG : divCycle P f G = 0
      · have hgG : divCycle P g G ≠ 0 := by
          intro h0
          apply hG
          simp [ratDiv, hfG, h0]
        unfold divCycle at hgG
        split_ifs at hgG with hW
        · exact ⟨g, hD.den_not_mem, ⟨bg, hg⟩, hW.1, hW.2⟩
        · exact absurd rfl hgG
      · unfold divCycle at hfG
        split_ifs at hfG with hW
        · exact ⟨f, hD.num_not_mem, ⟨bf, hf⟩, hW.1, hW.2⟩
        · exact absurd rfl hfG
    obtain ⟨h, hhP, ⟨e, he⟩, hGmin, hGrel⟩ := hmin
    have hGp : G.IsPrime := hGmin.1.1
    have hPG : P ≤ G := le_sup_left.trans hGmin.1.2
    have hhG : h ∈ G := hGmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hPltG : P < G := lt_of_le_of_ne hPG (fun hPeq => hhP (hPeq ▸ hhG))
    have hGmh : IsMultiHomogIdeal G :=
      MinimalPrimeMultiHomog.proof O K ι _ G
        (SupSpanMultiHomog.proof O K ι P h e hP.multiProj.multiHomog he) hGmin
    have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
    have hdim : ringKrullDim (MRing ι O ⧸ G) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have hdrop := DimStrictDrop.proof (MRing ι O) P G hPltG
      rw [hP.dim] at hdrop
      have hN : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [hN] at hdrop
      exact withBot_lt_natCast_of_add_one_le _ _ hdrop
    have hsG : s ∉ G := by
      intro hsG
      have h1 := mem_minimalPrimes_sup_span_mul (x := h) hsP hGmin
      have hGs : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        refine ⟨⟨hGp, sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)⟩, fun Q hQ hQG => ?_⟩
        have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
        exact h1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
          ((Ideal.span_singleton_le_iff_mem _).mpr (Q.mul_mem_left h hsQ))⟩ hQG
      have hne : divCycle P s G ≠ 0 := by
        unfold divCycle
        rw [dite_eq_left ⟨hGs, hGrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {s}) G hGs.1.2
        have h0 : multAt (P ⊔ Ideal.span {s}) G ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime G)
            (M := LocalizedModule G.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {s})))).ne'
        have htop := length_localizedQuot_ne_top _ G hGs
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      exact hG (hno G hϖG hne)
    exact hcut O ϖ hϖ K ι G d hGp hGmh hϖG hdim s c hs hsG L

  have hfinR : (Function.support (ratDiv P f g)).Finite :=
    ((DivCycleFiniteSupport.proof O K ι P f).union (DivCycleFiniteSupport.proof O K ι P g)).subset
      (fun G hG => by
        by_contra hc
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
        exact hG (by simp [ratDiv, hc.1, hc.2]))
  set A := hfinR.toFinset with hAdef
  have hfinB : (⋃ G ∈ A, Function.support (divCycle G s)).Finite :=
    A.finite_toSet.biUnion (fun G _ => DivCycleFiniteSupport.proof O K ι G s)
  set B := hfinB.toFinset with hBdef
  have hA : ∀ G, ratDiv P f g G ≠ 0 → G ∈ A := fun G hG => hfinR.mem_toFinset.mpr hG
  have hB : ∀ G ∈ A, ∀ U, divCycle G s U ≠ 0 → U ∈ B :=
    fun G hGA U hU => hfinB.mem_toFinset.mpr (Set.mem_biUnion hGA hU)
  have eL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      ∑ G ∈ A, ∑ U ∈ B, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG))]
    refine Finset.sum_congr rfl fun G _ => ?_
    by_cases hr : ratDiv P f g G = 0
    · simp [hr]
    · rw [key G hr, cycEval, finsum_eq_sum_of_support_subset _ (s := B)
        (fun U hU => hB G (hA G hr) U (left_ne_zero_of_mul hU)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ => by ring
  have eR : cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g)) =
      ∑ U ∈ B, ∑ G ∈ A, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    have hsub : Function.support (fun U =>
        (∑ᶠ G, ratDiv P f g G * divCycle G s U) * vNum U L) ⊆ ↑B := by
      intro U hU
      have h1 := left_ne_zero_of_mul hU
      obtain ⟨G, hG⟩ : ∃ G, ratDiv P f g G * divCycle G s U ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h1 (finsum_eq_zero_of_forall_eq_zero hc)
      exact hB G (hA G (left_ne_zero_of_mul hG)) U (right_ne_zero_of_mul hG)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG)),
      Finset.sum_mul]
  rw [eL, eR, Finset.sum_comm]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace AdditivityInDivisor

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_add_cycle {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  rw [← finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))]
  exact finsum_congr fun W => by simp [add_mul]

theorem cycEval_add_fn {n n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (h : ∀ W, Z W ≠ 0 → n W = n₁ W + n₂ W) : cycEval n Z = cycEval n₁ Z + cycEval n₂ Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW, mul_add]

theorem ratDiv_support_finite {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by
  refine (hf.union hg).subset fun W hW => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem withBot_lt_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e] at hx
      exact absurd (WithBot.coe_le_coe.mp hx) (by simp)
    | coe m =>
      have h1 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : m + 1 ≤ n := by exact_mod_cast h1
      have h3 : ((m : ℕ) : WithBot ℕ∞) < ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast (show m < n by omega)
      simpa using h3

theorem ratDiv_mul_mul (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by
  funext W
  simp only [ratDiv, Pi.add_apply, hmul O K ι P f₁ f₂ hP hf₁ hf₂, hmul O K ι P g₁ g₂ hP hg₁ hg₂]
  ring

end AdditivityInDivisor

theorem AdditivityInDivisor.proof (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b₁ b₂ f₁ g₁ f₂ g₂ hD₁ hD₂ c s hs hsP hsH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have rfin : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ratDiv_support_finite (hfin O K ι Q x) (hfin O K ι Q y)
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [ratDiv_mul_mul hmul hPp hD₁.num_not_mem hD₂.num_not_mem hD₁.den_not_mem hD₂.den_not_mem]
    exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
  · unfold cutIdentityRightSide
    refine cycEval_add_fn (hfin O K ι P s) fun W hW => ?_
    obtain ⟨hWp, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    split_ifs with hϖW
    ·
      have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        unfold divCycle at hW
        split_ifs at hW with h
        · exact h.1
        · exact absurd rfl hW
      have hWh : IsMultiHomogIdeal W :=
        hmin O K ι _ W (hsup O K ι P s c hP.multiProj.multiHomog hs) hWmin
      have hsW : s ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hsW)
      have hdim := hdrop (MRing ι O) P W hlt
      rw [hP.dim, ← hqd O ϖ hϖ K ι W hϖW,
        show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by ring] at hdim
      exact hadd _ K ι d (specialIdeal W) (hcor O ϖ hϖ K ι P W hWp hϖW).1 (hspm O K ι W hWh)
        (withBot_lt_of_add_one_le hdim) b₁ b₂ L
    ·
      obtain ⟨hV₁, hV₂⟩ := hsH W hW hϖW
      rw [ratDiv_mul_mul hmul hWp hV₁.num_not_mem hV₂.num_not_mem hV₁.den_not_mem hV₂.den_not_mem]
      exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

