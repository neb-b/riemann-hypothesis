module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)

namespace JoinPointFlagModel

section Charts

variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def extChart (t : ∀ k, ι k) : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k
  | .inl k => t k
  | .inr _ => (0 : Fin 1)

theorem mseg_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    mseg (joinCoord y (ptCoord (Ω := Ω))) s = mseg y (restrictChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart]

theorem chartMon_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : K → ℤ) :
    chartMon (joinCoord y (ptCoord (Ω := Ω))) s (pullDeg a) = chartMon y (restrictChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart, pullDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s = chartRing O (mseg y) (restrictChart s) := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range, mseg_join]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrictChart t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨extChart t, rfl⟩

theorem mem_chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : Ω) :
    a ∈ chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s ↔
      a ∈ chartRing O (mseg y) (restrictChart s) := by
  rw [chartRing_join]

end Charts

section Bundles

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    ChartBundle O (mseg (joinCoord y (ptCoord (Ω := Ω)))) N E where
  lat s := B.lat (restrictChart s)
  stable s a ha e he := B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he
  frame s hs := by
    rw [chartRing_join]
    exact B.frame _ (by rwa [mseg_join] at hs)
  overlap s t hs ht e he := by
    rw [mseg_join, mseg_join]
    rw [mseg_join] at hs ht
    exact B.overlap _ _ hs ht e he

theorem pullBundle_lat (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E)
    (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) : (pullBundle O y B).lat s = B.lat (restrictChart s) :=
  rfl

theorem isPull_pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    IsPull O y (ptCoord (Ω := Ω)) B (pullBundle O y B) := by
  intro s _
  rw [pullBundle_lat]
  apply le_antisymm
  · intro v hv
    exact AddSubgroup.subset_closure ⟨1, one_mem _, v, hv, (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he

theorem isGradedFrame_pull (y : (Σ k, ι k) → Ω) {B : ChartBundle O (mseg y) N E}
    {Vs : Fin (N + 1) → Submodule Ω E} {m : Fin N → K → ℤ} {gen : Fin N → E}
    (h : IsGradedFrame O y B Vs m gen) :
    IsGradedFrame O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) Vs
      (fun i => pullDeg (m i)) gen := by
  intro s hs
  rw [mseg_join] at hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ hs
  refine ⟨k, f, c, fun l => (mem_chartRing_join O y s _).mpr (hf l),
    fun l => (mem_chartRing_join O y s _).mpr (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hw⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩
  · rw [pullBundle_lat]
    simp only [mem_chartRing_join]
    exact hiff e
  · obtain ⟨w, ⟨hw0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hw i
    refine ⟨w, ⟨hw0, ⟨n₁, (mem_chartRing_join O y s _).mpr hn₁⟩,
      ⟨n₂, (mem_chartRing_join O y s _).mpr hn₂⟩⟩, ?_⟩
    rw [chartMon_join]
    exact hmem

end Bundles

section Forms

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_join (y : (Σ k, ι k) → Ω) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) :
    aeval (joinCoord y (ptCoord (Ω := Ω))) (rename (liftVar ptIdx) f) = aeval y f := by
  rw [aeval_rename]
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := Unit) a - pullDeg (K' := Unit) b = pullDeg (K' := Unit) (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end Forms

section Pairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
  [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullFlagPair (y : (Σ k, ι k) → Ω) {B B' : ChartBundle O (mseg y) N E} (F : FlagPair O y B B')
    (hvert : ∀ i, IsVertDiv O (mcIdeal O (joinCoord y (ptCoord (Ω := Ω))))
      (pullDeg (K' := Unit) (F.deg i - F.deg' i)) (rename (liftVar ptIdx) (F.f i))
      (rename (liftVar ptIdx) (F.g i))) :
    FlagPair O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) (pullBundle O y B') where
  Vs := F.Vs
  mono := F.mono
  dim := F.dim
  top := F.top
  deg i := pullDeg (F.deg i)
  gen := F.gen
  gen_mem := F.gen_mem
  frame := isGradedFrame_pull O y F.frame
  deg' i := pullDeg (F.deg' i)
  gen' := F.gen'
  gen'_mem := F.gen'_mem
  frame' := isGradedFrame_pull O y F.frame'
  f i := rename (liftVar ptIdx) (F.f i)
  g i := rename (liftVar ptIdx) (F.g i)
  rel i := by
    simp only [aeval_join]
    exact F.rel i
  vert i := by
    simp only [pullDeg_sub]
    exact hvert i

theorem fnField_join (y : (Σ k, ι k) → Ω) :
    fnField O (joinCoord y (ptCoord (Ω := Ω))) = fnField O y := by
  unfold fnField
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ha)
    · exact Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)
    · have h1 : joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, i⟩ /
          joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by
        simp [joinCoord, ptCoord]
      simp only at h1 ⊢
      rw [h1]
      exact one_mem _
  · apply Subfield.closure_mono
    rintro a (ha | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩

end Pairs

end JoinPointFlagModel


open JoinPointFlagModel in
theorem JoinPointFlagModel.proof (hIff : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hModel : JoinPointModel.Statement) (hVert : JoinPointVerticalDivisor.Statement) :
    JoinPointFlagModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hW N E _ _ B B' _ w w' x x' f g hF
  obtain ⟨F, -, -, hdeg, hdeg', hf, hg⟩ :=
    ((hIff O Ω K ι y N E B B' ϖ hϖ hW.multiProj).1 w w' x x' f g).1 hF
  refine ⟨pullBundle O y B, pullBundle O y B',
    pullFlagPair O y F fun i => hVert O Ω K ι y _ _ _ (F.vert i),
    hModel O Ω K ι y d hW, fnField_join O y, isPull_pullBundle O y B, isPull_pullBundle O y B',
    ?_, ?_, ?_, ?_⟩
  · show (fun i => pullDeg (F.deg i)) = _
    rw [hdeg]
  · show (fun i => pullDeg (F.deg' i)) = _
    rw [hdeg']
  · show (fun i => rename (liftVar ptIdx) (F.f i)) = _
    rw [hf]
  · show (fun i => rename (liftVar ptIdx) (F.g i)) = _
    rw [hg]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace plainPairNumber

section ClassNum

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 2
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_eq_sum_of_subset {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by
    rw [mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]


omit [DecidableEq K] in
theorem classList_add_perm {σ : Type*} (cls : σ → K → ℤ) (μ ν : σ →₀ ℕ) :
    (classList cls (μ + ν)).Perm (classList cls μ ++ classList cls ν) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [classList, Multiset.coe_toList, map_add (f := _), Multiset.map_add (f := _)]


theorem classNum_mul_monomial {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (A : MvPolynomial σ ℤ)
    (t : σ →₀ ℕ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (A * monomial t 1) Q W = classNum cls A (classList cls t ++ Q) W := by
  have hsub : (A * monomial t 1).support ⊆ A.support.image (· + t) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · rw [mul_one] at hν
      exact Finset.mem_image.mpr ⟨ν - t, mem_support_iff.mpr hν, tsub_add_cancel_of_le hle⟩
    · exact absurd rfl hν
  rw [classNum_eq_sum_of_subset cls _ Q W hsub,
    Finset.sum_image fun a _ b _ h => add_right_cancel h]
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_mul_monomial, mul_one, ← List.append_assoc,
    FlagTypings.vNumL_perm W ((classList_add_perm cls μ t).append_right Q)]

end ClassNum

section DivDiff

def term {r : ℕ} (l : Fin r) (μ : Fin r →₀ ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  (∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
    (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
    ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j

theorem rename_divDiff_eq_sum {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ)
    {S : Finset (Fin r →₀ ℕ)} (hS : G.support ⊆ S) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ S, C (G.coeff μ) * term l μ := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine (Finset.sum_subset hS ?_).trans (Finset.sum_congr rfl fun μ _ => ?_)
  · intro μ _ hμ
    rw [mem_support_iff, not_not] at hμ
    simp [hμ]
  · unfold term
    ring

end DivDiff

end plainPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


open Classical in
def specialRelDeg (W' : Ideal (MRing (extIdx ι J) O)) : ℕ :=
  if h : (specialIdeal W').IsPrime then
    haveI := h
    FieldNumbers.relDeg Function.Embedding.some (specialIdeal W')
  else 0

end Objects

section Lemmas

def BlowUpFibreDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → divCycle P x W ≠ 0 →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ)
          else 0) =
        divCycle P x W

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      W.comap (liftForm (ι := ι) (J := J) (R := O)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes

def BlowUpHorizontalChartLength.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ hW : W.IsPrime,
      haveI := hW
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) W =
        Module.length
          (Localization.AtPrime ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
            (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))
          (LocalizedModule ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
              (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))).primeCompl
            (Polynomial (MRing ι O) ⧸
              (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))

def PolynomialLocalizedLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime] (I : Ideal R),
    Module.length (Localization.AtPrime (q.map (Polynomial.C : R →+* Polynomial R)))
        (LocalizedModule (q.map (Polynomial.C : R →+* Polynomial R)).primeCompl
          (Polynomial R ⧸ I.map (Polynomial.C : R →+* Polynomial R))) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenericProjClosureDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) →
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

