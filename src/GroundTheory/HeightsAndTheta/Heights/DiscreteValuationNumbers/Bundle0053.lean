module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section ClassNumPairDiff

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_pairDiff_mul {n e : ℕ} {W : Ideal (MRing ι O)}
    (hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
      vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l))
    (z z' : Fin n → K → ℤ) (j : Fin n) {H : MvPolynomial (Fin n ⊕ Fin n) ℤ} {t : ℕ}
    (hH : H.IsHomogeneous t) (Q : List (K → ℤ)) (ht : e ≤ t + Q.length) :
    classNum (Sum.elim z z') (pairDiff j * H) Q W =
      ∑ μ ∈ H.support,
        H.coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
  have hsub : classNum (Sum.elim z z') (pairDiff j * H) Q W =
      classNum (Sum.elim z z') (X (Sum.inl j) * H) Q W -
        classNum (Sum.elim z z') (X (Sum.inr j) * H) Q W := by
    rw [pairDiff, sub_mul]
    exact map_sub (classNumAddHom (Sum.elim z z') Q W) _ _
  rw [hsub, classNum_X_mul, classNum_X_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : e ≤ (classList (Sum.elim z z') μ ++ Q).length := by
    rw [List.length_append, classList_length_of_mem_support _ hH hμ]
    exact ht
  have h := hadd (z j - z' j) (z' j) _ hlen
  rw [sub_add_cancel] at h
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h]
  ring

end ClassNumPairDiff

theorem cycEval_vNumL_comm (hC2 : VerticalDivisorsCommute.Statement.{0}) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hP : IsModelOver P (l.length + 1)) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g') :
    cycEval (fun W => vNumL W (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => vNumL W (b :: l)) (ratDiv P f' g') := by
  have h := hC2 O ϖ hϖ K ι P l.length hP b b' f g f' g' hD hD' l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

theorem PairNumberExpansionIndependence.proof (hC2 : VerticalDivisorsCommute.Statement.{0}) :
    PairNumberExpansionIndependence.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP n z z' f g hD m A hA As Bs hAs hBs Q hQ
  have hrel : ∑ i, pairDiff i * (As - Bs) i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, pairDiff, ← hAs.expansion,
      ← hBs.expansion, sub_self]
  obtain ⟨Kz, hKa, hKh, hK0, hKs⟩ := koszul_homogeneous (m := m) (As - Bs)
    (fun i => (hAs.homogeneous i).sub (hBs.homogeneous i)) hrel
  rw [← sub_eq_zero, ← pairNumHom_apply, ← pairNumHom_apply, ← map_sub]
  by_cases hm : m - 1 = 0
  · have h0 : As - Bs = 0 := funext fun i => by
      rw [hKs i]
      simp [hK0 hm]
    rw [h0, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hlen : ∀ i j μ, μ ∈ (Kz i j).support → (classList (Sum.elim z z') μ ++ Q).length = e := by
    intro i j μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hKh i j) hμ]
    omega

  let V : Fin n → Fin n → (Fin n ⊕ Fin n →₀ ℕ) → ℤ := fun i j μ =>
    cycEval (fun W => vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)))
      (ratDiv P (f i) (g i))
  let F : Fin n → Fin n → ℤ := fun i j => ∑ μ ∈ (Kz i j).support, (Kz i j).coeff μ * V i j μ
  have hexp : pairNumHom P z z' f g Q (As - Bs) = ∑ i, ∑ j, F i j := by
    rw [pairNumHom_apply]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin := ratDiv_finite_support P (f i) (g i)
    have hW : ∀ W ∈ hfin.toFinset, classNum (Sum.elim z z') ((As - Bs) i) Q W =
        ∑ j, ∑ μ ∈ (Kz i j).support,
          (Kz i j).coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
      intro W hWm
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hWm
      rw [hKs i]
      have h := map_sum (classNumAddHom (Sum.elim z z') Q W) (fun j => pairDiff j * Kz i j)
        Finset.univ
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact classNum_pairDiff_mul (vNumL_add_of_ratDiv_ne_zero hϖ hP (hD i) hWm) z z' j (hKh i j) Q
        (by omega)
    simp only [F, V, cycEval_eq_sum hfin]
    rw [Finset.sum_congr rfl
      (fun W hW' => congrArg (ratDiv P (f i) (g i) W * ·) (hW W hW'))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
    ring
  have hF : ∀ i j, F j i = -F i j := by
    intro i j
    simp only [F]
    rw [hKa j i, support_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hP' : IsModelOver P ((classList (Sum.elim z z') μ ++ Q).length + 1) := by
      rw [hlen i j μ hμ]
      exact hP
    have hc := cycEval_vNumL_comm hC2 hϖ _ hP' (hD i) (hD j)
    simp only [V, coeff_neg]
    rw [hc]
    ring
  rw [hexp]
  have hS : ∑ i, ∑ j, F i j = -∑ i, ∑ j, F i j := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hF i j
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [Algebra O Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra O Φ]
  [IsScalarTower O Ω Φ]

theorem segreVec_algebraMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreVec (fun p => algebraMap Ω Φ (y p)) c = algebraMap Ω Φ (segreVec y c) := by
  simp [segreVec, map_prod]

theorem algebraMap_mem_chartRing_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {z : Ω}
    (hz : z ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Φ z ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c := by
  have hle : chartRing O (segreVec y) c ≤
      (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap
        (IsScalarTower.toAlgHom O Ω Φ) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈
      chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c
    rw [map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]
    exact div_mem_chartRing _ _ _
  exact hle hz

end Lemmas

theorem eq_repr_smul_basis_first {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (w : Module.Basis (Fin N) Ω E) (h0 : 0 < N) (v : E)
    (hv : ∀ j : Fin N, (⟨0, h0⟩ : Fin N) < j → w.repr v j = 0) :
    v = w.repr v ⟨0, h0⟩ • w ⟨0, h0⟩ := by
  conv_lhs => rw [← w.sum_repr v]
  refine Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)
  have hlt : (⟨0, h0⟩ : Fin N) < j := by
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    show 0 < (j : ℕ)
    omega
  rw [hv j hlt, zero_smul]

theorem SegreFlagClosureBirational.proof : SegreFlagClosureBirational.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hcΩ : segreVec y c ≠ 0 := by
    intro h
    apply hc
    rw [segreVec_algebraMap, h, map_zero]
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)
  have hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)

  have hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag.graded c hcΩ i0] at hmem
  obtain ⟨v, hv, hvj, hv0⟩ := hmem
  have hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag'.graded c hcΩ i0] at hmem'
  obtain ⟨v', hv', hvj', hv0'⟩ := hmem'
  have hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0 := by
    rw [← hv0]; exact eq_repr_smul_basis_first w hN v hvj
  have hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0 := by
    rw [← hv0']; exact eq_repr_smul_basis_first w' hN v' hvj'
  have hw' : w' i0 = w.repr (w' i0) i0 • w i0 :=
    eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj
  set u : Ω := w.repr (w' i0) i0 with hudef
  have hu : u ≠ 0 := by
    intro h
    apply w'.ne_zero i0
    rw [hw', h, zero_smul]

  choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv
  choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'
  set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef
  set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef
  have hD : D ≠ 0 := mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)
  have hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m) := by
    intro l m
    have hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k := by
      rw [← hαeq l, hv_eq, map_smul, smul_eq_mul]
    have hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) =
        β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k := by
      rw [← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]
    rw [hDdef, hGdef]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA +
      (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB
  have hprodΦ : ∀ (l : Fin M) (m : Fin M'),
      algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) =
        algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m)) := by
    intro l m
    have := congrArg (algebraMap Ω Φ) (hprod l m)
    simpa only [map_mul] using this

  set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT
  have hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0 := by
    intro j hj
    have : ¬ ((j : ℕ) < 1) := by
      intro h
      apply hj
      ext
      simp only [hi0]
      omega
    simp [flagCoord, this]
  have hfc0 : flagCoord w e t 1 i0 = T := by simp [flagCoord, hi0, hT]
  have hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' =
      (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0))) := by
    intro c'
    rw [segreVec, Fintype.prod_option, Fintype.prod_unique]
    exact congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))

  refine ⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)),
    algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), ?_, ?_⟩
  · intro h0
    apply hc₂
    have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only [mul_zero]
    rw [hseg]
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0
  · have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only
    rw [hseg, hseg]
    have h1 := hprodΦ (c₁ (some ())) (c₁ none)
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 -
      T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace ChernClassOnFlagPair

theorem fieldNum_spec (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type) [∀ k, Fintype (κ k)] :
    IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem append_pullDeg {K K' : Type} {a b : ℕ} (u : Fin a → K → ℤ) (v : Fin b → K → ℤ) :
    Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (u i))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (v j)) =
      fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (Fin.append u v l) := by
  funext l
  induction l using Fin.addCases with
  | left i => simp
  | right j => simp

theorem isVertDiv_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) (hb : b = 0) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b 1 1 := by
  subst hb
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι O) 0 := by
    simpa using IndefiniteRowSideFullHecke.NumbersDVR.Bundles.isMultiHomog_C O (ι := ι) (1 : O)
  refine ⟨⟨0, 0, h1, h1, by simp⟩, ?_, ?_, fun Q hQ _ _ => ⟨1, 1, ⟨0, h1⟩, ⟨0, h1⟩, ?_, ?_, by simp⟩⟩
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem length_classList {K σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls μ).length = μ.degree := by
  simp [classList, Finsupp.card_toMultiset, Finsupp.sum]
  rfl

theorem isFlagPair_self {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (h : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) := by
  refine ⟨h, h, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hij.ne]
  · intro i
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  · intro i
    simp [Module.Basis.repr_self]

end ChernClassOnFlagPair


open ChernClassOnFlagPair in
theorem ChernClassOnFlagPair.proof (h1 : JoinPointFlagModel.Statement)
    (h2 : JoinPointNumbers.Statement) (h3 : FlagModelValueIndependence.Statement)
    (h4 : FlagModelRootIndependence.Statement) (h5 : plainPolynomialPairNumber.Statement)
    (h6 : RootPolynomialNumber.Statement) (h7 : PairNumberExpansionIndependence.Statement)
    (h8 : dividedDifferenceExpansion.Statement) : ChernClassOnFlagPair.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hK hW N E _ _ B B' hBB' w w' x x' f g hfp
  have hW2 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hK, hW⟩
  have hprime : (pointIdeal O y).IsPrime := hW2.2.1.1
  refine ⟨fun k hk1 hk2 Gs hGs q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, hd', hf, hg⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B' hBB' w w' x x' f g hfp
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B' :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B') := ⟨F₀⟩
    have hv : F₀.value O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _) (Fin.append φ.deg' _)
        (Fin.append φ.f _) (Fin.append φ.g _) _ = _
      rw [hd, hd', hf, hg]
    have hW' : ∀ H : MvPolynomial (Fin (N + q)) ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1) H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O y) d (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1)
          (Fin.append g fun _ => 1) H := by
      intro H
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
      simp only [append_pullDeg]
      refine Finset.sum_congr rfl fun l _ => ?_
      induction l using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact (h2 O ϖ hϖ Ω K ι y d hW _ _ _).1 _ _ _ (hfp.vertical i)
      | right j =>
        simp only [Fin.append_right, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, sub_self,
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum_zero_index]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h3 O Ω K ι y d N E B B' hW2 ((BundleExamples.sameGeneric_iff hϖ y B B').mpr hBB')
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => isVertDiv_one hprime _ (sub_self _)) k Q hk2 (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((hW' _).trans ((h5 O K ι (pointIdeal O y) d N x x' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q L Q hQ).trans ?_))
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList L μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [h7 O ϖ hϖ K ι (pointIdeal O y) d hW N x x' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ Gs (h8 N k _ (isHomogeneous_psum N k)) hGs (classList L μ) hlen]
  · have hsame : SameGenericFibre ϖ B B := fun c _ =>
      ⟨fun v hv => ⟨0, by simpa using hv⟩, fun v hv => ⟨0, by simpa using hv⟩⟩
    obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, -, -, -⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B hsame w w x x _ _ (isFlagPair_self hfp.flag)
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B) := ⟨F₀⟩
    have hv : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι F₀.ι')) W d
          (Fin.append F₀.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₀.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y F₀.z)) (C a))) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) W d
          (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (Fin.append x L j))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum _ W d
          (Fin.append φ.deg _) _) _ = _
      rw [hd, append_pullDeg]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h4 O Ω K ι y d N E B B hW2 ((BundleExamples.sameGeneric_iff hϖ y B B).mpr hsame)
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) c G hsym hG hc q L Q hQ a
      ha).trans ?_
    refine hv.trans (((h2 O ϖ hϖ Ω K ι y d hW _ _ _).2 a ha).trans ?_)
    exact h6 O K ι (pointIdeal O y) d N x c G hG hc q L Q hQ a

end GroundTheory.Heights₂.Heights.NumbersDVR
end

