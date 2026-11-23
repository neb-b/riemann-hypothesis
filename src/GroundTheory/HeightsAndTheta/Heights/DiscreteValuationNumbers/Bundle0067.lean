module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open FlagBundleSectionDivProof GenericProjClosureDivisor in
theorem SegreFlagCutDivisor.proof (hSpec : SegreFlagCutSpecialize.Statement)
    (hChart : SegreFlagCutChart.Statement) : SegreFlagCutDivisor.Statement := by
  have hModel : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSat : MultAtOfSaturated.Statement.{0} := MultAtOfSaturated.proof
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk cs ch s h hs hh hdeg hsP hhP hval W hW
  classical
  have hPp : (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))).IsPrime := RingHom.ker_isPrime _
  have hQp : (pointIdeal O (flagClosurePt y w e φ φ' t k)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨hPQ, hspec⟩ := hSpec O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  have hτ : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
    intro h0
    exact hsP (mem_of_homog hs (by rw [hval, h0, zero_mul]))
  by_cases hWc : W.IsPrime ∧ IsRelevant W ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hWc
    obtain ⟨cl, cm, l, μ, u, hl, hμ, hdl, hμW, huW, hlv, hl0, hsat⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk W
        hWp hWrel hPW hW
    have hμP : μ ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := fun h' => hμW (hPW h')
    have hlP : l ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      intro h'
      have h0 := aeval_eq_zero_of_mem h'
      rw [hlv] at h0
      exact hμP (mem_of_homog hμ ((mul_eq_zero.mp h0).resolve_left hτ))
    have huW' : ∀ n : ℕ, u ^ n ∉ W := fun n h' => huW (hWp.mem_of_pow_mem n h')
    have hdeg' : cs + cm = cl + ch := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : s * μ - l * h ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      have h2 := hl.mul hh
      rw [← hdeg'] at h2
      refine mem_of_homog (b := cs + cm) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp
        (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))) ?_
      rw [map_sub, map_mul, map_mul, hval, hlv]
      ring
    rw [ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff]
    unfold ratDiv
    rw [divCycle_eq_zero_of_not_mem hμW, sub_zero]
    have hlQ : 0 < k → l ∈ pointIdeal O (flagClosurePt y w e φ φ' t k) := fun _ =>
      mem_of_homog hl (hspec l μ hlv)
    split_ifs with hc
    · obtain ⟨hkpos, rfl⟩ := hc
      obtain ⟨hmin, hmult⟩ := hSat O (Option (Option K)) (bundleIdx (bundleIdx ι M) M') _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hlQ hkpos)))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact ⟨_, huW' n, hn⟩)
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hWrel⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h'
        · exact h'.1
        · exact absurd rfl hne
      have hlW : l ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l))
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact hl0 hk0 hlW
      · have hQW : pointIdeal O (flagClosurePt y w e φ φ' t k) ≤ W := fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW' n)
        have hPQ' : pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) <
            pointIdeal O (flagClosurePt y w e φ φ' t k) :=
          lt_of_le_of_ne hPQ (fun h' => hlP (by rw [h']; exact hlQ hkpos))
        exact hc ⟨hkpos, (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm⟩
  · have h0 : ∀ z, divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) z W = 0 := fun z => by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h', hr⟩
      exact hWc ⟨h'.1.1, hr, le_sup_left.trans h'.1.2⟩
    have hWQ : ¬ (0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k)) := by
      rintro ⟨hkpos, rfl⟩
      exact hWc ⟨hQp, (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
        Φ e t ht k hkpos hk.le).1.multiProj.relevant, hPQ⟩
    rw [ite_eq_right hWQ]
    simp [ratDiv, h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutLiesOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutLiesOverProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ικ : κ → Type} [∀ o, Fintype (ικ o)] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem le_comap_of_chart (pt : (Σ o, ικ o) → Φ) {A F : Type*} [CommRing A] [FunLike F A (MRing ικ O)]
    [RingHomClass F A (MRing ικ O)] (ρ : F) (Q : Ideal A) (u : MRing ικ O) (τ : Φ) {cs ch dl dm : κ → ℕ}
    {s h l μ : MRing ικ O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hl : IsMultiHomog l dl)
    (hμ : IsMultiHomog μ dm) (hdeg : cs + dm = dl + ch) (hsP : s ∉ pointIdeal O pt)
    (hhP : h ∉ pointIdeal O pt) (hsv : aeval pt s = τ * aeval pt h) (hlv : aeval pt l = τ * aeval pt μ)
    (hsat : ∀ q ∈ Q, ∃ n : ℕ, u ^ n * ρ q ∈ pointIdeal O pt ⊔ Ideal.span {l})
    {W : Ideal (MRing ικ O)} (hμW : μ ∉ W) (huW : ∀ n : ℕ, u ^ n ∉ W)
    (hPW : pointIdeal O pt ≤ W) (hW : ratDiv (pointIdeal O pt) s h W ≠ 0) : Q ≤ W.comap ρ := by
  have : (pointIdeal O pt).IsPrime := RingHom.ker_isPrime _
  have hμP : μ ∉ pointIdeal O pt := fun h' => hμW (hPW h')
  have hsv0 : aeval pt s ≠ 0 := fun h0 => hsP (GenericProjClosureDivisor.mem_of_homog hs h0)
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hsv0 (by rw [hsv, zero_mul])
  have hμv : aeval pt μ ≠ 0 := fun h0 => hμP (GenericProjClosureDivisor.mem_of_homog hμ h0)
  have hlP : l ∉ pointIdeal O pt := fun h' =>
    mul_ne_zero hτ hμv (hlv ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h')
  have hdiff : s * μ - l * h ∈ pointIdeal O pt := by
    have h2 := hl.mul hh
    rw [← hdeg] at h2
    have h1 : IsMultiHomog (s * μ - l * h) (cs + dm) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
    refine GenericProjClosureDivisor.mem_of_homog h1 ?_
    rw [map_sub, map_mul, map_mul, hsv, hlv]
    ring
  have hrat := congrFun (ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff) W
  have hμ0 : divCycle (pointIdeal O pt) μ W = 0 := by
    unfold divCycle
    rw [dite_eq_right]
    rintro ⟨h', -⟩
    exact hμW (h'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)))
  have hl0 : divCycle (pointIdeal O pt) l W ≠ 0 := by
    rw [hrat] at hW
    unfold ratDiv at hW
    rwa [hμ0, sub_zero] at hW
  have hmin : W ∈ (pointIdeal O pt ⊔ Ideal.span {l}).minimalPrimes := by
    unfold divCycle at hl0
    split_ifs at hl0 with h'
    · exact h'.1
    · exact absurd rfl hl0
  have hWp : W.IsPrime := hmin.1.1
  intro q hq
  obtain ⟨n, hn⟩ := hsat q hq
  exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW n)


omit [Fintype κ] [DecidableEq κ] [∀ o, Fintype (ικ o)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem support_ratDiv {P W : Ideal (MRing ικ O)} {s h : MRing ικ O} (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  have key : ∀ v, divCycle P v W ≠ 0 → W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    intro v hv
    unfold divCycle at hv
    split_ifs at hv with h'
    · exact ⟨h'.1.1.1, le_sup_left.trans h'.1.1.2, h'.2⟩
    · exact absurd rfl hv
  by_cases h1 : divCycle P s W = 0
  · exact key h fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key s h1

end SegreFlagCutLiesOverProof


open SegreFlagCutLiesOverProof in
theorem SegreFlagCutLiesOver.proof (hChart : SegreFlagCutChartSection.Statement) :
    SegreFlagCutLiesOver.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hchart : ∀ (s h : MRing (bundleIdx (bundleIdx ι M) M') O) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
      ∃ c : ∀ j, ι j, segreVec y c ≠ 0 ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W ∧
        ∀ m : K → ℕ, (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j) ∉ W := by
    intro s h W hW
    obtain ⟨hWp, hPW, hWr⟩ := support_ratDiv hW
    choose c hc using fun j : K => hWr (some (some j))
    refine ⟨c, ?_, hPW, ?_⟩
    · unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro j _ hj
      apply hc j (hPW ?_)
      refine GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      simp [flagClosurePt, pairProjCoord, projCoord, hj]
    · intro m hm
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp hm
      exact hc j (hWp.mem_of_pow_mem _ hj)
  have hdeg : ∀ {cs ch dl dm : Option (Option K) → ℕ} {D : Option (Option K) → ℤ},
      (fun o => (cs o : ℤ) - ch o) = D → (fun o => (dl o : ℤ) - dm o) = D → cs + dm = dl + ch := by
    intro cs ch dl dm D h1 h2
    funext o
    have e1 := congrFun h1 o
    have e2 := congrFun h2 o
    simp only [Pi.add_apply] at e1 e2 ⊢
    omega
  refine ⟨fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_, fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_⟩
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩, -⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨-, ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SegreFlagCutSection.proof (hModel : SegreFlagClosureModel.Statement)
    (hForms : SegreFlagCutForms.Statement) (hDiv : SegreFlagCutDivisor.Statement)
    (hD0 : SegreFlagDegreeZero.Statement) : SegreFlagCutSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk r a ha
  classical
  set I := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hI
  have hIp : I.IsPrime := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht (k + 1) (Nat.le_add_left 1 k) hk).1.multiProj.isPrime
  have hpt : ∀ (j : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t j ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl
  have hlift : ∀ i, liftPairForm M M' (a i) ∉ I := fun i hm =>
    ha i ((liftPairForm_mem_iff (hpt (k + 1)) _).1 hm)
  obtain ⟨f₃, g₃, hD₃, hv₃, hk₃⟩ := hD0 O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk

  let bad : MRing (bundleIdx (bundleIdx ι M) M') O → Set (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) :=
    fun z => {Q | Q ∈ (I ⊔ Ideal.span {z}).minimalPrimes ∧ IsRelevant Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q}
  let T := bad f₃ ∪ bad g₃ ∪ ⋃ i, bad (liftPairForm M M' (a i))
  have hbfin : ∀ z, (bad z).Finite := fun z =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I ⊔ Ideal.span {z})).subset fun Q hQ => hQ.1
  have hTfin : T.Finite := ((hbfin _).union (hbfin _)).union (Set.finite_iUnion fun i => hbfin _)
  have hbad : ∀ z, ∀ Q ∈ bad z, Q.IsPrime ∧ IsRelevant Q ∧ I ≤ Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q :=
    fun _ _ hQ => ⟨Ideal.IsMinimalPrime.isPrime hQ.1, hQ.2.1,
      le_sup_left.trans (Ideal.IsMinimalPrime.le hQ.1), hQ.2.2⟩
  obtain ⟨cs, ch, s, h, hs, hh, hdeg, hsI, hhI, hval, havoid⟩ :=
    hForms O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      hTfin.toFinset (by
        intro Q hQ
        rcases (hTfin.mem_toFinset.1 hQ) with (hQ | hQ) | hQ
        · exact hbad _ Q hQ
        · exact hbad _ Q hQ
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hQ
          exact hbad _ Q hi)
  have hdiv := hDiv O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
    cs ch s h hs hh hdeg hsI hhI hval
  refine ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsI, hhI, hval, hdiv, hD₃, hv₃, hk₃, ?_⟩
  intro H hH hϖH
  by_cases hh0 : divCycle I h H = 0
  ·
    have hs0 : divCycle I s H ≠ 0 := hH.resolve_right (not_not.2 hh0)
    have hne : ratDiv I s h H ≠ 0 := by
      unfold ratDiv
      rw [hh0, sub_zero]
      exact hs0
    rw [hdiv H hϖH] at hne
    split_ifs at hne with hc
    · obtain ⟨hk0, rfl⟩ := hc
      obtain ⟨hf, hg, -⟩ := hk₃ hk0
      exact ⟨hf, hg, fun i hm => ha i ((liftPairForm_mem_iff (hpt k) _).1 hm)⟩
    · exact absurd rfl hne
  ·
    obtain ⟨hmin, hrel⟩ := relevant_minimal_of_divCycle_ne_zero hh0
    have hhH : h ∈ H :=
      Ideal.IsMinimalPrime.le hmin (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    have avoid : ∀ z, z ∉ I → (H ∈ bad z → H ∈ T) → z ∉ H := by
      intro z hz hT hzH
      exact havoid H (hTfin.mem_toFinset.2 (hT ⟨mem_minimalPrimes_sup_span_of_mem hmin hz hzH, hrel, hϖH⟩)) hhH
    exact ⟨avoid f₃ hD₃.num_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_left _ h'),
      avoid g₃ hD₃.den_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_right _ h'),
      fun i => avoid _ (hlift i) fun h' => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, h'⟩)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagProjSpecialDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem comap_C_pointIdeal {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by
  ext a
  simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
    MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]
  exact ⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩

theorem specialIdeal_dim_add_one_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by
  set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  have e1 := (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 := (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P
    (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) := h0
    rw [hPC, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

theorem relDim_specialIdeal_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have h := (specialIdeal_dim_add_one_le hϖ P hPC).trans hdim
  unfold FieldNumbers.relDim specialIdeal
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
    P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

theorem SegreFlagProjSpecialDim.proof (hDim : PrimeDimLeTrdeg.Statement) (hTr : FlagProjTrdegLe.Statement) :
    SegreFlagProjSpecialDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _
    e t ht k hk
  obtain ⟨h1, h2⟩ := hTr O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk

  have hVt : (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat = ((d + Fintype.card K : ℕ) : ℕ∞) := by
    have h := DvrConeDimTrdeg.proof O K ι _ hV.multiProj hV.noTorsion
    rw [hV.dim] at h
    have h0 : ((d + 1 + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      exact_mod_cast h
    have h' : ((d + Fintype.card K : ℕ) : ℕ∞) + 1 = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      rw [← h0]; push_cast; ring
    exact (WithTop.add_right_cancel ENat.one_ne_top h').symm

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      simp [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, ha]
    rwa [hV.noTorsion, Ideal.mem_bot] at hmem
  have hOΦ : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    exact (algebraMap Ω Φ).injective.comp hOΩ

  have key : ∀ {K' : Type} [Fintype K'] [DecidableEq K'] (j : K' ↪ Option (Option K)), Fintype.card K' = Fintype.card K + 1 →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
          pointIdeal O (flagProjPt j y w e φ φ' t k)) ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt j y w e φ φ' t k))) <
        ((d + k : ℕ) : WithBot (WithTop ℤ)) := by
    intro K' _ _ j hcard hle
    have hP : (pointIdeal O (flagProjPt j y w e φ φ' t k)).IsPrime := by
      unfold pointIdeal
      exact RingHom.ker_isPrime _
    have hPC := comap_C_pointIdeal hOΦ (flagProjPt j y w e φ φ' t k)
    refine relDim_specialIdeal_lt hϖ _ hPC (d + k) ((hDim O K' _ _ hP hPC).trans ?_)
    have ht : Cardinal.toENat _ ≤ Cardinal.toENat _ := OrderHomClass.mono Cardinal.toENat hle
    simp only [map_add (f := _), map_natCast, hVt] at ht
    have : ((Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
        pointIdeal O (flagProjPt j y w e φ φ' t k))).toENat + 1 : ℕ∞) ≤ ((d + k + Fintype.card K' : ℕ) : ℕ∞) := by
      rw [hcard]
      calc _ ≤ ((d + Fintype.card K : ℕ) : ℕ∞) + (k : ℕ∞) + 1 := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast this
  exact ⟨key Function.Embedding.some (by simp) h1, key secondFactorBlocks (by simp) h2⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

