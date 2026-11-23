module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureModel

theorem exists_flag_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by
  have hN : 0 < N := by omega
  by_contra! h0

  let θ : Fin P → Module.Dual Ω E := fun l =>
    ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j
  have hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j := by
    intro l i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : ∀ l, θ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by
      rw [← h0 l]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0 := by
    intro l
    have h := congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj])
      (by simp)] at h
    simpa [show (0 : ℕ) < k by omega] using h
  have hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hw0 l
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)
  simp at this

end SegreFlagClosureModel


open GenericProjClosureDim GenericProjClosureDivisor SegreFlagClosureModel in
theorem SegreFlagClosureModel.proof (hTr : SegreFlagClosureTrdeg.Statement) :
    SegreFlagClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  have hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k) := rfl

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k')
    · exact exists_flag_ne_zero w e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN
    · exact exists_flag_ne_zero w e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN
    · exact ⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ)
        (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy

  have hdy := DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  have hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) := by
    refine ⟨hP, hnt, ?_⟩
    rw [DvrConeDimTrdeg.proof _ _ _ _ hP hnt,
      hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty,
      ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
      show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (k + 1) + 1 by omega]
    norm_cast
  refine ⟨hZ, ?_⟩

  rw [hpt] at hZ ⊢
  have hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP' le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureTrdeg

theorem sum_flagCoord {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (a : Fin N → Φ) :
    ∑ j, flagCoord w e t k j * a j =
      ∑ j : Fin k, flagCoord w e t k (Fin.castLE hkN j) * a (Fin.castLE hkN j) := by
  calc ∑ j, flagCoord w e t k j * a j
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hkN), flagCoord w e t k j * a j :=
        (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    _ = _ := Finset.sum_map _ _ _
  intro j _ hj
  have hjk : ¬ (j : ℕ) < k := fun h => hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [flagCoord, hjk]

theorem flagCoord_indep {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun j : Fin k => flagCoord w e t k (Fin.castLE hkN j)) := by
  classical
  let _ := w.invertibleToMatrix e
  have hS := PairConeLinesIndep.linearChange_indep (w.toMatrix e) (isUnit_of_invertible _) t ht
  have h := hS.comp (Fin.castLE hkN) (Fin.castLE_injective hkN)
  convert h using 1
  funext j
  simp [flagCoord, Module.Basis.toMatrix_apply, j.isLt]

end SegreFlagClosureTrdeg


open SegreFlagClosureTrdeg in
theorem SegreFlagClosureTrdeg.proof (halg : SegreFlagConeAlg.Statement) : SegreFlagClosureTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
    k hk hkN
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN
  set z := flagClosurePt y w e φ φ' t k with hzdef

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (z p) * X p.1
  let xs : Fin k ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin k => C (z ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (z ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O z) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O z)).trdeg_eq
    have e2 : (pointConeMap O z).range = Algebra.adjoin O (Set.range gZ) := aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range xs ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  let b := Pi.basisFun Ω (Fin k)
  let ψ : Fin k → Module.Dual Ω (Fin k → Ω) :=
    fun i => b.dualBasis.equivFun.symm (fun j => φ (l i) (w (Fin.castLE hkN j)))
  have hψb : ∀ i j, ψ i (b j) = φ (l i) (w (Fin.castLE hkN j)) := by
    intro i j
    rw [← Module.Basis.dualBasis_equivFun]
    simp [ψ, Finsupp.single_apply]
  have hψ : LinearIndependent Ω ψ := hl.map' b.dualBasis.equivFun.symm.toLinearMap b.dualBasis.equivFun.symm.ker
  have hind' := PairConeLinesIndep.proof Ω Φ K k (Fin k → Ω) b ψ hψ
    (fun j => flagCoord w e t k (Fin.castLE hkN j)) (flagCoord_indep hkN w e t ht) _ hm'
  have hxs : xs = Sum.elim
      (fun i : Fin k => C (∑ j, flagCoord w e t k (Fin.castLE hkN j) * algebraMap Ω Φ (ψ i (b j))) * X (some none))
      (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ)) := by
    funext i
    rcases i with i | _
    · simp only [xs, Sum.elim_inl, hψb]
      congr 2
      exact sum_flagCoord hkN w e t _
    · rfl
  rw [← hxs] at hind'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let fr : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    fr.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) xs :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := AdjoinTrdegAdd.proof O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ)
    (Fin k ⊕ Unit) xs hxZ hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutContraction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutContraction

theorem pullDeg_comp_of_eq_zero {K K' : Type*} (j : K ↪ K') (b : K' → ℤ)
    (hb : ∀ o, o ∉ Set.range j → b o = 0) : FieldNumbers.pullDeg j (b ∘ j) = b := by
  funext o
  by_cases ho : ∃ a, j a = o
  · obtain ⟨a, rfl⟩ := ho
    exact j.injective.extend_apply (b ∘ j) 0 a
  · rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ ho, Pi.zero_apply]
    exact (hb o (by simpa [Set.mem_range] using ho)).symm

theorem withBot_le_of_lt_succ (a : WithBot ℕ∞) (m : ℕ) (h : a < ((m + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((m : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe c =>
      have h' : (((c : ℕ) : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hc : c < m + 1 := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show (((c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((m : ℕ) : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : c ≤ m))

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]


omit [IsDomain O] [IsDiscreteValuationRing O] [∀ o, Fintype (ι' o)] in
theorem ratDiv_support {P W : Ideal (MRing ι' O)} (hPm : IsMultiHomogIdeal P) {cs ch : K' → ℕ}
    {s h : MRing ι' O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  have key : ∀ {c : K' → ℕ} {u : MRing ι' O}, IsMultiHomog u c → divCycle P u W ≠ 0 →
      W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
    intro c u hu hne
    unfold divCycle at hne
    split_ifs at hne with hW'
    · exact ⟨hW'.1.1.1, le_sup_left.trans hW'.1.1.2,
        MinimalPrimeMultiHomog.full O K' ι' _ W (SupSpanMultiHomog.full O K' ι' P u c hPm hu) hW'.1⟩
    · exact absurd rfl hne
  by_cases h1 : divCycle P s W = 0
  · exact key hh fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key hs h1

theorem vNumL_eq_zero_of_contract {ϖ : O} (hϖ : Irreducible ϖ) {P W : Ideal (MRing ι' O)} {n : ℕ}
    (hP : IsModelOver P n) [hWp : W.IsPrime] (hPW : P ≤ W) (hWm : IsMultiHomogIdeal W)
    (hϖW : (C ϖ : MRing ι' O) ∈ W) {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K')
    (hcon : FieldNumbers.relDim (FieldNumbers.contractPrime j (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι' O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι' O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι' O) P W hlt
  rw [hP.dim] at hdrop
  obtain ⟨hQp, -, -, -⟩ := SpecialIdealCorresp.full O ϖ hϖ K' ι' P W hWp hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hWm
  have hdimQ : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' + 1 : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW]
    refine lt_natCast_of_add_one_le ?_
    have e : l.length + Fintype.card K' + 1 = l.length + 1 + Fintype.card K' := by omega
    rw [e]
    exact hdrop
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ¬ IsRelevant (specialIdeal W) ∨ ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm hcase l.get
  · push Not at hcase
    obtain ⟨hrel, hge⟩ := hcase
    have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (withBot_le_of_lt_succ _ _ hdimQ) hge
    have hrelQ : FieldNumbers.relDim (specialIdeal W) = ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrel⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (pullDeg_comp_of_eq_zero j _ (hlj _ (List.get_mem l i))).symm

end SegreFlagCutContraction


open SegreFlagCutContraction in
theorem SegreFlagCutContraction.proof (hModel : SegreFlagClosureModel.Statement)
    (hProj : SegreFlagCutProjection.Statement) : SegreFlagCutContraction.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hH : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) (d + k) := by
    have h := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht (k + 1) (by omega) (by omega)).1
    simpa using h
  obtain ⟨hp1, hp2⟩ := hProj O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_⟩
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW Function.Embedding.some
      (hp1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    cases o with
    | none => exact hl0 b hb
    | some o => exact absurd ⟨o, rfl⟩ ho
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW secondFactorBlocks
      (hp2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    rcases o with _ | _ | o
    · exact absurd ⟨none, rfl⟩ ho
    · exact hl0 b hb
    · exact absurd ⟨some o, rfl⟩ ho

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

