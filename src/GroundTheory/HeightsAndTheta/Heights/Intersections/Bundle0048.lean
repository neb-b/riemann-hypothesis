module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.AevalNeZeroOfNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChartFiniteness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_rename_eq (G : GenFibre v P') (A : MRing ι) :
    aeval G.x' (rename v A) = algebraMap G.Φ G.Φ' (aeval G.x A) := by
  rw [aeval_rename]
  have h : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
  rw [h, MvPolynomial.aeval_algebraMap_apply]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_eq_zero_of_mem (G : GenFibre v P') {f : MRing ι'} (hf : f ∈ P') : aeval G.x' f = 0 := by
  rw [← G.genericFibre_ker_target] at hf
  exact hf


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_ne_zero_of_not_mem (G : GenFibre v P') {f : MRing ι} (hf : f ∉ imageZ v P') : aeval G.x f ≠ 0 := by
  rw [← G.ker_x] at hf
  exact hf

def coeffPoly {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) : Polynomial F :=
  ∑ j : Fin (m + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)

theorem coeffPoly_coeff_last {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) :
    (coeffPoly a).coeff m = a (Fin.last m) := by
  unfold coeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro b _ hb
    have : (m : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext (by simp [h]))
    simp [this]
  · simp

end ChartFiniteness


open ChartFiniteness in
theorem ArithmeticIntersectionChartFinite.of_blockRatioAlg (hR : BlockRatioAlg.Statement) : ArithmeticIntersectionChartFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨q, rfl⟩
  apply IsAlgebraic.isIntegral
  set c : Σ k', ι' k' := ⟨q.1.1, j q.1⟩ with hc
  have hc0 : G.x' c ≠ 0 := hj q.1
  have hcP : (X c : MRing ι') ∉ P' := by
    intro h
    apply hc0
    have := aeval_eq_zero_of_mem G h
    rwa [aeval_X] at this
  obtain ⟨m, A, a, -, hAm, hmem⟩ := hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ c rfl hcP
  refine ⟨coeffPoly fun i => aeval G.x (A i), ?_, ?_⟩
  · intro h0
    have := coeffPoly_coeff_last fun i => aeval G.x (A i)
    rw [h0, Polynomial.coeff_zero] at this
    exact aeval_ne_zero_of_not_mem G hAm this.symm
  · have hsum := aeval_eq_zero_of_mem G hmem
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, aeval_X, aeval_rename_eq] at hsum
    have hpow : G.x' c ^ m ≠ 0 := pow_ne_zero _ hc0
    unfold coeffPoly
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    apply (mul_left_inj' hpow).mp
    rw [zero_mul, Finset.sum_mul, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.2
    rw [div_pow, mul_assoc, mul_assoc]
    congr 1
    have e : G.x' c ^ m = G.x' c ^ (i : ℕ) * G.x' c ^ (m - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    change G.x' _ ^ (i : ℕ) / G.x' c ^ (i : ℕ) * (G.x' c ^ (i : ℕ) * G.x' c ^ (m - i)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hc0)]

theorem ArithmeticIntersectionChartFinite.proof : ArithmeticIntersectionChartFinite.Statement :=
  ArithmeticIntersectionChartFinite.of_blockRatioAlg BlockRatioAlg.proof

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsNormalise
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsInAffineChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
theorem exists_normalise {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by
  obtain ⟨s, hs, hzs⟩ := hzz
  let d : K' → ℂ := fun k' =>
    if h : k' ∈ Set.range κ then c h.choose / s h.choose else (z' ⟨k', j ⟨k', h⟩⟩)⁻¹
  have hdk : ∀ k, d (κ k) = c k / s k := by
    intro k
    have h : κ k ∈ Set.range κ := ⟨k, rfl⟩
    have hk : h.choose = k := hv.1 h.choose_spec
    simp only [d, dif_pos h, hk]
  have hd : ∀ k, d k ≠ 0 := by
    intro k'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := h
      rw [hdk]
      exact div_ne_zero (hc k) (hs k)
    · simp only [d, dif_neg h]
      exact inv_ne_zero (hj ⟨k', h⟩)
  refine ⟨d, hd, mcPts_smul hP' d hd hz', fun p => ?_, fun k => ?_⟩
  · have h1 : z' (v p) = s p.1 * z p := congrFun hzs p
    rw [hv.2.2.1 p, hdk, h1]
    field_simp [hs p.1]
  · have h : k.1 ∉ Set.range κ := k.2
    simp only [d, dif_neg h]
    exact inv_mul_cancel₀ (hj k)


omit [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem eq_of_normalised {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {j : ∀ k : FibreBlock κ, ι' k.1} {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    {z₁ z₂ : (Σ k', ι' k') → ℂ} (h₁v : ∀ p, z₁ (v p) = w p) (h₁j : ∀ k : FibreBlock κ, z₁ ⟨k.1, j k⟩ = 1)
    (h₂v : ∀ p, z₂ (v p) = w p) (h₂j : ∀ k : FibreBlock κ, z₂ ⟨k.1, j k⟩ = 1) (h : SameOrbit z₁ z₂) :
    z₁ = z₂ := by
  obtain ⟨t, -, ht⟩ := h
  have ht1 : ∀ k', t k' = 1 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      obtain ⟨i, hi⟩ := hw k
      have e := congrFun ht (v ⟨k, i⟩)
      simp only [h₁v, h₂v, hv.2.2.1] at e
      have e' : (t (κ k) - 1) * w ⟨k, i⟩ = 0 := by rw [sub_mul, ← e]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hi)
    · have e := congrFun ht ⟨k', j ⟨k', hk⟩⟩
      have e1 : z₁ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₁j ⟨k', hk⟩
      have e2 : z₂ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₂j ⟨k', hk⟩
      simp only [e1, e2, mul_one] at e
      exact e.symm
  rw [ht]
  funext q
  simp [ht1]

end GenericPointsInAffineChart


open GenericPointsInAffineChart PullbackDegreeCount in
theorem GenericPointsInAffineChart.proof (hFin : ArithmeticIntersectionChartFinite.Statement) (hNorm : ChartNormCount.Statement)
    (hOrb : OrbitCompNonvanish.Statement) : GenericPointsInAffineChart.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  obtain ⟨E, hE, hEw⟩ := hNorm K ι K' ι' κ v P' n G j hv hP' hP hj (hFin K ι K' ι' κ v P' n G j hv hP' hP hj)
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  have hP'h : IsMultiHomogIdeal P' := hP'.2.1.2.1
  obtain ⟨D, a, hD, hDP, hDz⟩ := hOrb K ι (imageZ v P') E hPh hE
  refine ⟨D, a, hD, hDP, fun z hz hDz0 => ?_⟩
  obtain ⟨c, hc, hEc⟩ := hDz z hDz0
  have hw : (fun p => c p.1 * z p) ∈ mcPts (imageZ v P') := mcPts_smul hPh c hc hz
  obtain ⟨hfin, hcard, hnz⟩ := hEw _ hw hEc
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hN
  let orb : ((Σ k', ι' k') → ℂ) → Set ((Σ k', ι' k') → ℂ) := fun z' => {z'' | SameOrbit z'' z'}
  have himg : ptsOverChart P' κ v j z = orb '' N := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hzz, hjz⟩
      obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
      have hs : SameOrbit (fun q => d q.1 * z' q) z' := ⟨d, hd, rfl⟩
      refine ⟨_, ⟨hm, hdv, hdj⟩, ?_⟩
      ext y
      exact ⟨fun h => sameOrbit_comp h hs, fun h => sameOrbit_comp h (sameOrbit_flip hs)⟩
    · rintro ⟨z', ⟨hz', hzv, hzj⟩, rfl⟩
      refine ⟨z', hz', rfl, ⟨c, hc, funext hzv⟩, fun k => ?_⟩
      rw [hzj k]
      exact one_ne_zero
  have hinj : Set.InjOn orb N := by
    intro z₁ h₁ z₂ h₂ h12
    have hmem : z₁ ∈ orb z₁ := sameOrbit_self z₁
    rw [h12] at hmem
    exact eq_of_normalised hv hw.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 hmem
  refine ⟨himg ▸ hfin.image orb, ?_, fun z' hz' hzz hjz q hq => ?_⟩
  · rw [himg, hinj.ncard_image, hcard]
  · obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
    have h := hnz _ hm hdv hdj q hq
    exact right_ne_zero_of_mul h

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtra
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

theorem pullbackPushforward_holds.proof (hGen : BlockGenFinite.Statement) (hIsol : FibreIsolFinite.Statement) :
    pullbackPushforward_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv hP' hP hΨ
  exact ⟨fun j => pullbackPushforward_holds.pullBad_null R hGen hv hP' hP Ψ hΨ j,
    fun y => pullbackPushforward_holds.pullFib_finite R hIsol hv hP' hP Ψ hΨ y⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreOverFinite.proof (h : FibreIncomp.Statement) : FibreOverFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  refine (divSupp_finite P' (rename v s)).subset fun W' hW' => ?_
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    rw [← hW'.2.2] at hsW
    exact hsW
  exact ((FibreDivSupp.proof h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW W').mp ⟨hW', hsW'⟩).1

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRankAdjoin.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem SemilocRankAdjoin.isMultiHomogIdeal_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι →+* MRingOver ℚ ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, fun m hm => ha m (MvPolynomial.support_map_subset _ _ hm)⟩

theorem SemilocRankAdjoin.chain (hT : ChartScalingIndep.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') (i' : ∀ k', ι' k')
    (F : Type) [Field F] [Algebra F G.Φ] [Algebra F G.Φ'] [IsScalarTower F G.Φ G.Φ'] (hv : IsBlockMap κ v)
    (hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0)
    (hmh : IsMultiHomogIdeal (RingHom.ker (aeval G.x' : MRingOver F ι' →ₐ[F] G.Φ'))) :
    IntermediateField.relfinrank
        (IntermediateField.adjoin F (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩)) := by
  let y' : (Σ k', ι' k') → G.Φ' := fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩
  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom F G.Φ G.Φ').fieldRange
  let L₀ := IntermediateField.adjoin F (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin F (Set.range y')
  let E := IntermediateField.adjoin F (Set.range t)
  have mono : ∀ {A B : Set G.Φ'}, A ⊆ B → IntermediateField.adjoin F A ≤ IntermediateField.adjoin F B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => SemilocRankAdjoin.chart_congr G.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          have hq : G.x' (v q) = y' (v q) * t q.1 := by
            show _ = G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom F G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin F
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩) := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_)
      (((le_sup_right : E ≤ L₀ ⊔ E).trans hL₀E.le).trans le_sup_left)) (sup_le ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hv.2.2.2 q hq
        exact (le_sup_left : Φ₁ ≤ _) (hyv r)
      · exact (le_sup_right : IntermediateField.adjoin _ _ ≤ _)
          (IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩)
    · rw [← hL₀E]
      exact sup_le_sup_right (mono (Set.range_comp_subset_range v y')) E
    · refine (mono ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨q.1.1, q.2⟩, rfl⟩
  have hindep : AlgebraicIndependent L t := (hT F G.Φ' K' ι' G.x' i' hx hmh).comp κ hv.1
  rw [← AdjoinIndepRelfinrank.proof F G.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep,
    FinrankAdjoinRange.proof F G.Φ G.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

theorem SemilocRankAdjoin.proof (hF : SemilocRankFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocRankAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' hZ hs hsP hW hi'

  have hker : ∀ f : MRing ι', aeval G.x' f = 0 ↔ f ∈ P' := fun f => by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
  have : CharZero G.Φ' := charZero_of_inj_zero fun m hm => by
    have h : (C (m : ℤ) : MRing ι') ∈ P' := (hker _).1 (by rw [aeval_C]; exact_mod_cast hm)
    have h' : (m : ℤ) ∈ P'.comap (C : ℤ →+* MRing ι') := h
    rw [hP'.2.2.1, Ideal.mem_bot] at h'
    exact_mod_cast h'
  have : CharZero G.Φ := (RingHom.charZero_iff (algebraMap G.Φ G.Φ').injective).2 inferInstance
  have : IsScalarTower ℚ G.Φ G.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

  have hkerQ : RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ') =
      P'.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι' →+* MRingOver ℚ ι') := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k', ι' k') (R := ℤ) (S := ℚ)
    have _ : IsLocalization ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι') :=
      MvPolynomial.isLocalization _ _
    refine (IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι')
      (RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ'))).symm.trans ?_
    congr 1
    ext f
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_def, aeval_map_algebraMap, hker]
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' ((hker _).1 (by rw [aeval_X, h]))
  rw [hF K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi',
    SemilocRankAdjoin.chain hT G i' ℚ hv hx (hkerQ ▸ SemilocRankAdjoin.isMultiHomogIdeal_map hP'.2.1.2.1)]

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists

theorem ThmIExists.proof (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StCentreOverW
section

end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartNormPts
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ChartNormPts.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∀ z' : (Σ k', ι' k') → ℂ, (fun p => z' (v p)) ∈ mcPts (imageZ v P') →
      (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) (fun q => z' ⟨q.1.1, q.2⟩) F = 0)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

