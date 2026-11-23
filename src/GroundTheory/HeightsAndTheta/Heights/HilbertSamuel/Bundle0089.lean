module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphDeg

theorem isMultiHomog_blockForms {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type}
    (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem x'_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (k : K) (i : ι k)
    (hi : (X ⟨k, i⟩ : MRing ι) ∉ P) : G.x' ⟨Sum.inl k, i⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl k, i⟩ : MRing (Sum.elim ι ι₂)) ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  exact hi (Ideal.Quotient.eq_zero_iff_mem.1 (MvPolynomial.C_eq_zero.1 h1))

end BlockGraphDeg


open BlockGraphDeg in
theorem BlockGraphDeg.proof (hGr : GraphStatement) (hImg : BlockGraphImage.Statement)
    (hEx : GenFibreExistsStatement) (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCR : Inter.ChartRankAdjoin.Statement) (hRat : BlockGraphFibreRatio.Statement) :
    BlockGraphDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hx hI
  have hImage := hImg K ι Ω κ y k₀ M N x hI
  have hIm : IsArithVar (imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ))
      (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (D + 1) := by
    rw [hImage]
    exact hx

  have hnv : ∀ u : Unit, ∃ j, blockForms k₀ M ⟨u, j⟩ ∉ mCoordIdeal y := by
    intro u
    obtain ⟨j, hj⟩ := hIm.2.1.2.2 u
    refine ⟨j, fun hm => hj ?_⟩
    rw [imageZ, Ideal.mem_comap]
    change rename inrV (X ⟨u, j⟩) ∈ _
    rw [rename_X, graphIdeal, RingHom.mem_ker, inrV, graphMap, eval₂Hom_X']
    change C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨u, j⟩)) * X u = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero, zero_mul]
  have hΓ := (hGr K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) hy
    (isMultiHomog_blockForms k₀ M) hnv).1
  obtain ⟨G⟩ := hEx Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  choose c hc using hy.2.1.2.2
  let ch : (k : FibreBlock (Sum.inr : Unit → K ⊕ Unit)) → fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k := fun
    | ⟨Sum.inl k, _⟩ => c k
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(k | u), h⟩
    · exact x'_ne_zero G k (c k) (hc k)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := hCR (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit),
      fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(k | u), h⟩, i⟩, rfl⟩
    · exact IntermediateField.mem_bot.2 (hRat D K ι Ω κ y k₀ M N x hy hB hI G k i (c k) (x'_ne_zero G k (c k) (hc k)))
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphFibreRatio

set_option linter.unusedSectionVars false

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) (f : MRing ι) :
    eval s (mConeMap v f) = aeval (fun p => s p.1 * v p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    simp [mConeMap, mul_comm]

theorem aeval_smul_of_isMultiHomog {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) {f : MRing ι}
    {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    aeval (fun p => s p.1 * v p) f = (∏ k, s k ^ d k) * aeval v f := by
  rw [← eval_mConeMap, ProjLine.mConeMap_eq_of_isMultiHomog v hf, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] {v : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal v) : aeval v f = 0 := by
  have h := eval_mConeMap v (fun _ => 1) f
  rw [show mConeMap v f = 0 from hf] at h
  simpa using h.symm

theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : MRing ι) (blockDeg k 1) := by
  classical
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    have hs : ∀ b, (Finsupp.single (⟨k', i⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k', b⟩ = if b = i then 1 else 0 := by
      intro b
      by_cases hb : b = i
      · subst hb
        simp
      · rw [if_neg hb, Finsupp.single_apply, if_neg]
        intro h
        exact hb (eq_of_heq (Sigma.mk.inj h).2).symm
    simp [blockDeg, hs]
  · simp [blockDeg, hk, Sigma.ext_iff]

end Cone

section Graph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (f : MRing ι) :
    graphMap P g (rename (inlV (ι₂ := ι₂)) f) = C (Ideal.Quotient.mk P f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap]
  | add f f' hf hf' =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_add (f := _), hf, hf', map_add (Ideal.Quotient.mk P),
        map_add (C : (MRing ι ⧸ P) →+* MvPolynomial K₂ (MRing ι ⧸ P))]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf, rename_X, map_mul, map_mul]
    congr 1
    rw [graphMap, eval₂Hom_X']
    rfl

theorem mem_iff_aeval_inl {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (f : MRing ι) :
    f ∈ P ↔ aeval (fun p => G.x' (inlV p)) f = 0 := by
  have h : aeval (fun p => G.x' (inlV p)) f = aeval G.x' (rename inlV f) := by
    rw [aeval_rename]
    rfl
  rw [h, ← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]

end Graph

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h.1 j, map_sum, Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

def nForm (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) (l : ι k₀) : MRing (Sum.elim ι (GlobalTheory κ)) :=
  ∑ q : Ix κ, C (N l q) * X (inrV q)

theorem graphMap_nForm {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (l : ι k₀) :
    graphMap (mCoordIdeal y) (blockForms k₀ M) (nForm k₀ N l) =
      C (Ideal.Quotient.mk (mCoordIdeal y) (X ⟨k₀, l⟩)) * X () := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Ideal.Quotient.eq.2 (sub_mem_mCoordIdeal h l), nForm, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨⟩, j⟩ := q
  rw [map_mul, graphMap, eval₂Hom_C, eval₂Hom_X']
  change (Int.castRingHom _) (N l ⟨(), j⟩) * (C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) * X ()) = _
  simp [mul_assoc]

end Block

end BlockGraphFibreRatio


open BlockGraphFibreRatio in
theorem BlockGraphFibreRatio.proof : BlockGraphFibreRatio.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hI G k i j hj
  classical
  set z : (Σ k, ι k) → G.Φ' := fun p => G.x' (inlV p) with hzdef
  have hmem := mem_iff_aeval_inl G
  rw [← hzdef] at hmem
  change z ⟨k, j⟩ ≠ 0 at hj
  change z ⟨k, i⟩ / z ⟨k, j⟩ ∈ _

  have hyj : aeval y (X ⟨k, j⟩ : MRing ι) ≠ 0 := by
    intro h0
    refine hj ?_
    have h1 : (X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y _ = 0
      rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j), h0, map_zero, zero_mul]
    simpa using (hmem _).1 h1

  obtain ⟨n, g', h', hg', hh', hh0, hgh⟩ :=
    hB (blockDeg k 1) (X ⟨k, i⟩) (X ⟨k, j⟩) (isMultiHomog_X k i) (isMultiHomog_X k j) hyj
  have hF : (X ⟨k, i⟩ * h' - g' * X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y hh',
      ProjLine.mConeMap_eq_of_isMultiHomog y hg', ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k i),
      ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j)]
    calc _ = C (aeval y (X ⟨k, i⟩ : MRing ι) * aeval y h' - aeval y g' * aeval y (X ⟨k, j⟩ : MRing ι)) *
          ((∏ k', X k' ^ blockDeg k 1 k') * ∏ k', X k' ^ blockDeg k₀ n k') := by
          rw [map_sub, map_mul, map_mul]
          ring
      _ = 0 := by rw [hgh, sub_self, map_zero, zero_mul]
  have hz := (hmem _).1 hF
  simp only [map_sub, map_mul, aeval_X] at hz
  have hh'z : aeval z h' ≠ 0 := fun h0 => hh0 (aeval_eq_zero_of_mem ((hmem h').2 h0))
  have hratio : z ⟨k, i⟩ / z ⟨k, j⟩ = aeval z g' / aeval z h' := by
    rw [div_eq_div_iff hj hh'z]
    linear_combination hz

  obtain ⟨l, hl⟩ := hy.2.1.2.2 k₀
  have hzl : z ⟨k₀, l⟩ ≠ 0 := fun h0 => hl ((hmem _).2 (by simpa using h0))
  have hw : ∀ a, aeval G.x' (nForm k₀ N a) = algebraMap G.Φ G.Φ' (∑ q, (N a q : G.Φ) * G.x q) := by
    intro a
    simp [nForm, G.compat]
  have hker : ∀ f, aeval G.x' f = 0 ↔ graphMap (mCoordIdeal y) (blockForms k₀ M) f = 0 := by
    intro f
    rw [← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker]
  have hwl : aeval G.x' (nForm k₀ N l) ≠ 0 := by
    intro h0
    rw [hker, graphMap_nForm hI] at h0
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single () 1)) h0
    rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hl h1
  have hcross : ∀ a, aeval G.x' (nForm k₀ N a) * z ⟨k₀, l⟩ = z ⟨k₀, a⟩ * aeval G.x' (nForm k₀ N l) := by
    intro a
    have hX : ∀ p : Σ k, ι k, graphMap (mCoordIdeal y) (blockForms k₀ M) (X (inlV p)) =
        C (Ideal.Quotient.mk (mCoordIdeal y) (X p)) := fun p => by
      rw [← rename_X, graphMap_rename_inlV]
    have h0 := (hker (nForm k₀ N a * X (inlV ⟨k₀, l⟩) - X (inlV ⟨k₀, a⟩) * nForm k₀ N l)).2 (by
      rw [map_sub, map_mul, map_mul, graphMap_nForm hI, graphMap_nForm hI, hX, hX]
      ring)
    rw [map_sub, map_mul, map_mul, aeval_X, aeval_X, sub_eq_zero] at h0
    exact h0
  set c := aeval G.x' (nForm k₀ N l) / z ⟨k₀, l⟩ with hcdef
  have hc : c ≠ 0 := div_ne_zero hwl hzl
  have hwc : ∀ a, aeval G.x' (nForm k₀ N a) = c * z ⟨k₀, a⟩ := by
    intro a
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff hzl, hcross a, mul_comm]

  let s : K → G.Φ' := fun k' => if k' = k₀ then c else 0
  have hs : ∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n) →
      aeval (fun p => s p.1 * z p) f = c ^ n * aeval z f := by
    intro f hf
    rw [aeval_smul_of_isMultiHomog z s hf, Finset.prod_eq_single k₀]
    · simp [s, blockDeg]
    · intro b _ hb
      simp [s, blockDeg, hb]
    · simp
  have hex : ∀ p : Σ k, ι k, ∃ a : G.Φ, algebraMap G.Φ G.Φ' a = s p.1 * z p := by
    rintro ⟨k', a⟩
    by_cases hk : k' = k₀
    · subst hk
      exact ⟨_, ((hw a).symm.trans (hwc a)).trans (by simp [s])⟩
    · exact ⟨0, by simp [s, hk]⟩
  choose u hu using hex
  have hmap : ∀ f : MRing ι, aeval (fun p => s p.1 * z p) f = algebraMap G.Φ G.Φ' (aeval u f) := by
    intro f
    have hfun : (fun p => s p.1 * z p) = algebraMap G.Φ G.Φ' ∘ u := funext fun p => (hu p).symm
    rw [hfun, aeval_algebraMap_apply]
  refine RingHom.mem_range.2 ⟨aeval u g' / aeval u h', ?_⟩
  rw [map_div₀, ← hmap, ← hmap, hs g' hg', hs h' hh', hratio, mul_div_mul_left _ _ (pow_ne_zero n hc)]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegreeIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockResolutionDegreeIntegral

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem ratio_smul {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) :
    A₁.h (fun p => c p.1 * z p) / A₀.h (fun p => c p.1 * z p) = A₁.h z / A₀.h z := by
  have hp : (∏ k, ‖c k‖ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A₁.smul c z hc, A₀.smul c z hc, hdeg, mul_div_mul_left _ _ hp]

theorem smooth_logRatio (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) :
    d.R.A.Smooth (fun x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x))) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm := (contDiffOn_const (c := t)).mul
    ((AnResBridge.contDiffOn_potOf d.R h₁ ((d.R.A.chart j).symm y) j).sub
      (AnResBridge.contDiffOn_potOf d.R h₀ ((d.R.A.chart j).symm y) j))
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  have hz := (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2.2).1
  change t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) /
      A₀.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))) =
    t * (Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) -
      Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))))
  rw [hcy, ratio_smul hdeg c hc, Real.log_div (A₁.pos _ hz).ne' (A₀.pos _ hz).ne']

theorem mInt_blockInterpPot_eq (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (t : ℝ) (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) g =
      mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀ +
        LocPot.ofFun (fun x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x)))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2).1
  have h₀ := A₀.pos _ hz
  have h₁ := A₁.pos _ hz
  change (1 - t) * Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) /
        A₀.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')))
  rw [hcy, ratio_smul hdeg c hc, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
      mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀) (fun _ => 1) := by
  rw [mInt_blockInterpPot_eq d hdeg t]
  exact massIndep d.R.A (fun _ => AnResBridge.potOf d.R A₀)
    (fun _ x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x)))
    (fun _ => AnResBridge.isPotential_potOf d.R h₀) (fun _ => smooth_logRatio d hdeg h₀ h₁ t)

theorem mass_potOf (hGG : GenDegGeomDeg.Statement) (d : HSMBlockDatum D K ι Ω) {A₀ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hdeg : A₀.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) (h₀ : IsSmoothHerm A₀) :
    mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀) (fun _ => 1) =
      (genDeg (mCoordIdeal d.y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) : ℝ) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)
  have hB : IsSmoothHerm B := contDiffOn_const
  have hlog : logNorm B.inv 1 = fun _ => (1 : ℝ) := by
    funext z
    rw [logNorm_inv_one]
    simp [B, HermLine.ofWeight]
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 rfl
  have key := AnResBridge.bridge d.R hex.choose (fun _ => A₀) B.inv 1 d.arith hex.choose_spec
    (fun _ => h₀) (isSmoothHerm_inv hB) hsec
  simp only [hlog] at key
  have hg := hGG K ι Ω d.y D A₀ d.arith h₀
  rw [hdeg] at hg
  rw [← hg]
  unfold geomDeg ptsIntegral
  rw [dite_eq_left hex]
  exact key.symm

end BlockResolutionDegreeIntegral

theorem BlockResolutionDegreeIntegral.proof (hGG : GenDegGeomDeg.Statement) :
    BlockResolutionDegreeIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h0 h1 hs0 hs1 t _
  rw [BlockResolutionDegreeIntegral.mass_eq d (h1.trans h0.symm) hs0 hs1 t]
  exact BlockResolutionDegreeIntegral.mass_potOf hGG d h0 hs0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

