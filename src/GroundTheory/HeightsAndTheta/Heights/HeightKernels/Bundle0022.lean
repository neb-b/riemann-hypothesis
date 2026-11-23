module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootPointsFiniteAlt

variable {K : Type*} {ι : K → Type*}

def homog (q : Polynomial ℤ) (p a : Σ k, ι k) : MRing ι :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X p ^ i * X a ^ (q.natDegree - i)

theorem homog_mem (y : (Σ k, ι k) → ℂ) (k : K) (i i₀ : ι k) (ha : y ⟨k, i₀⟩ = 1) (q : Polynomial ℤ)
    (hq : q.eval₂ (Int.castRingHom ℂ) (y ⟨k, i⟩) = 0) :
    homog q ⟨k, i⟩ ⟨k, i₀⟩ ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  have hterm : ∀ n ∈ Finset.range (q.natDegree + 1),
      mConeMap y (C (q.coeff n) * X ⟨k, i⟩ ^ n * X ⟨k, i₀⟩ ^ (q.natDegree - n)) =
        MvPolynomial.C ((q.coeff n : ℂ) * y ⟨k, i⟩ ^ n) * MvPolynomial.X k ^ q.natDegree := by
    intro n hn
    have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
    simp only [mConeMap, map_mul, map_pow, map_intCast, aeval_X, ha, map_one, one_mul]
    conv_rhs => rw [← pow_mul_pow_sub (MvPolynomial.X k) hle]
    rw [aeval_C, eq_intCast (algebraMap ℤ (MvPolynomial K ℂ))]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homog, map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  have : ∑ n ∈ Finset.range (q.natDegree + 1), (q.coeff n : ℂ) * y ⟨k, i⟩ ^ n = 0 := by
    rw [← hq, Polynomial.eval₂_eq_sum_range]; rfl
  rw [this, map_zero, zero_mul]

theorem homog_eval (z : (Σ k, ι k) → ℂ) (p a : Σ k, ι k) (hza : z a ≠ 0) (q : Polynomial ℤ) :
    eval z (map (Int.castRingHom ℂ) (homog q p a)) =
      z a ^ q.natDegree * q.eval₂ (Int.castRingHom ℂ) (z p / z a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum, homog, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
  simp only [map_mul, map_pow, map_intCast, map_X, eval_X, eq_intCast]
  conv_rhs => rw [← pow_mul_pow_sub (z a) hle, div_pow]
  field_simp

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (hx : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hx]⟩

theorem rootCoord_isIntegral {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine IsIntegral.det fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hx⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hx

end RootPointsFiniteAlt


open RootPointsFiniteAlt in
theorem RootPointsFinite.proof (h : RootAnchorNonzero.Statement) : RootPointsFinite.Statement := by
  intro f j m ζ hζ
  have hint : ∀ p, ∃ q : Polynomial ℤ, q.Monic ∧ q.eval₂ (Int.castRingHom ℂ) (rootCoord ζ p) = 0 := by
    intro p
    obtain ⟨q, hqm, hq⟩ := rootCoord_isIntegral ζ hζ p
    exact ⟨q, hqm, by rwa [← RingHom.ext_int (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]⟩
  choose q hqm hq using hint
  let S : Set ((Σ _ : Fin f, PlIdx j m) → ℂ) :=
    Set.pi Set.univ fun p => {u | Polynomial.IsRoot ((q p).map (Int.castRingHom ℂ)) u}
  have hS : S.Finite := Set.Finite.pi fun p =>
    Polynomial.finite_setOfPred_isRoot ((hqm p).map _).ne_zero
  have hmem : ∀ z ∈ mcPts (rootPointIdeal ζ),
      (fun p : Σ _ : Fin f, PlIdx j m => z p / z ⟨p.1, plAnchor j m⟩) ∈ S := by
    intro z hz p _
    have hza := h f j m ζ hζ z hz p.1
    have h0 := hz.2 _ (homog_mem (rootCoord ζ) p.1 p.2 (plAnchor j m)
      (by simp [rootCoord, anchor_minor]) (q p) (hq p))
    rw [homog_eval z _ _ hza] at h0
    simpa [Polynomial.IsRoot, Polynomial.eval_map, hza] using h0
  let F : McClasses (rootPointIdeal ζ) → S := Quot.lift
    (fun z => ⟨fun p => z.1 p / z.1 ⟨p.1, plAnchor j m⟩, hmem z.1 z.2⟩) (by
      rintro z z' ⟨c, hc, hz'⟩
      apply Subtype.ext
      funext p
      simp only [hz']
      exact (mul_div_mul_left _ _ (hc p.1)).symm)
  have := hS.to_subtype
  refine Finite.of_injective F ?_
  intro x x'
  induction x using Quot.ind with | mk z => ?_
  induction x' using Quot.ind with | mk z' => ?_
  intro hF
  have hfun := fun p => congrFun (congrArg Subtype.val hF) p
  apply Quot.sound
  refine ⟨fun τ => z'.1 ⟨τ, plAnchor j m⟩ / z.1 ⟨τ, plAnchor j m⟩,
    fun τ => div_ne_zero (h f j m ζ hζ z'.1 z'.2 τ) (h f j m ζ hζ z.1 z.2 τ), ?_⟩
  funext p
  have hza := h f j m ζ hζ z.1 z.2 p.1
  have hza' := h f j m ζ hζ z'.1 z'.2 p.1
  have e : z.1 p / z.1 ⟨p.1, plAnchor j m⟩ = z'.1 p / z'.1 ⟨p.1, plAnchor j m⟩ := hfun p
  rw [div_eq_div_iff hza hza'] at e
  rw [div_mul_eq_mul_div, eq_div_iff hza]
  linear_combination -e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

abbrev ProjIdx (K : Type) [Field K] [NumberField K] (i : ℕ) : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin i

abbrev projBlocks (K : Type) [Field K] [NumberField K] (i : ℕ) : Unit → Type := fun _ => ProjIdx K i

abbrev ProjField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin i) K)


open scoped Classical in
def embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (z : ProjIdx K i → ℂ) :
    Fin i → ℂ :=
  by
    classical
    exact fun j => ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single σ 1) m * z (m, j)

def latticeNormSq {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i)
    (z : ProjIdx K i → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (embComp σ z) ⬝ᵥ (F.metric σ *ᵥ embComp σ z)).re

theorem latticeNormSq_term_nonneg {K : Type} [Field K] [NumberField K] {i : ℕ}
    (F : HermLattice K i) (σ : K →+* ℂ) (w : Fin i → ℂ) :
    0 ≤ (star w ⬝ᵥ (F.metric σ *ᵥ w)).re := by
  by_cases hw : w = 0
  · simp [hw]
  · exact ((Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hw)).1).le

theorem embComp_smul {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (c : ℂ)
    (z : ProjIdx K i → ℂ) : embComp σ (c • z) = c • embComp σ z := by
  funext j
  simp only [embComp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring


open scoped Classical in
theorem sum_emb_embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (z : ProjIdx K i → ℂ)
    (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin i) :
    ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j = z (m, j) := by
  classical
  set b := canonicalEmbedding.latticeBasis K
  have hb : b m = ∑ σ : K →+* ℂ, σ (integralBasis K m) • (Pi.single σ 1 : (K →+* ℂ) → ℂ) := by
    funext τ
    simp [b, canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, Pi.single_apply]
  have hr : ∀ m' , (if m = m' then (1 : ℂ) else 0) =
      ∑ σ : K →+* ℂ, σ (integralBasis K m) * b.repr (Pi.single σ 1) m' := by
    intro m'
    have := congrArg (fun v => b.repr v m') hb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    rw [← this, Finsupp.single_apply]
  have hs : ∀ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) =
      (if m = m' then (1 : ℂ) else 0) * z (m', j) := by
    intro m'
    rw [hr m', Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j
      = ∑ σ : K →+* ℂ, ∑ m', σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) :=
        Finset.sum_comm
    _ = ∑ m', (if m = m' then (1 : ℂ) else 0) * z (m', j) := Finset.sum_congr rfl fun m' _ => hs m'
    _ = z (m, j) := by simp

def latticeLine {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLine (projBlocks K i) where
  a := fun _ => 1
  h z := Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩)
  pos z hz := by
    apply Real.sqrt_pos.mpr
    obtain ⟨⟨m, j⟩, hmj⟩ := hz ()
    have hσ : ∃ σ : K →+* ℂ, embComp σ (fun q => z ⟨(), q⟩) ≠ 0 := by
      by_contra h
      push Not at h
      apply hmj
      rw [← sum_emb_embComp (fun q => z ⟨(), q⟩) m j]
      simp [h]
    obtain ⟨σ, hσ⟩ := hσ
    have hpos : 0 < (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re :=
      (Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hσ)).1
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun σ =>
      (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re)
      (fun σ _ => latticeNormSq_term_nonneg F σ _) (Finset.mem_univ σ))
  smul c z hc := by
    have hz : (fun q => (fun p : Σ _ : Unit, ProjIdx K i => c p.1 * z p) ⟨(), q⟩) =
        c () • fun q => z ⟨(), q⟩ := by
      funext q; rfl
    simp only [hz, latticeNormSq, embComp_smul, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    have : ∀ σ : K →+* ℂ, (star (c () • embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ (c () • embComp σ fun q => z ⟨(), q⟩))).re =
        ‖c ()‖ ^ 2 * (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
          (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re := by
      intro σ
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
        Complex.normSq_eq_norm_sq]
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

def LineOfLargeDegreeFromZ.Statement : Prop :=
  SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → LineOfLargeDegree.Statement

end

end GroundTheory.Heights₂.Heights
end

