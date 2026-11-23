module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordsOfMemAdjoin
section
namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set F) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    refine ⟨0, 1, ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    simp
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a + a', b + b', ?_⟩
    simp only [map_add (f := _)]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add (f := _), map_mul, ← hs]
    ring

theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfPowEqSelf
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDict


open Polynomial in
theorem exists_eq_of_pow_eq_self {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Field L] (j : Ω →+* L) {N : ℕ}
    (hN : 2 ≤ N) {ζ : L} (hζ : ζ ^ N = ζ) : ∃ z, j z = ζ := by
  have hmon : (X ^ N - X : Polynomial Ω).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hb : ζ ∈ ((X ^ N - X : Polynomial Ω).map j).roots := by
    rw [mem_roots (hmon.map j).ne_zero]
    simp [hζ]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem isFrob_iff_of_lifts (h : IsPlaceOver A w) {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ : G E Ω}
    (hσ : σ ∈ Dec (F := E) A) (H : Lifts ι g σ) :
    IsFrob (F := E) A (normV w) σ ↔
      ∀ (ζ : Kbar w) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → g ζ = ζ ^ normV w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rw [GlobalTheory.FrobTeich.isFrob_iff_teichmuller E Ω A w h σ]
  constructor
  · rintro ⟨-, hT⟩ ζ m hm hζ
    obtain ⟨z, rfl⟩ := exists_eq_of_pow_eq_self (ι : Ω →+* Kbar w)
      (Nat.one_lt_pow hm.ne' (one_lt_normV w)) hζ
    have hz : z ^ normV w ^ m = z := (ι : Ω →+* Kbar w).injective (by rw [map_pow]; exact hζ)
    change g (ι z) = ι z ^ normV w
    rw [H z, hT z m hm hz, map_pow]
  · intro hT
    refine ⟨hσ, fun z m hm hz => (ι : Ω →+* Kbar w).injective ?_⟩
    change ι (σ z) = ι (z ^ normV w)
    rw [← H z, map_pow]
    exact hT _ m hm (by rw [← map_pow, hz])

end GlobalTheory.WeilDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinity
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.GLInfReduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def entries (y : Matrix (Fin a) (Fin a) (Cinf E)) : GlobalTheory.FlagMeas.MatInf E a := fun w i k => y i k w

def dn (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∏ w, ‖(y.det) w‖ ^ 2

theorem detNorm_entries (y : Matrix (Fin a) (Fin a) (Cinf E)) :
    GlobalTheory.FlagMeas.detNorm E a (entries y) = dn y := by
  unfold GlobalTheory.FlagMeas.detNorm dn
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of (entries y w) = (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix y := by
    ext i k; rfl
  rw [this, ← RingHom.map_det]; rfl

theorem entries_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : entries (g * y) = entries g * entries y := by
  funext w i k
  change (g * y) i k w = (Matrix.of (entries g w) * Matrix.of (entries y w)) i k
  simp [Matrix.mul_apply, Finset.sum_apply, entries]

theorem dn_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : dn (g * y) = dn g * dn y := by
  simp [dn, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]

theorem dn_pos (y : GL (Fin a) (Cinf E)) : 0 < dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := by
  refine Finset.prod_pos fun w _ => ?_
  have h : (y : Matrix (Fin a) (Fin a) (Cinf E)).det * ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h' := congrFun h w
  have hne : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 := left_ne_zero_of_mul_eq_one h'
  positivity

end GlobalTheory.GLInfReduction


open GlobalTheory.GLInfReduction in
theorem GlobalTheory.GLInfReduction.exists_cover_of_finite_measure (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)) (hΛ : Submodule.IsFullLattice E Λ)
    [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure] :
    ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E,
      (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧
      ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨Set.univ, ?_, fun y => ⟨1, by simp, 0, trivial⟩⟩
    haveI : Subsingleton (GL (Fin 0) (Cinf E)) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Finite (GL (Fin 0) (Cinf E)) := Finite.of_subsingleton
    exact isCompact_univ.measure_lt_top
  set r := Fintype.card (InfinitePlace E) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set N : ℕ := 2 * a * r with hN_def
  have hN : 0 < N := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'

  have hslab := GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top E inferInstance a ha Λ (by
    letI := hΛ
    infer_instance)
  simp only [GlobalTheory.FlagMeas.covol, iInf_lt_iff] at hslab
  obtain ⟨D, hDm, hcov, hDlt⟩ := hslab
  have hD' := _root_.GlobalTheory.haarGL_finite_pullback E a ν D hDm hDlt
  set S : Set (GL (Fin a) (Cinf E)) := {y | entries (y : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D} with hS
  have hS' : ν S < ⊤ := hD'

  let c : ℝ → GL (Fin a) (Cinf E) := fun t => GeneralLinearGroup.map (pInf E) (splitCentre E a t)
  have hc_val : ∀ t : ℝ, (c t : Matrix (Fin a) (Fin a) (Cinf E)) =
      Matrix.scalar (Fin a) (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := by
    intro t
    simp only [c, splitCentre, pInf_infGL]
    rfl
  have hc_dn : ∀ t : ℝ, dn (c t : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (N * t) := by
    intro t
    rw [hc_val, dn]
    simp only [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Pi.pow_apply, norm_pow, Complex.norm_exp_ofReal]
    rw [← hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hN_def]
    congr 1; push_cast; ring
  have hcomm : ∀ t g, c t * g = g * c t := by
    intro t g
    have := congrArg (GeneralLinearGroup.map (pInf E)) (splitCentre_comm (E := E) (a := a) t (infGL E a g))
    simpa [map_mul] using this
  have hcint : ∀ n : ℤ, GeneralLinearGroup.map (pInf E) (splitCentre E a 1 ^ n) = c n := by
    intro n; simp only [c, splitCentre_intCast]
  refine ⟨⋃ k ∈ Finset.range N, (fun h => c (-(k : ℝ) / N) * h) ⁻¹' S, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    rw [measure_preimage_mul]
    exact hS'
  · intro y
    set L := Real.log (dn (y : Matrix (Fin a) (Fin a) (Cinf E)))
    have hL : Real.exp L = dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := Real.exp_log (dn_pos y)
    set m := ⌊L⌋
    set q := m / (N : ℤ)
    set ρ := m % (N : ℤ)
    have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hρN : ρ < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    have hm : ρ + N * q = m := by simp only [ρ, q]; rw [Int.emod_def]; ring
    set k := ρ.toNat
    have hk : (k : ℤ) = ρ := Int.toNat_of_nonneg hρ0
    have hkN : k < N := by omega
    set x := c (-(k : ℝ) / N) * (c ((-q : ℤ) : ℝ) * y)
    have hx : dn (x : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (L - m) := by
      simp only [x, Units.val_mul, dn_mul, hc_dn, ← hL, ← Real.exp_add]
      congr 1
      have hmR : (ρ : ℝ) + N * q = m := by exact_mod_cast hm
      have hkR : (k : ℝ) = ρ := by exact_mod_cast hk
      rw [← hmR, hkR]; push_cast; field_simp; ring
    have hxS : 1 ≤ GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
        GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) < Real.exp 1 := by
      rw [detNorm_entries, hx]
      constructor
      · exact Real.one_le_exp (by linarith [Int.floor_le L])
      · exact Real.exp_lt_exp.2 (by linarith [Int.lt_floor_add_one L])
    obtain ⟨g, ⟨γ, hγΛ, hgγ⟩, hgD⟩ := hcov _ hxS
    refine ⟨γ, hγΛ, -q, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, hkN, ?_⟩
    set R := GeneralLinearGroup.map (pInf E) (ratGL E a γ)
    have hR : entries (R : Matrix (Fin a) (Fin a) (Cinf E)) = g := by
      funext w i j
      rw [hgγ w i j]
      exact pInf_algebraMap (γ i j) w
    have e1 : c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) = R * x := by
      rw [map_mul, hcint, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc, mul_assoc]
    change entries ((c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) :
      GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D
    rw [e1, Units.val_mul, entries_mul, hR]
    exact hgD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfPlacesTypePrime
section
noncomputable section

namespace GlobalTheory.MemN.HalfPlaces

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.Mem.GaloisStage
open scoped Pointwise

theorem exists_transversal_cover {S : Type} [Fintype S] (c : S → S) (hc : ∀ x, c (c x) = x)
    (hne : ∀ x, c x ≠ x) {n : ℕ} (hn : Fintype.card S = 2 * n) :
    ∃ e : Fin n → S, Function.Injective e ∧ (∀ i j, c (e i) ≠ e j) ∧ ∀ x, ∃ i, x = e i ∨ x = c (e i) := by
  classical
  obtain ⟨e, he, he'⟩ := exists_transversal c hc hne hn
  refine ⟨e, he, he', fun x => ?_⟩
  have hinj : Function.Injective (Sum.elim e (fun i => c (e i)) : Fin n ⊕ Fin n → S) := by
    rintro (i | i) (j | j) h
    · exact congrArg _ (he h)
    · exact absurd h.symm (he' j i)
    · exact absurd h (he' i j)
    · have h' : c (e i) = c (e j) := h
      have : e i = e j := by rw [← hc (e i), h', hc]
      exact congrArg _ (he this)
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [hn, two_mul]⟩
  obtain ⟨i | i, h⟩ := hbij.2 x
  · exact ⟨i, Or.inl h.symm⟩
  · exact ⟨i, Or.inr h.symm⟩

variable {R : Ranks}

theorem isConjPl_iff (H : Host R) (w w' : PlE H) :
    IsConjPl H w w' ↔ H.conj • w.asIdeal = w'.asIdeal := by
  constructor
  · intro h
    ext y
    have := h (H.conj⁻¹ • y) y (by rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, smul_inv_smul])
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact this
  · intro h x y hxy
    have hy : y = H.conj • x := by
      apply Subtype.ext
      exact hxy
    rw [← h, hy, Ideal.smul_mem_pointwise_smul_iff]

theorem exists_places_cover (H : Host R) {p : ℕ} (hp : p.Prime)
    (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    ∃ e : Fin R.f → PlE H, (∀ i, e i ∈ placesOver H.E p) ∧ Function.Injective e ∧
      (∀ i j, ¬ IsConjPl H (e i) (e j)) ∧ ∀ w ∈ placesOver H.E p, ∃ v, w = e v ∨ IsConjPl H (e v) w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hG : IsGalois ℚ H.E := H.galois
  have := Formalism.FrobeniusOrbits.SplitK.span_prime p
  have : IsGaloisGroup (H.E ≃ₐ[ℚ] H.E) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
  have hr : Set.range (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) := by
    rw [GlobalTheory.HostSplit.ncard_placesOver H.E hp, ← hr, ← IsGalois.card_aut_eq_finrank, ← Set.image_univ,
      ← Set.ncard_univ] at hs
    exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq hs)
  have hcard : Fintype.card (H.E ≃ₐ[ℚ] H.E) = 2 * R.f := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      H.finrank_cmField, Ranks.f, Ranks.n]
    ring
  obtain ⟨e, he, he', hcov⟩ := exists_transversal_cover (fun σ => H.conj * σ)
    (fun σ => by rw [← mul_assoc, conj_mul_conj, one_mul])
    (fun σ h => conj_ne_one H (mul_eq_right.1 h)) hcard
  refine ⟨fun i => ⟨e i • P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 _⟩, fun i => ?_,
    fun i j h => he (hinj (congrArg HeightOneSpectrum.asIdeal h)), fun i j h => he' i j (hinj ?_),
    fun w hw => ?_⟩
  · have h3 : (p : ℤ) ∈ (e i • P).under ℤ := by
      rw [← Ideal.over_def (e i • P) (Ideal.span {(p : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    have h4 : algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ e i • P := h3
    rw [map_natCast] at h4
    exact h4
  · show (H.conj * e i) • P = e j • P
    rw [mul_smul]
    have h' := (isConjPl_iff H _ _).1 h
    dsimp only at h'
    exact h'
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    have hwp := w.isPrime
    have hw' : w.asIdeal ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
      refine ⟨hwp, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
      rw [Ideal.span_singleton_le_iff_mem]
      show algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    rw [← hr] at hw'
    obtain ⟨σ, hσ⟩ := hw'
    have hσ' : σ • P = w.asIdeal := hσ
    obtain ⟨i, h | h⟩ := hcov σ
    · exact ⟨i, Or.inl (HeightOneSpectrum.ext (by rw [← hσ', h]))⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [isConjPl_iff]
      dsimp only
      rw [← hσ', h, mul_smul]

end GlobalTheory.MemN.HalfPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LevFinCong

variable {D : D7}

theorem finE_mem_UA (V : HSp D) (κ : GA D V) : finE V κ ∈ UA D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have := (GlobalTheory.Mass.swapPts (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen ((((Kg D.sp.cm V.gram β T).comap
      ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)) : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous ((Bridge.Gf V).subtype) := continuous_subtype_val
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β T hc (map_one _)] with x hh
  obtain ⟨h2, h3⟩ := hh
  obtain ⟨g, hg⟩ := x.2
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ UA D.sp.cm V.gram := by
    rw [← hg]; exact finE_mem_UA V g
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem exists_finCong_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  classical
  intro D V β L
  obtain ⟨N, hN, hK⟩ := GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (isOpen_comap_Kg V β (L.Pg ∪ L.Q))
  refine ⟨N, hN, fun k hf hk => ?_⟩
  have hk' : finE V k ∈ Kg D.sp.cm V.gram β (L.Pg ∪ L.Q) := hK k hk
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk'
  · unfold levChi
    rw [GlobalTheory.GoodFiniteDim.levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk', Units.val_one]

end GlobalTheory.LevFinCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlockStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type) (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω), A₀ ∈ S.S (genericPoint M.Z) → ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  first | exact @GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | exact GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | (intros; apply GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
section
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem shaOK_shaTrue (B : Pre) : ShaOK B (GaloisStage.shaTrue B.host) := by
  refine ⟨fun p _ => GaloisStage.lData B.host p, ?_⟩
  intro p hp e _ _ n h
  rw [GaloisStage.shaTrue, dite_eq_left hp.out]
  show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n
  rw [h, ENat.toNat_natCast]

end GlobalTheory.MemN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory

theorem FlagBundle.bears_self : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  intro F _ ι _ m X Y Eb S φ f hR K _ w
  obtain ⟨A, hA⟩ := Eb.nonempty ((w ≫ f) (IsLocalRing.closedPoint K))
  obtain ⟨A', hA'⟩ := S.nonempty (w (IsLocalRing.closedPoint K))
  have hA₁ : A ∈ Eb.S (f (w (IsLocalRing.closedPoint K))) := (Scheme.Hom.comp_apply w f (IsLocalRing.closedPoint K)) ▸ hA
  have hN := hR.2.1 _ A' hA' A hA₁
  have hh : Par 0 ⊤ ((A' * (A.map φ)⁻¹).map ((ratOf Y).val w)) := by
    have hz := RatModel.range_eq_singleton (M := ratOf Y) w (IsLocalRing.closedPoint K)
    exact hN.map_of ((ratOf Y).val w) (RatModel.valHom (M := ratOf Y) w _ hz)
      (fun x => (RatModel.valHom_apply (M := ratOf Y) w _ hz x).symm)
  refine ⟨A, hA, _, hh, A', hA', ?_⟩
  rw [Mat.mul_inv hh.det_ne]
  exact Par.one
end GlobalTheory
end

