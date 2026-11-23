module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsOrbitalTermEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.Move

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem aeval_conj (y : G.Cˣ) (x : G.C) (A : Polynomial G.F) :
    Polynomial.aeval ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) A =
      (y : G.C) * Polynomial.aeval x A * ((y⁻¹ : G.Cˣ) : G.C) := by
  have hp : ∀ k : ℕ, ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) ^ k =
      (y : G.C) * x ^ k * ((y⁻¹ : G.Cˣ) : G.C) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  induction A using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg, mul_add, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hp n, ← mul_assoc, ← mul_assoc,
      Algebra.commutes a (y : G.C)]
    simp only [mul_assoc]

theorem move (y : G.Cˣ) (s : ℚ) (g b b' : G.C) (A : Polynomial G.F)
    (hb : b' = algebraMap ℚ G.C s * (y * b * sh G y)) :
    Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) A * b' =
      algebraMap ℚ G.C s * (y * (Polynomial.aeval g A * b) * sh G y) := by
  rw [aeval_conj, hb, ← mul_assoc, ← Algebra.commutes s]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem cancel {R : Type*} [Ring R] (X w : R) (b u : Rˣ) (hu : X * b = u) (h : X * b = X * w) :
    (b : R) = w := by
  have hX : X = (u : R) * ((b⁻¹ : Rˣ) : R) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hl : (b : R) * ((u⁻¹ : Rˣ) : R) * X = 1 := by
    rw [hX, mul_assoc, ← mul_assoc ((u⁻¹ : Rˣ) : R), Units.inv_mul, one_mul, Units.mul_inv]
  calc (b : R) = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * b := by rw [hl, one_mul]
    _ = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * w := by rw [mul_assoc _ X, h, ← mul_assoc]
    _ = w := by rw [hl, one_mul]

private theorem minpoly_monic_of_irreducible (x : G.C)
    (hi : Irreducible (minpoly G.F x)) : (minpoly G.F x).Monic := by
  have hint : IsIntegral G.F x := by
    by_contra h
    exact hi.ne_zero (minpoly.eq_zero h)
  exact minpoly.monic hint

private theorem aeval_eq_zero_of_aeval_conj_eq_zero (y : G.Cˣ) (g : G.C)
    (q : Polynomial G.F) (h : Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) q = 0) :
    Polynomial.aeval g q = 0 := by
  rw [aeval_conj] at h
  calc Polynomial.aeval g q
      = ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * Polynomial.aeval g q * ((y⁻¹ : G.Cˣ) : G.C)) * (y : G.C) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    _ = 0 := by rw [h, mul_zero, zero_mul]

private theorem minpoly_conj_eq_of_irreducible (y : G.Cˣ) (g : G.C)
    (hi : Irreducible (minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)))) :
    minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F g :=
  minpoly.eq_of_irreducible_of_monic hi (aeval_eq_zero_of_aeval_conj_eq_zero y g _ (minpoly.aeval _ _))
    (minpoly_monic_of_irreducible _ hi)

end GlobalTheory.LKDef.Move

namespace GlobalTheory.LKDef

open GlobalTheory.LKDef.Move

theorem cls_equiv_dcls_irr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  intro p hp G ha hn sel hsel
  obtain ⟨v0, hv0⟩ : ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 := by
    have h1 : 0 < G.a := by rw [ha]; exact Nat.one_pos
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp h1
    exact ⟨x.1, x.2⟩
  have key := fun (P0 : Polynomial G.F) (hi : Irreducible P0) (hm : P0.Monic)
      (hd : P0.natDegree = G.n) =>
    GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked p G ha hn P0 (sel P0) v0 hv0 hi (hsel v0 hv0 P0 hm hd)
  choose! A hA1 hA2 using key
  have hF := fun (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)) =>
    hA2 P.pol hi (minpoly_monic_of_irreducible (P.γ : G.C) hi) P.reg.1 P rfl hm
  choose FQ hFγ hFc hFβ hFu using hF
  have hB := fun (Q : DPair G) (hi : Irreducible Q.pol) =>
    hA1 Q.pol hi (minpoly_monic_of_irreducible (Q.γ : G.C) hi) Q.reg.1 Q rfl
  choose BP hBγ hBc hBβ hBm hBu using hB

  have hpolP : ∀ P P' : Pair G, P'.Rel P → Irreducible P.pol → P'.pol = P.pol := by
    intro P P' hr hi
    obtain ⟨y, s, -, -, hγ⟩ := hr
    have e : (P.γ : G.C) = (y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C) := by
      rw [hγ, Units.val_mul, Units.val_mul]
    have hi' : Irreducible (minpoly G.F ((y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C))) := by
      rw [← e]; exact hi
    show minpoly G.F (P'.γ : G.C) = minpoly G.F (P.γ : G.C)
    rw [e]
    exact (minpoly_conj_eq_of_irreducible y _ hi').symm
  have hFirr : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      Irreducible (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol := by
    intro P hi hm
    rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
    show Irreducible (minpoly G.F ((FQ P hi hm).γ : G.C))
    rw [hFγ P hi hm]
    exact hi
  have hBok : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      Irreducible (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol ∧
      (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).Mark
        (sel (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol) := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    rw [hpolP _ _ hr hPi, Pair.mark_iff_of_rel p G _ _ _ hr, hPpol]
    exact ⟨hi, hBm Q hi⟩

  have hleft : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      P.Rel (BP _ (hFirr P hi hm)) := by
    intro P hi hm
    obtain ⟨y, s, hs, hβ, hγ⟩ := DPair.rel_out (FQ P hi hm)
    have hpol : (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol := by
      rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    refine ⟨y, s, hs, ?_, ?_⟩
    · rw [hBβ _ (hFirr P hi hm), hpol, hγ, Units.val_mul, Units.val_mul,
        GlobalTheory.LKDef.Move.move y s ((FQ P hi hm).γ : G.C) _ _ (A P.pol) hβ, hFγ P hi hm, ← hFβ P hi hm]
    · rw [hBγ _ (hFirr P hi hm), hγ, hFγ P hi hm]

  have hright : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      (FQ _ (hBok Q hi).1 (hBok Q hi).2).Rel Q := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    have hP'pol : (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = Q.pol := by
      rw [hpolP _ _ hr hPi, hPpol]
    have hA' : A (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = A Q.pol := by
      rw [hP'pol]
    obtain ⟨y, s, hs, hβ, hγ⟩ := id hr
    have hc : (y : G.C) * (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).γ *
        ((y⁻¹ : G.Cˣ) : G.C) = Q.γ := by
      rw [← hBγ Q hi, hγ, Units.val_mul, Units.val_mul]
    refine ⟨y, s, hs, ?_, ?_⟩
    · refine GlobalTheory.LKDef.Move.cancel (Polynomial.aeval (Q.γ : G.C) (A Q.pol)) _ Q.β (BP Q hi).β
        (hBβ Q hi).symm ?_
      rw [← hBβ Q hi, hβ, hFβ _ (hBok Q hi).1 (hBok Q hi).2,
        ← GlobalTheory.LKDef.Move.move y s _ _ _ _ rfl, hc, hA']
    · rw [hFγ _ (hBok Q hi).1 (hBok Q hi).2, ← hBγ Q hi, hγ]

  have hterm : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol ∧
      ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
        (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
        (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).term Kf f r K φ =
          P.term Kf f r K φ := by
    intro P hi hm
    have h9 := _root_.GlobalTheory.LKDef.DPair.rel_pol_c_term p G (FQ P hi hm) _ (DPair.rel_out (FQ P hi hm))
    refine ⟨?_, fun Kf f r K φ hr hf hφ => ?_⟩
    · rw [← h9.1]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    · rw [← h9.2.2 Kf f r K φ hr hf hφ]
      exact (_root_.GlobalTheory.LKDefTerm.term_eq_of_local_isom p G P (FQ P hi hm) (hFγ P hi hm).symm (hFc P hi hm).symm (hFu P hi hm)
        Kf f r K φ hr hf hφ).symm
  refine ⟨⟨fun q => ⟨(Quot.mk (DPair.Rel (G := G)) (FQ _ q.2.1 q.2.2) : DCls G), hFirr _ q.2.1 q.2.2⟩,
    fun q => ⟨(Quot.mk (Pair.Rel (G := G)) (BP _ q.2) : Cls G), hBok _ q.2⟩, fun q => ?_, fun q => ?_⟩,
    fun q => hterm _ q.2.1 q.2.2⟩
  · apply Subtype.ext
    exact ((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1.mpr (hleft _ q.2.1 q.2.2)).symm.trans
      (Quot.out_eq q.1)
  · apply Subtype.ext
    exact ((DPair.mk_eq_iff _ _).mpr (hright _ q.2)).trans (Quot.out_eq q.1)
end GlobalTheory.LKDef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FixedBound

theorem exists_entry_absFin_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))),
    ?_, fun v => le_max_left _ _, fun v => le_max_right _ _⟩
  have h := Filter.eventually_all.2 fun p : Fin n × Fin d => GlobalTheory.AdelicU.eventually_absFin_le_one F (Y p.1 p.2)
  refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun p _ => hv' p)

end GlobalTheory.FixedBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist
section
noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.SqIntMaxCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLinearSystemConeAlgebraIffCoeff
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.DegCmp

theorem X_pow_mul_C_mem_coneAlg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (d : ℕ) (t : Ω) (ht : t ∈ ((LinearMap.range ev) ^ d : Submodule K Ω)) :
    (Polynomial.X ^ d * Polynomial.C t : Polynomial Ω) ∈ coneAlg ev := by
  induction ht using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, one_mul]
    exact (coneAlg ev).algebraMap_mem r
  | add x y i _ _ hx hy =>
    rw [map_add (f := _), mul_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    have h : (Polynomial.X * Polynomial.C (ev v) : Polynomial Ω) ∈ coneAlg ev := Algebra.subset_adjoin ⟨v, rfl⟩
    have e : (Polynomial.X ^ i.succ * Polynomial.C (ev v * x) : Polynomial Ω) =
        (Polynomial.X * Polynomial.C (ev v)) * (Polynomial.X ^ i * Polynomial.C x) := by
      rw [map_mul, pow_succ]; ring
    rw [e]
    exact mul_mem h hx

theorem mem_coneAlg_iff_coeff : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (p : Polynomial Ω), p ∈ coneAlg ev ↔ ∀ d : ℕ, p.coeff d ∈ ((LinearMap.range ev) ^ d : Submodule K Ω) := by
  intro K V Ω _ _ _ _ _ ev p
  constructor
  · intro hp
    unfold coneAlg at hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro d
      rcases d with _ | d
      · simp
      · simp only [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs with h
        · subst h
          simp
        · exact zero_mem _
    | algebraMap r =>
      intro d
      rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
      split_ifs with h
      · subst h
        rw [pow_zero]
        exact Submodule.algebraMap_mem r
      · exact zero_mem _
    | add x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_add]
      exact add_mem (hx d) (hy d)
    | mul x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_mul]
      refine Submodule.sum_mem _ fun c hc => ?_
      have hc' : c.1 + c.2 = d := by simpa using hc
      rw [← hc', pow_add]
      exact Submodule.mul_mem_mul (hx _) (hy _)
  · intro h
    rw [p.as_sum_support]
    refine Subalgebra.sum_mem _ fun d _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
    exact X_pow_mul_C_mem_coneAlg ev d _ (h d)

end GlobalTheory.DegCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
section
noncomputable section

open NumberField

namespace GlobalTheory.WeilUnitaryTransport

def ratPair (F : Type) [Field F] [NumberField F] (κ : Type) :
    AddSubgroup ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
  ((AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).prodMap
    (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ)).range

theorem mem_ratPair_iff {F : Type} [Field F] [NumberField F] {κ : Type}
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    w ∈ ratPair F κ ↔ ∃ y z : κ → F,
      w = (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) := by
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    exact ⟨(y, z), rfl⟩

end GlobalTheory.WeilUnitaryTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LawsFieldChange

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem goodOf_comp (σ' : c'.F →+* ℂ) :
    (goodOf c' σ').comp (incF c c' hle) = goodOf c (σ'.comp (incF c c' hle)) := by
  have h : GoodEmb c' σ' ↔ GoodEmb c (σ'.comp (incF c c' hle)) := Iff.rfl
  unfold goodOf
  by_cases hg : GoodEmb c' σ'
  · rw [if_pos hg, if_pos (h.1 hg)]
  · rw [if_neg hg, if_neg (fun h' => hg (h.2 h'))]
    rfl

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem modelWt_unfBC (σ' : c'.F →+* ℂ) (G : WTZ E) :
    modelWt (unfBC hle U σ') G = modelWt (U (σ'.comp (incF c c' hle))) G := by
  have hr : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  unfold modelWt
  rw [hr]
  rfl

theorem petAt_unfBC (σ' : c'.F →+* ℂ) (x : ℝ) {D : D7} (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (μ : Measure (AutQ V)) (G : WTZ E)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    petAt (unfBC hle U σ') x V dict μ G (rulBC hle f) = petAt (U (σ'.comp (incF c c' hle))) x V dict μ G f := by
  have hrd := (rulBC_cusp E H Dw l Xo c c' hle r U a n f hf).1 σ'
  unfold petAt
  rw [hrd, modelWt_unfBC hle U σ' G]
  rfl

end

theorem laws_fieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  intro D j H Dw l Xo c c' hle U dict hL
  refine ⟨?_, ?_⟩
  · exact
      { inR := hL.inR
        host := hL.host
        dat := hL.dat
        levA := hL.levA
        unf := fun σ' hσ' => GlobalTheory.OneMapAll.isUnf_unfExt hle σ' (fun _ => rfl) (hL.unf (σ'.comp (incF c c' hle)) hσ')
        chiTriv := fun σ' hσ' a n hd k γ hγ => by
          rw [laU_unfBC hle U σ' a n]
          exact hL.chiTriv (σ'.comp (incF c c' hle)) hσ' a n hd k γ hγ
        dictU := fun σ' hσ' => hL.dictU (σ'.comp (incF c c' hle)) hσ'
        modelW := fun σ' hσ' => hL.modelW (σ'.comp (incF c c' hle)) hσ' }
  · intro a n _ f
    have hf : (f : Rul Xo c) ∈ cusp Xo c U a n := (cuspW_wtZ (U := U) a n).le f.2
    have hsec : (f : Rul Xo c) ∈ sec Xo c a n := cusp_le_sec _ _ _ _ _ hf
    have hmem : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n) := by
      rw [cuspW_wtZ]
      exact (rulBC_cusp _ H Dw l Xo c c' hle D.R.r U a n _ hsec).2.2 hf
    refine ⟨hmem, fun σ' => ?_⟩
    have e1 : normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ'
        ⟨_, hmem⟩ = petAt (unfBC hle U (goodOf c' σ')) (xiR D) (D.sp.W j) (dict ((goodOf c' σ').comp (incF c c' hle)))
          (muQ1 (D.sp.W j)) (wtZ a n) (rulBC hle (f : Rul Xo c)) := rfl
    have e2 : normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ'.comp (incF c c' hle)) f =
        petAt (U (goodOf c (σ'.comp (incF c c' hle)))) (xiR D) (D.sp.W j) (dict (goodOf c (σ'.comp (incF c c' hle))))
          (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := rfl
    rw [e1, e2, petAt_unfBC hle U (goodOf c' σ') _ _ _ _ _ hsec]
    have key : ∀ τ τ' : c.F →+* ℂ, τ = τ' →
        petAt (U τ) (xiR D) (D.sp.W j) (dict τ) (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) =
        petAt (U τ') (xiR D) (D.sp.W j) (dict τ') (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := by
      rintro τ _ rfl; rfl
    exact key _ _ (goodOf_comp hle σ')

end GlobalTheory.LawsFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChartStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFactor_and_density_near_one_in_flagChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧ Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  first | exact @GlobalTheory.ChartNearOne.chart_near_one | exact GlobalTheory.ChartNearOne.chart_near_one | (intros; apply GlobalTheory.ChartNearOne.chart_near_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.PlacingProd

theorem multiProd_placing_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  intro k _ _ _ _ h n d e e' X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin n) (fun a => Fin (d a)) e e' _).1 _

end GlobalTheory.PlacingProd
end

