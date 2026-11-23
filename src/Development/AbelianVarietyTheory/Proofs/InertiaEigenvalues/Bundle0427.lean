module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangular
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EnvShape

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A]

theorem C_mem_supp (S : Set ℕ) (c : A) : MvPolynomial.C c ∈ MvPolynomial.supported A S := by
  rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ c


omit hl in
theorem cc_mem_ideal {R : Type} [CommRing R] (I : Ideal R) {x : R} (y : R) (hx : x ∈ I) : cc l x y ∈ I := by
  unfold cc
  exact Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx k (Finset.mem_Ioo.1 hk).1))


omit hl in
theorem cc_mem_sub {R : Type} [CommRing R] [Algebra A R] (S : Subalgebra A R) {x y : R} (hx : x ∈ S)
    (hy : y ∈ S) : cc l x y ∈ S := by
  unfold cc
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hx _)) (S.pow_mem hy _)

theorem phi_mem (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) {e : A} (he : e ∈ J) : D.φ e ∈ J := by
  rw [D.φ_eq]; exact J.add_mem (J.pow_mem_of_mem he _ hl.out.pos) (J.mul_mem_right _ hlJ)

theorem delta_Iio (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) (i : ℕ) (s : MvPolynomial ℕ A)
    (hs : s ∈ MvPolynomial.supported A (Set.Iio i)) :
    (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic i) ∧
    ∃ a ∈ MvPolynomial.supported A (Set.Iio i), ∃ b ∈ MvPolynomial.supported A (Set.Iio i),
      (polyDelta D).δ s - (a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  cases i with
  | zero =>
    have h0 : Set.Iio (0:ℕ) = ∅ := by ext; simp
    rw [h0, MvPolynomial.supported_empty, Algebra.mem_bot] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨C_mem_supp _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ c), C_mem_supp _ _, ?_⟩
    simp
  | succ i =>
    have h1 : Set.Iio (i+1) = Set.Iic i := by ext; simp [Nat.lt_succ_iff]
    rw [h1] at hs ⊢
    obtain ⟨h2, a, ha, b, hb, h3⟩ := _root_.GlobalTheory.BSP.polyDelta_supported_linear_mod l A D i s hs
    have hl' : (l : MvPolynomial ℕ A) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial ℕ A) hlJ
      rwa [map_natCast] at this
    exact ⟨h2, a, ha, b, hb, Ideal.span_le.2 (Set.singleton_subset_iff.2 hl') h3⟩

theorem step_eq (D : Delta l A) (e : A) (k : ℕ) (s : MvPolynomial ℕ A) :
    (polyDelta D).δ (MvPolynomial.C e * MvPolynomial.X k + s) =
      MvPolynomial.C (D.φ e) * MvPolynomial.X (k + 1) +
        (MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
          cc l (MvPolynomial.C e * MvPolynomial.X k) s) := by
  rw [(polyDelta D).δ_add, (polyDelta D).δ_mul, polyDelta_C, polyDelta_X, D.φ_eq]
  simp only [map_add (f := _), map_pow, map_mul, map_natCast]
  unfold cc; ring

theorem shape (D : Delta l A) (J : Ideal A) (d p : A) (hlJ : (l : A) ∈ J) (hd : d ∈ J)
    (hu : IsUnit (D.δ d)) (k : ℕ) :
    ∃ e ∈ J, IsUnit (D.δ e) ∧ ∃ s ∈ MvPolynomial.supported A (Set.Iio k),
      (polyDelta D).δ^[k] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) =
        MvPolynomial.C e * MvPolynomial.X k + s := by
  induction k with
  | zero => exact ⟨d, hd, hu, MvPolynomial.C p, C_mem_supp _ _, by simp [add_comm]⟩
  | succ k ih =>
    obtain ⟨e, he, heu, s, hs, hk⟩ := ih
    have hIic : Set.Iic k = Set.Iio (k+1) := by ext; simp [Nat.lt_succ_iff]
    have hX : MvPolynomial.X k ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      by rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨k, by simp, rfl⟩
    have hδ := (delta_Iio D J hlJ k s hs).1
    rw [hIic] at hδ
    have hs' : s ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      MvPolynomial.supported_mono (Set.Iio_subset_Iio (Nat.le_succ k)) hs
    refine ⟨D.φ e, phi_mem D J hlJ he, ?_, MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
      cc l (MvPolynomial.C e * MvPolynomial.X k) s, ?_, ?_⟩
    · rw [GlobalTheory.T.deltaRingStructure_delta_frobenius_comm]; exact heu.map D.φ
    · exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hX _)
        (C_mem_supp _ _)) hδ) (cc_mem_sub _ (Subalgebra.mul_mem _ (C_mem_supp _ _) hX) hs')
    · rw [Function.iterate_succ_apply', hk, step_eq]

theorem envRel_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A),
    a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧
    envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈
      J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  intro l _ A _ D J d p hlJ hd hu i
  obtain ⟨e, he, heu, s, hs, hi⟩ := shape D J d p hlJ hd hu i
  obtain ⟨-, a, ha, b, hb, hab⟩ := delta_Iio D J hlJ i s hs
  refine ⟨heu.unit, a, b, ha, hb, ?_⟩
  have hrel : envRel D d p i = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) +
      (MvPolynomial.X i ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s) := by
    rw [envRel, Function.iterate_succ_apply', hi, step_eq]
  have hdiff : envRel D d p i - (MvPolynomial.C (heu.unit : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) + ((polyDelta D).δ s - (a * MvPolynomial.X i + b)) -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s := by
    rw [hrel, IsUnit.unit_spec]; ring
  rw [hdiff]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (phi_mem D J hlJ he))) hab)
    (cc_mem_ideal _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)))

end GlobalTheory.EnvShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PrimesQD

open Formalism.FrobeniusOrbits Formalism.MainNotions.EmbeddingTypeJumps
open scoped Pointwise

theorem liesOver_span {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa [placesOver] using hv
  exact hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle

theorem ramIdx_eq_two (D : D7) {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E l) (g : D.R.GG) (hg : g ≠ 1)
    (hin : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔
      (D.host.galE σ = 1 ∨ D.host.galE σ = g)) :
    v.asIdeal.ramificationIdx ℤ = 2 := by
  have hgal := D.host.hostE_isGalois
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := liesOver_span hl hv
  have := v.isPrime
  have : Fact l.Prime := ⟨hl⟩
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hIn : Nat.card (v.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e1 : (v.asIdeal.inertia Gal(D.host.E/ℚ)) ≃ (({1, g} : Set (D.R.GG))) :=
      Equiv.subtypeEquiv (D.host.gal).toEquiv (fun σ => by
        rw [show σ ∈ v.asIdeal.inertia Gal(D.host.E/ℚ) ↔ σ ∈ ineG D v from Iff.rfl, hin σ]
        simp [Formalism.HC.HostRaw.galE])
    rw [Nat.card_congr e1, Nat.card_coe_set_eq, Set.ncard_pair hg.symm]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]

theorem bE_sq (D : D7) : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

theorem neg_mem_iff (D : D7) (φ : D.host.E →+* ℂ) :
    (-φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)) ↔
      ¬ φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  set z := φ (D.host.sqd)
  set s : ℂ := (Real.sqrt D.host.d : ℂ)
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hs : s ^ 2 = (D.host.d : ℂ) := by
    simp only [s, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hz : z ^ 2 = -(D.host.d : ℂ) := by
    simp only [z, ← map_pow, bE_sq, map_neg, map_natCast]
  have hs0 : Complex.I * s ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (by simpa [s] using hd0.ne')
  have hfac : (z - Complex.I * s) * (z + Complex.I * s) = 0 := by
    have : (z - Complex.I * s) * (z + Complex.I * s) = z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
    rw [this, hz, hs, Complex.I_sq]; ring
  constructor
  · intro h1 h2
    apply hs0
    have : (2 : ℂ) * (Complex.I * s) = 0 := by linear_combination -(h1 + h2)
    simpa using this
  · intro h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) h
    · linear_combination -h1

theorem ramification_two_and_conjugation_at_q_and_d : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  have hH := D.host.hyp
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  intro l hl
  have hl' : l = D.host.q ∨ l = D.host.d := by simpa using hl
  have hlp : l.Prime := by rcases hl' with rfl | rfl <;> assumption
  refine ⟨by rcases hl' with rfl | rfl <;> omega, ?_⟩
  intro v hv
  have hlo := liesOver_span hlp hv
  have := v.isPrime
  have hmemI : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔ ∀ x : 𝓞 D.host.E, σ • x - x ∈ v.asIdeal :=
    fun σ => AddSubgroup.mem_inertia
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rcases hl' with rfl | rfl
    · obtain ⟨g, hg, hin⟩ := UpperTheory.Small.inertia_q D.host
      exact ramIdx_eq_two D hlp v hv g hg fun σ => (hmemI σ).trans (hin v.asIdeal σ)
    · refine ramIdx_eq_two D hlp v hv D.R.iod (fun h => ?_)
        fun σ => (hmemI σ).trans (D.host.der.inertia_d v.asIdeal σ)
      have h' := congrArg (fun g : D.R.GG => g.1.2) h
      exact absurd (show (-1 : ℤˣ) = 1 from h') (by decide)
  ·
    intro h
    refine D.host.der.decompConj l hlp ?_ v.asIdeal (MulAction.mem_stabilizer_iff.mpr h)
    rcases hl' with rfl | rfl
    · exact (dvd_mul_left _ _).mul_right _
    · exact dvd_mul_left _ _
  ·
    rintro rfl σ hσ φ
    have hb : σ (D.host.sqd) = D.host.sqd :=
      (D.host.galE_mem_Psi_iff σ).1 (D.host.der.decomp_typeI _ hlp (dvd_mul_left _ _) v.asIdeal σ hσ)
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = D.host.sqd from hb]
  ·
    rintro rfl σ hσ hσ1 φ
    have h2 := (D.host.der.inertia_d v.asIdeal σ).1 ((hmemI σ).1 hσ)
    have hg : D.host.galE σ = D.R.iod := h2.resolve_left fun h => hσ1 ((D.host.galE_eq_one_iff σ).1 h)
    have hb : σ (D.host.sqd) = -D.host.sqd := by
      rw [D.host.galE_bE σ, hg, show D.R.iod.1.2 = -1 from rfl]
      simp
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = -D.host.sqd from hb,
      map_neg]
    exact neg_mem_iff D φ

end GlobalTheory.PrimesQD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBoundStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_selmer_determinant_order_bound : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s → EqDim bkP i s → ResBound bkP i s := by
  first | exact @GlobalTheory.ResOrder.resBound | exact GlobalTheory.ResOrder.resBound | (intros; apply GlobalTheory.ResOrder.resBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowPlacesSatisfyRowHypothesisAtQAndD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowBoundB

open Module

theorem jump_windows (η Sc b : ℝ) (t : ℕ) (hη : 0 < η) (hS : 0 < Sc) (ht : 1 ≤ (t : ℝ))
    (hpar : Sc + η + t + 2 ≤ b) (s : ℤ) (Jc Jl : Finset ℤ)
    (h1 : η + t + 1 < (s : ℝ)) (h2 : (s : ℝ) ≤ b + η + t + 1)
    (hl : ∀ a ∈ Jl, ((-η + ((t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ η + ((t : ℝ) - 1) / 2)))
    (hc : (∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + Sc) ≤ a ∧ a ≤ -s)) :
    ∃ (up : Bool) (bτ : ℕ), ⌊η⌋₊ + t < bτ ∧
      (∀ a : ℤ, (-a - 1 ∈ Jc ∨ -a - 1 ∈ Jl ∨ (0 ≤ -a - 1 ∧ -a - 1 < t)) →
        a ∈ ElementDenominator.deep up bτ ⌊Sc⌋₊ ∪ Set.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ) ∧
        a ∈ Set.Icc (-((⌊2 * b⌋₊ : ℕ) : ℤ)) ((⌊2 * b⌋₊ : ℕ) : ℤ)) ∧
      ∀ a ∈ Finset.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ), -a - 1 ∉ Jc := by
  have key : ∀ (x : ℝ) (n : ℤ), 0 ≤ x → (n : ℝ) ≤ x → n ≤ ((⌊x⌋₊ : ℕ) : ℤ) := by
    intro x n hx hn
    rw [Int.natCast_floor_eq_floor hx]
    exact Int.le_floor.2 hn
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hs1 : ((⌊η⌋₊ : ℕ) : ℤ) + t + 1 < s := by
    have : (((⌊η⌋₊ : ℕ) : ℤ) : ℝ) + ((t : ℤ) : ℝ) + 1 < (s : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hb : s + 1 + ((⌊Sc⌋₊ : ℕ) : ℤ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℤ) := by
    apply key _ _ (by linarith)
    push_cast; linarith
  have hlow : ∀ a : ℤ, -a - 1 ∈ Jl → -(((⌊η⌋₊ : ℕ) : ℤ) + t) ≤ a ∧ a ≤ ((⌊η⌋₊ : ℕ) : ℤ) + t := by
    intro a ha
    rcases hl _ ha with ⟨p, q⟩ | ⟨p, q⟩
    · have : a ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at p; linarith
      omega
    · have : -a - t ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at q ⊢; linarith
      omega
  rcases hc with hc | hc
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → s ≤ -a - 1 ∧ -a - 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨p, key _ _ hS.le ?_⟩
      push_cast at q ⊢; linarith
    refine ⟨false, (s + 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → -a - 1 ≤ -s ∧ a + 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨q, key _ _ hS.le ?_⟩
      push_cast at p ⊢; linarith
    refine ⟨true, (s - 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, if_true, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega

theorem sum_le_card (I Jl : Finset ℤ) (f : ℤ → ℤ) (h1 : ∀ a ∈ I, f a ≤ 1)
    (h0 : ∀ a ∈ I, -a - 1 ∉ Jl → f a = 0) : ∑ a ∈ I, f a ≤ Jl.card := by
  classical
  have e : ∑ a ∈ I, f a ≤ ∑ a ∈ I, (if -a - 1 ∈ Jl then (1 : ℤ) else 0) := by
    refine Finset.sum_le_sum fun a ha => ?_
    split_ifs with h
    · exact h1 a ha
    · exact (h0 a ha h).le
  refine e.trans ?_
  rw [Finset.sum_boole]
  have : (I.filter fun a => -a - 1 ∈ Jl).card ≤ Jl.card := by
    refine Finset.card_le_card_of_injOn (fun a => -a - 1) (fun a ha => (Finset.mem_filter.1 ha).2) ?_
    intro a _ b _ hab
    simp only at hab
    omega
  exact_mod_cast this

theorem boundA_le (CA η Sc b : ℝ) (l n r t m f : ℕ) (hl : 2 ≤ l) (hη : 0 < η) (hS : 0 < Sc) (hb : 1 ≤ b)
    (hf : f = n * 2) :
    ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ ≤
      max CA 0 * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (4 * b / (l : ℝ) + 2 * Sc + 2 * Real.logb (l : ℝ) (2 * b) + 1 + η + (t : ℝ)) + 3 * ((f : ℕ) : ℝ) * (m : ℝ) * (2 * b + 1)) := by
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have e3 : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have e4 : (1 : ℝ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℝ) := by
    have : 1 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have e5 : 0 ≤ Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) := Real.logb_nonneg hl' e4
  have e6 : Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ Real.logb (l : ℝ) (2 * b) :=
    Real.logb_le_logb_of_le hl' (by linarith) e3
  have e7 : 2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) ≤ 4 * b / (l : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hQ : ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ =
      CA * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) + 2 * ((⌊Sc⌋₊ : ℕ) : ℝ) +
        2 * Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) + 1 + ((⌊η⌋₊ : ℕ) : ℝ) + (t : ℝ)) +
        3 * ((f : ℕ) : ℝ) * (m : ℝ) * (((⌊2 * b⌋₊ : ℕ) : ℝ) + 1)) := by
    simp only [ElementDenominator.boundA, hf]
    push_cast
    ring
  rw [hQ]
  refine (mul_le_mul_of_nonneg_right (le_max_left CA 0) (by positivity)).trans ?_
  gcongr

theorem rowAt_of_thmA {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (CA : ℝ)
    (hT : ElementDenominator.thmA P K LL CA) (he : finrank ↥(K0 K) ↥K.1 = 2) {ι : Type} {k r : ℕ}
    (Ms : ι → ↥(GK K) → Matrix (Fin k) (Fin k) ↥LL.1) (M2 : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1)
    (S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (q : ℚ)
    (h1 : ∀ (V1 : Type) [AddCommGroup V1] [Module ↥LL.1 V1] [Module ℚ_[l] V1]
          [IsScalarTower ℚ_[l] ↥LL.1 V1] [FiniteDimensional ↥LL.1 V1]
          (ρ1 : Representation ↥LL.1 ↥(GK K) V1), IsSubOfSums ρ1 Ms → IsCrys (P.PD K) ρ1 ∧
          ∀ τ a, IsJumpV (P.PD K) ρ1 τ a →
            a ∈ ElementDenominator.deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η ∧ a ∈ Set.Icc (-(h : ℤ)) h)
    (h2 : IsCrys (P.PD K) (matRep M2)) (hb : ∀ τ, η < b τ)
    (hsum : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) (matRep M2) τ a ≤ m)
    (hq : ElementDenominator.boundA CA l (finrank ℚ_[l] ↥(K0 K)) 2 r S η m h ≤ q) :
    RowAt (P.PD K) (O := ↥(OL LL)) Ms ⇑M2 q := by
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hmat V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hsub F hFo
  obtain ⟨c1, c2⟩ := h1 V1 ρ1 hsub
  obtain ⟨e, heg, -⟩ := hmat
  have he' : ∀ g v, e (ρ2 g v) = matRep M2 g (e v) := by
    intro g v
    rw [heg]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  have hr : finrank ↥LL.1 V2 = r := by simpa using e.finrank_eq
  have hs2 : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) ρ2 τ a ≤ m := by
    intro τ
    simp only [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he']
    exact hsum τ
  obtain ⟨mm, k, hm, hk, hle⟩ := hT { V := V1, ρ := ρ1, cont := hc1, L := T1 }
    { V := V2, ρ := ρ2, cont := hc2, L := T2 } F r S η m h up b c1
    (GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he' h2) hFo hr
    (fun τ a ha => (c2 τ a ha).1) hb hs2 (fun τ a ha => (c2 τ a ha).2) (Or.inl he)
  refine ⟨mm, k, hm, hk, ?_⟩
  rw [he] at hle
  have h3 := hle.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg k))
  exact_mod_cast h3

theorem row_bound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  intro D r ρ large₂ ep CA h0 h1 hA hJ hF _ _ hLit hPar i hi π hπ dc
  refine ⟨fun w => ((⌈max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1))⌉ : ℤ) : ℚ), ?_, fun w _ => ?_⟩
  swap
  · rw [Rat.cast_intCast]
    exact (Int.ceil_lt_add_one _).le
  intro w hw _ C hC
  have hl4 : D.nd.l i % 4 = 3 := (h1 (D.nd.l i) (by simpa using hi.1.1)).1
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨-, hK1, he, -⟩ := h0 i hi.1.1 w hw
  have hG : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 hK1
  have hdeg : locDeg D.host.E w = finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) * 2 := by
    have h := ((hLit i hi).2.2.1 w hw).2.2
    unfold Br.DegW at h
    rw [← h, ← he]
    set_option synthInstance.maxHeartbeats 200000 in
      exact (Module.finrank_mul_finrank _ _ _).symm
  have hT := hA (D.nd.l i) hl2 _ _ hG
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht := large₂.t_win.1
  have hb : 1 ≤ large₂.sc.b := by unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar; linarith
  choose s Jc Jl j1 j2 _ j4 j5 j6 _ _ j9 using hJ i hi w hw C
  choose up bτ w1 w2 w3 using fun τ => jump_windows large₂.etaSz large₂.Sc large₂.sc.b D.R.t hη hS ht hPar (s τ) (Jc τ) (Jl τ)
    (j1 τ) (j2 τ) (fun a ha => (j5 τ a ha).1) (j6 τ)
  obtain ⟨f1, f2⟩ := hF i hi w hw C
  obtain ⟨g1, g2⟩ := f2 π hπ
  have hbd := boundA_le CA large₂.etaSz large₂.Sc large₂.sc.b (D.nd.l i) _ D.R.r D.R.t D.R.m _ (by omega) hη hS hb hdeg
  refine rowAt_of_thmA (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL CA hT he _ _
    ⌊large₂.Sc⌋₊ (⌊large₂.etaSz⌋₊ + D.R.t) D.R.m ⌊2 * large₂.sc.b⌋₊ up bτ _ ?_ g1 w1 ?_ ?_
  · intro V1 _ _ _ _ _ ρ1 hsub
    obtain ⟨c1, c2⟩ := f1 V1 ρ1 hsub
    refine ⟨c1, fun τ a ha => ?_⟩
    obtain ⟨x, hx⟩ := c2 τ a ha
    exact w2 τ a ((j9 τ x _).1 hx)
  · intro τ
    rw [← j4 τ]
    apply sum_le_card
    · intro a _
      by_cases hh : (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ)))
      · exact ((g2 τ a).1 hh).le
      · exact ((g2 τ a).2 hh).le.trans zero_le_one
    · intro a ha hn
      refine (g2 τ a).2 ?_
      rintro ⟨p, q⟩
      rcases (j9 τ π _).1 p with h | h | h
      · exact w3 τ a ha h
      · exact hn h
      · exact q h
  · rw [Rat.cast_intCast]
    exact hbd.trans (Int.le_ceil _)

end GlobalTheory.RowBoundB
end
end

