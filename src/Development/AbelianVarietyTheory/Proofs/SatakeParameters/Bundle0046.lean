module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfiStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  first | exact @GlobalTheory.SplitField.descend_decomp | exact GlobalTheory.SplitField.descend_decomp | (intros; apply GlobalTheory.SplitField.descend_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbeddingStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_at_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m), Thick D.host g → L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  first | exact @GlobalTheory.HTW.SizeThick.size_thick | exact GlobalTheory.HTW.SizeThick.size_thick | (intros; apply GlobalTheory.HTW.SizeThick.size_thick <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.InertWord

theorem inert_nothree_nonthick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 →
    ¬ (φ = R.cc ∧ Thick H τ) →
    NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧
      ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  intro R H τ φ hL hφ hnot
  have h2 : 2 ≤ orderOf φ := by
    rw [_root_.GlobalTheory.orderOf_moving_stmt φ hφ]
    exact Nat.le_of_dvd (Nat.lcm_pos two_pos (orderOf_pos _)) (Nat.dvd_lcm_left _ _)
  by_cases hc : φ = R.cc
  · have hτ : ¬ Thick H τ := fun h => hnot ⟨hc, h⟩
    subst hc
    have hno : ∀ i : ZMod (orderOf (R.cc)), ¬ Thick H (letter τ (R.cc) i) := by
      intro i h
      apply hτ
      have := (_root_.GlobalTheory.HTW.ConjWord.conj_word_one_place τ).2 i
      unfold Thick at h ⊢
      rw [this] at h
      exact h
    exact _root_.GlobalTheory.noThree_of_atMostOne _ h2 (fun a b ha _ => absurd ha (hno a))
  · by_cases hlen : 4 * H.Lw < orderOf φ.2
    · exact _root_.GlobalTheory.noThree_of_windowTwo _ H.Lw hL (_root_.GlobalTheory.HTW.LongWindow.main H τ φ hlen)
    · have h1 : φ ≠ 1 := by
        rintro rfl
        exact absurd (show (1 : ℤˣ) = -1 from hφ) (by decide)
      have adj : ∀ i : ZMod (orderOf φ), ¬ (Thick H (letter τ φ i) ∧ Thick H (letter τ φ (i + 1))) := fun i h =>
        UpperTheory.KStar.Words.placeOf_letter_succ_ne τ φ h1 hc i
          (_root_.GlobalTheory.HTW.short_orbit_one_thick H τ φ (not_lt.mp hlen) (i + 1) i h.2 h.1)
      refine ⟨fun i h => adj i ⟨h.1, h.2.1⟩, ?_⟩
      by_contra hall
      have hall' : ∀ i, Thick H (letter τ φ i) := fun i => by_contra fun hi => hall ⟨i, hi⟩
      exact adj 0 ⟨hall' 0, hall' (0 + 1)⟩

end GlobalTheory.HTW.InertWord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternalStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  first | exact @GlobalTheory.SplitField.isoSub_summand_of_isInternal | exact GlobalTheory.SplitField.isoSub_summand_of_isInternal | (intros; apply GlobalTheory.SplitField.isoSub_summand_of_isInternal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfMultVNeZero
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.TwistDualLoc

def matGRep {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_dot {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) :
    IsDual1 PD (matRep M) (matRep (twistM (dualM M) (cycLL PD LL))) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose).mulVec y) =
      ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

end

end GlobalTheory.HTW.TwistDualLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint
section
noncomputable section

namespace GlobalTheory.ParamRepCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped Pointwise

section Inertia

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_lt_one_iff_eq_zero_or_inv_notMem' (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← B.valuation_le_one_iff, map_inv₀]
    have h0 : 0 < B.valuation y := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hy
    simp [hy, inv_le_one₀ h0]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma smul_mem_smul_valuationSubring_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    h • y ∈ h • B ↔ y ∈ B := by
  refine ⟨fun hy => ?_, ValuationSubring.smul_mem_pointwise_smul h y B⟩
  have := ValuationSubring.smul_mem_pointwise_smul h⁻¹ _ _ hy
  simpa [smul_smul] using this

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_smul_smul_lt_one_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    (h • B).valuation (h • y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem', valuation_lt_one_iff_eq_zero_or_inv_notMem', ← smul_inv'',
    smul_mem_smul_valuationSubring_iff]
  simp


open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
theorem _root_.GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq {A A' : ValuationSubring Ω} {g σ : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : g • A = A') (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A') : g⁻¹ * σ * g ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A := by
  subst hg
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    rw [mul_smul, mul_smul, hdec, inv_smul_smul]
  · rw [← valuation_smul_smul_lt_one_iff g]
    have hx' : (g • A).valuation (g • x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact ValuationSubring.smul_mem_pointwise_smul g x A hx
    have := hval (g • x) hx'
    convert this using 2
    rw [smul_sub]
    simp [AlgEquiv.smul_def]

end Inertia

section Clauses

variable (D : D7)

end Clauses

end GlobalTheory.ParamRepCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem window_and_cTB_of_jumps_at_embeddings :
    ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  intro S Y h r n t _ _ hs hcard hn hg hv hth hU
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  refine ⟨fun a ha => ?_, fun e he => ?_⟩
  · have := hb a (Finset.mem_coe.1 (hsub ha))
    omega
  · unfold LocalSituation.cTBY
    rw [hg, hs, hv]
    exact cTB_le (LocalSituation.ell S) h t (n * r) e S.PD.hp _ _ hsub hc hb he hth

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMHStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_mem_box_neg_M_h : ∀ {n : ℕ} (W : WordData n), (∀ i, 0 ≤ W.sz i) → W.T1 → ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  first | exact @GlobalTheory.HTW.WordData.jumps_mem_box | exact GlobalTheory.HTW.WordData.jumps_mem_box | (intros; apply GlobalTheory.HTW.WordData.jumps_mem_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_degW {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N)
    (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) :
    Br.DegW nbr i w hw := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl (N.l i) := (nbr i w hw).j.comp (algebraMap H.E N.Om)
  have hK : (nbr i w hw).Kw.1 = IntermediateField.adjoin ℚ_[N.l i] (Set.range c) :=
    _root_.GlobalTheory.padicAlgCl_finite_dense_eq_adjoin (N.l i) H.E c (nbr i w hw).Kw.1 (nbr i w hw).j_E (nbr i w hw).Kw.2
      (nbr i w hw).j_dense
  obtain ⟨v, hv, hc⟩ := _root_.GlobalTheory.LocPlace.exists_place_of_emb (N.l i) H.E c
  have h1 := _root_.GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer (N.l i) H.E c v hc
  have h2 := _root_.GlobalTheory.DecompCard.card_stabilizer_eq_locDeg (N.l i) H.E v w hv hw
  have h3 : Module.finrank ℚ_[N.l i] (nbr i w hw).Kw.1 = locDeg H.E w := by
    rw [hK, h1, h2]
  exact h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensional
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.LocalH1Finiteness

theorem matRep_apply' {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (g : ↥(GK K)) (v : Fin k → ↥LL.1) (a : Fin k) :
    matRep M g v a = ∑ b, M g a b * v b := rfl

theorem finite_continuous_cocycles_matRep (hK : Formalism.GaloisCohomology.LocalFinitenessK) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hM : Continuous fun g => M g)
    (hi : ∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) :
    Module.Finite ↥LL.1 (continuousCocycles (matRep M)) := by
  have := LL.2
  have := K.2
  let φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K) :=
    (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom
  have hφ : Continuous φ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2
  have hφs : Function.Surjective φ := (IntermediateField.fixingSubgroupEquiv K.1).symm.surjective
  have hc : ReciprocityTheory.Gal.ContAction (matRep M) := by
    refine continuous_pi fun a => ?_
    simp only [matRep_apply']
    refine continuous_finsetSum _ fun b _ =>
      Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)
    exact (hM.comp continuous_fst).matrix_elem a b
  have hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖ := fun g v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [matRep_apply']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)
  exact finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs
    (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)

theorem finite_H1fV_matRep : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1),
    Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) →
    Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  intro hK l _ P K LL k M hM hi
  have h1 := finite_continuous_cocycles_matRep hK K LL M hM hi
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M)) :=
    Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 :
      finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)
  exact Module.Finite.quotient _ _

end GlobalTheory.LocalH1Finiteness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLength
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := _root_.GlobalTheory.HTW.LongWindow.main H τ φ h4
  refine ⟨_root_.GlobalTheory.HTW.winClusters _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBound
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem wMax_le_and_ge : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  intro D L C hR
  have hb : (0 : ℝ) ≤ L.sc.b' := by
    obtain ⟨-, h1, -, h3, -⟩ := hR
    linarith
  have hmem : ∀ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat},
      (s : ℝ) ≤ 8 / 5 * L.sc.b' := by
    rintro s ⟨g, j, hg, rfl⟩
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HTW.size_not_thick L C g j hR hg
    have h100 : (100 : ℝ) ≤ L.sc.w'' D.R.n := hR.2.1
    have hpos : (0 : ℤ) ≤ ⌊(hcAt D g).e j⌋ := by
      have : (0 : ℝ) ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    have : ((⌊(hcAt D g).e j⌋.toNat : ℤ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [Int.toNat_of_nonneg hpos]
    have h' : ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [← this]; norm_cast
    rw [h']; exact h2
  have hbdd : BddAbove {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} := by
    refine ⟨⌊8 / 5 * L.sc.b'⌋₊, fun s hs => ?_⟩
    exact Nat.le_floor (hmem s hs)
  refine ⟨?_, ?_⟩
  · unfold wMax
    rcases Set.eq_empty_or_nonempty {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} with he | hne
    · rw [he, csSup_empty]; simp; linarith
    · obtain ⟨s, hs, hseq⟩ : ∃ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, s = sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} :=
        ⟨_, Nat.sSup_mem hne hbdd, rfl⟩
      rw [← hseq]; exact hmem s hs
  · intro g j hg
    have h1 : ⌊(hcAt D g).e j⌋.toNat ≤ wMax D := le_csSup hbdd ⟨g, j, hg, rfl⟩
    calc ⌊(hcAt D g).e j⌋ ≤ (⌊(hcAt D g).e j⌋.toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (wMax D : ℤ) := by exact_mod_cast h1

end GlobalTheory.HTW
end

