module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialKernelCyclotomicCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitCount

theorem locDeg_mul_ncard (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite ∧
      ∀ w ∈ placesOver E l, locDeg E w * (placesOver E l).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have him : HeightOneSpectrum.asIdeal '' placesOver E l = (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, GlobalTheory.HubLoc.liesOver_of_mem hl hv⟩
    · rintro ⟨hP, hlo⟩
      have hm : ((l : ℕ) : 𝓞 E) ∈ P := by
        have : (l : ℤ) ∈ P.under ℤ := by
          rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
        simpa [Ideal.under, Ideal.mem_comap] using this
      refine ⟨⟨P, hP, ?_⟩, hm, rfl⟩
      rintro rfl
      exact hl.ne_zero (by simpa using hm)
  refine ⟨Set.Finite.of_finite_image (him ▸ Algebra.QuasiFinite.finite_primesOver _) hinj.injOn, fun w hw => ?_⟩
  have := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have := w.isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ), ← him,
    Set.ncard_image_of_injective _ hinj, IsGalois.card_aut_eq_finrank] at h
  rw [← h, mul_comm]
  rfl

section Host
variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  obtain ⟨φ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  apply φ.injective
  rw [GlobalTheory.SplitRowProbe.conj_sqrt, GlobalTheory.SplitRowProbe.conj_sqrt, starRingEnd_self_apply]

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem cInt_coe (x : 𝓞 H.E) : (cInt H x : H.E) = H.conj (x : H.E) := rfl

theorem cInt_cInt (x : 𝓞 H.E) : cInt H (cInt H x) = x :=
  RingOfIntegers.ext (by rw [cInt_coe, cInt_coe, conj_conj])

def cPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap (cInt H).toRingHom (cInt H).surjective w

theorem mem_cPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (cPl H w).asIdeal ↔ cInt H x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : cPl H (cPl H w) = w :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cPl, mem_cPl, cInt_cInt])

theorem isConjPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (cPl H w) := by
  intro x y h
  have : y = cInt H x := RingOfIntegers.ext h
  rw [this, mem_cPl, cInt_cInt]

theorem mem_placesOver_of_conj {l : ℕ} {w w' : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E l)
    (h : IsConjPl H w w') : w' ∈ placesOver H.E l :=
  (h (l : 𝓞 H.E) (l : 𝓞 H.E) (by simp)).1 hw

end Host

theorem columns_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have hgal := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  set C := columns (N := D.nd) D.nbr i s with hC
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun w ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  have h2 : 2 * (locDeg D.host.E w * C.ncard) = 2 * D.R.f := by rw [← h]; ring
  omega

end GlobalTheory.SplitCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryBcrisOfDualExponentialZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.KerExpCrys

theorem finite_Ks {l : ℕ} [Fact l.Prime] (K : FinExt l) (j : ℕ) :
    FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

theorem cob_cris_of_expStar_zero : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → ∃ x : (D.loc l).R.B, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) = (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x := by
  intro D h2 h4 l _ K s hs e z hz
  obtain ⟨hpos, hzero⟩ := _root_.GlobalTheory.Cyc.ExpKernel.ker_expStar D h2 h4 l K s hs e z hz
  rcases Nat.eq_zero_or_pos e with he | he
  · have hI := hzero he
    subst he
    obtain ⟨⟨hc, -, hadd⟩, -⟩ := hz
    have hadd' : ∀ g h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l)),
        z ((g * h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l))) : GQ l) = z g + z h := by
      intro g h
      have := hadd g g.2 h h.2
      simpa using this
    have h1 : z 1 = 0 := by
      have := hadd' 1 1
      simpa using this
    obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedCrys.exists_rat (D.locA l) (D.locT l)
      (⟨Ks K s, finite_Ks K s⟩ : FinExt l) (fun g => z g) hc.restrict hadd' (by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx => exact hI x x.2 hx
        | one => exact h1
        | mul x y _ _ hx hy => rw [hadd', hx, hy, add_zero]
        | inv x _ hx =>
          have := hadd' x x⁻¹
          rw [mul_inv_cancel, hx, zero_add] at this
          rw [← this]
          exact h1)
    refine ⟨b, fun σ hσ => ?_⟩
    have := hb ⟨σ, hσ⟩
    simpa using this.symm
  · obtain ⟨y, -, hy⟩ := hpos he
    refine ⟨algebraMap ℚ_[l] _ y, fun σ hσ => ?_⟩
    rw [hy σ hσ, map_sub, map_mul, Algebra.smul_def]
    congr 2
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

end GlobalTheory.KerExpCrys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem exists_eq_of_coeff_box_eq_zero {R : Type} [CommRing R] (i n : ℕ) (D : R⟦X⟧⟦X⟧)
    (h : ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' D) = 0) :
    ∃ A B : R⟦X⟧⟦X⟧, D = X ^ (i + 1) * A + C (X ^ (n + 1)) * B := by
  classical
  obtain ⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by
    refine ⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩
    ext m
    rw [coeff_X_pow_mul', coeff_mk]
    split_ifs with hm
    · rw [coeff_mk, Nat.sub_add_cancel hm]
    · exact (h k hk m (by omega)).symm
  have hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_C_mul, hlow k (by omega), sub_self]
  obtain ⟨A, hA⟩ := hdvd
  exact ⟨A, B, by rw [← hA]; ring⟩

theorem coeff_frob2_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  intro l _ K _ φ₂ hC hX i n G H h
  obtain ⟨A, B, hAB⟩ := exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by
    rw [map_sub, map_sub, h i' hi' n' hn', sub_self])
  obtain ⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by
    rw [hX, map_pow]
    have hd := sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l
    rwa [add_sub_cancel_left] at hd
  have hl : 1 ≤ l := (Fact.out : Nat.Prime l).one_lt.le
  have e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A) := by
    rw [map_mul, map_pow, hc]
    ring
  have e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B := by
    rw [map_mul, hC, map_pow, frob_X, ← pow_mul]
  have hz : coeff n (coeff i (φ₂ (G - H))) = 0 := by
    rw [hAB, map_add (f := _), e1, e2, map_add (f := _), map_add (f := _), coeff_X_pow_mul',
      if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul',
      if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]
  rwa [map_sub, map_sub, map_sub, sub_eq_zero] at hz

end GlobalTheory.CrysPrism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisor
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CokerFinLen

theorem divApprox : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := GlobalTheory.T.exists_integral_powerSeries_division_approx

theorem exists_net {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset K, (∀ t ∈ T, ‖t‖ ≤ 1) ∧ ∀ x : K, ‖x‖ ≤ 1 → ∃ t ∈ T, ‖x - t‖ < δ := by
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  obtain ⟨t, hts, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1) hδ
  refine ⟨ht.toFinset, fun y hy => by simpa using hts (ht.mem_toFinset.1 hy), fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : K) 1 := by simpa using hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx')
  exact ⟨y, ht.mem_toFinset.2 hy, by simpa [dist_eq_norm] using hxy⟩

theorem exists_finset_reps {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (g : K⟦X⟧) (hg : g ∈ A O K) (hprim : ∃ n, ‖coeff n g‖ = 1) (c : K) (hc : c ≠ 0) :
    ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K, ∃ h ∈ A O K,
      f = r + q * g + C c * h := by
  classical
  have hδ : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨T, hT1, hT⟩ := exists_net (K := K) l hδ
  let n₀ := Nat.find hprim
  have hn₀ : ‖coeff n₀ g‖ = 1 := Nat.find_spec hprim
  have hlow : ∀ i < n₀, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne ((mem_A.1 hg) i) (Nat.find_min hprim hi)
  let mkR : (Fin n₀ → T) → K⟦X⟧ := fun t => PowerSeries.mk fun n =>
    if h : n < n₀ then ((t ⟨n, h⟩ : T) : K) else 0
  refine ⟨Finset.univ.image mkR, fun f hf => ?_⟩
  obtain ⟨q, hq, r, hr0, hr1, hrem⟩ := divApprox O K g hg n₀ hn₀ hlow _ hδ f hf
  choose t ht hrt using fun i : Fin n₀ => hT (coeff i r) (hr1 i)
  let r' := mkR fun i => ⟨t i, ht i⟩
  have hcoeff : ∀ n, coeff n r' = if h : n < n₀ then t ⟨n, h⟩ else 0 := fun n => by
    simp [r', mkR, coeff_mk]
  have hr'A : r' ∈ A O K := mem_A.2 fun n => by
    rw [hcoeff]; split_ifs
    · exact hT1 _ (ht _)
    · simp
  set d := f - q * g - r' with hd
  have hdn : ∀ n, ‖coeff n d‖ ≤ ‖c‖ := fun n => by
    have : d = (f - q * g - r) + (r - r') := by rw [hd]; ring
    rw [this, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrem n) ?_)
    rw [map_sub, hcoeff]
    split_ifs with h
    · exact (hrt ⟨n, h⟩).le
    · rw [hr0 n (not_lt.1 h), sub_zero, norm_zero]; exact hδ.le
  refine ⟨r', Finset.mem_image_of_mem mkR (Finset.mem_univ (fun i => (⟨t i, ht i⟩ : T))), hr'A, q, hq, C c⁻¹ * d,
    mem_A.2 fun n => ?_, ?_⟩
  · rw [coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hdn n) (norm_nonneg _)
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, hd]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.rdivSet τ) → IsFiniteLength (A O K) F.coker := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hY h1
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  have hc : ∀ τ, ∃ c : K, c ≠ 0 ∧ ∃ Y : Matrix ι κ K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      F.mat τ * Y = C c • (1 : Matrix κ κ K⟦X⟧) := by
    intro τ
    obtain ⟨-, Y, ⟨B, hB⟩, hFY⟩ := h1 τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(l : K)‖ ^ m * B < 1 := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (norm_l_lt_one (K := K) l)).mul_const B
      rw [zero_mul] at h
      exact (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨(l : K) ^ m, pow_ne_zero _ (l_ne_zero l), C ((l : K) ^ m) • Y,
      fun i j => mem_A.2 fun n => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul, coeff_C_mul, norm_mul, norm_pow]
      calc _ ≤ ‖(l : K)‖ ^ m * B := mul_le_mul_of_nonneg_left (hB i j n) (by positivity)
        _ ≤ 1 := hm.le
    · rw [Matrix.mul_smul, hFY, one_smul]
  choose c hc0 Y₁ hY₁A hY₁ using hc
  choose Yg g hYgA hgprim hYg using hY
  have hgA : ∀ τ (j : κ), g τ ∈ A O K := fun τ j => by
    have h := congrFun (congrFun (hYg τ) j) j
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply] at h
    rw [← h]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (F.mem τ j k) (hYgA τ k j)
  have hR : ∀ τ (j : κ), ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K,
      ∃ h ∈ A O K, f = r + q * g τ + C (c τ) * h := fun τ j =>
    exists_finset_reps l (g τ) (hgA τ j) (hgprim τ) (c τ) (hc0 τ)
  choose R hR using hR
  let Sset : Set Q.M := {v | ∀ τ j, (v : Vec K a κ) τ j ∈ R τ j}
  have hS : Sset.Finite := by
    have hfin : (Set.pi Set.univ fun τ => Set.pi Set.univ fun j => ((R τ j : Set K⟦X⟧))).Finite :=
      Set.Finite.pi fun τ => Set.Finite.pi fun j => (R τ j).finite_toSet
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact hv
  have hsurj : ∀ x : F.coker, x ∈ (Submodule.Quotient.mk '' Sset : Set F.coker) := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : ∀ τ j, (v : Vec K a κ) τ j ∈ A O K := fun τ j => mem_tot.1 v.2 τ j
    choose r hrR hrA q hqA h hhA hdec using fun τ j => hR τ j _ (hv τ j)
    refine ⟨⟨fun τ j => r τ j, mem_tot.2 fun τ j => hrA τ j⟩, hrR, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    unfold Hom.imM
    rw [Submodule.mem_map]
    refine ⟨fun τ => -(Yg τ *ᵥ q τ + Y₁ τ *ᵥ h τ), mem_tot.2 fun τ i => ?_, ?_⟩
    · have hmv : ∀ (Y : Matrix ι κ K⟦X⟧) (w : κ → K⟦X⟧), (∀ i j, Y i j ∈ A O K) →
          (∀ j, w j ∈ A O K) → ∀ i, (Y *ᵥ w) i ∈ A O K := fun Y w hY hw i =>
        Subalgebra.sum_mem _ fun j _ => mul_mem (hY i j) (hw j)
      exact neg_mem (add_mem (hmv _ _ (hYgA τ) (hqA τ) i) (hmv _ _ (hY₁A τ) (hhA τ) i))
    · ext τ j
      simp only [LinearMap.restrictScalars_apply, Hom.app_apply, Matrix.mulVec_neg,
        Matrix.mulVec_add, Matrix.mulVec_mulVec, hYg, hY₁, Matrix.smul_mulVec,
        Matrix.one_mulVec, Submodule.coe_sub, Pi.sub_apply, Pi.neg_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hdec τ j]
      ring_nf
  haveI : Finite F.coker :=
    Set.finite_univ_iff.1 ((hS.image _).subset fun x _ => hsurj x)
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_finite _ _, isArtinian_of_finite⟩

end GlobalTheory.CokerFinLen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffFamilyFrobeniusCongrPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem cstW_mem_QSet_of_const (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, 0) then c else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp only [cstW, coeff_C]
  by_cases hi : i = 0
  · by_cases hn : n = 0
    · simp [hi, hn, dpDen]
    · simp [hi, hn, coeff_C]
  · simp [hi]

theorem exists_sigma_eq_pow_add (c : Wq l a) : ∃ d : Wq l a, sigma l a c = c ^ l + (l : Wq l a) * d := by
  have h : sigma l a c - c ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, coeff_sigma, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
  exact ⟨d, by rw [← hd]; ring⟩

end

theorem cstW_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ c
  have h1 : frob2 φ₂ (cstW t K c) = cstW t K (sigma l a c) := by
    funext τ
    change φ₂ (cstW t K c (τ - 1)) = _
    simp only [cstW]
    rw [hC, frob_C, emb_sigma]
  refine ⟨cstW_mem_QSet_of_const t K e c, h1 ▸ cstW_mem_QSet_of_const t K e _, ?_⟩
  obtain ⟨d, hd⟩ := exists_sigma_eq_pow_add c
  refine ⟨cstW t K d, cstW_mem_QSet_of_const t K e d, ?_⟩
  rw [h1, hd]
  funext τ
  simp [cstW]

end GlobalTheory.CrysPrism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordinatesEqOfEisensteinPowMulInverseMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_ofA_of_injective [NeZero a] (hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)))
    (P : PhiMod O K l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (hβ : ∀ τ j i, E K l e ^ β * P.mxInv τ j i ∈ A O K) (τ : ZMod a) (j i : ι) :
    y τ j i = ofA O K l e ⟨E K l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  apply hinj
  rw [hy, ← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) _
    (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

end Gen

end GlobalTheory.BK.CoordInv


open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv_eq_ofA : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P β y hy hβ τ j i
  exact eq_ofA_of_injective (algebraMap_AhatE_injective l e) P β y hy hβ τ j i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallLetterTypeFunctionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_letterType_functional : ∀ {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F] [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L] [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D], (∀ (c : U) (x : D), c • x = m c x) → (∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) → ∀ x : D, (∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F), f x = 0) → x = 0 := by
  first | exact @GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | exact GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | (intros; apply GlobalTheory.LetterSep.eq_zero_of_forall_letterHom <;> assumption)
end

