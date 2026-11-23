module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProduct
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Pass

theorem ambient_h1f_of_local_finiteness : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (i : D.nd.Loc)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i),
    Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) →
    EmbeddingTypes.H1fFiniteRankTorsion (D := D) i ρ π dc := by
  intro hLF D i ρ π dc hc _ w hw _ C L2 _ n
  obtain ⟨⟨_, hdvr, hfr⟩, -⟩ := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  haveI := hdvr
  haveI := hfr
  have hcont := _root_.GlobalTheory.TwistedDualLoc.continuous_and_integral D i w hw C.LL C.le ρ π hc
  have hfin := _root_.GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep hLF (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL D.R.r
    (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) hcont.1 hcont.2
  exact GlobalTheory.T.period_data_crystalline_admissible (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) L2 hfin n

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_finite_ext_numberField_sqrt (Qq E K : Type) [Field Qq] [Field E] [Field K]
    [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : Qq) :
    ∃ (Kf : IntermediateField Qq (AlgebraicClosure Qq)) (s : Kf) (eK : K →+* Kf),
      FiniteDimensional Qq Kf ∧ s ^ 2 = algebraMap Qq Kf a ∧
        ∀ x : E, eK (e x) = algebraMap Qq Kf (i x) := by
  classical
  let Ω := AlgebraicClosure Qq
  letI : Algebra E K := e.toAlgebra
  letI : Algebra E Ω := ((algebraMap Qq Ω).comp i).toAlgebra
  haveI : CharZero E := RingHom.charZero e
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let f : K →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Qq Ω a) (n := 2) two_pos
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := E) (M := K)
  let S : Set Ω := insert s (f '' (T : Set K))
  haveI : Finite S := ((T.finite_toSet.image f).insert s).to_subtype
  let Kf : IntermediateField Qq Ω := IntermediateField.adjoin Qq S
  have hfin : FiniteDimensional Qq Kf :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x : K, f x ∈ Kf := by
    intro x
    have hx : x ∈ Submodule.span E (T : Set K) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      exact IntermediateField.subset_adjoin Qq S (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, Algebra.smul_def]
      exact mul_mem (Kf.algebraMap_mem (i c)) hy
  refine ⟨Kf, ⟨s, IntermediateField.subset_adjoin Qq S (Set.mem_insert _ _)⟩,
    (f : K →+* Ω).codRestrict Kf hmem, hfin, Subtype.ext hs, fun x => Subtype.ext ?_⟩
  exact f.commutes x

theorem exists_complete_dvr_ext_numberField_sqrt : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  intro W Qq E K _ _ _ _ _ _ _ _ _ _ i e a
  obtain ⟨Kf, s, eK, hfin, hs, he⟩ :=
    exists_finite_ext_numberField_sqrt Qq E K i e (algebraMap W Qq a)
  letI : Algebra W Kf := ((algebraMap Qq Kf).comp (algebraMap W Qq)).toAlgebra
  haveI : IsScalarTower W Qq Kf := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI h1 := FormalIsogeny.finite_integralClosure W Qq Kf
  haveI h2 := FormalIsogeny.isDiscreteValuationRing_integralClosure W Qq Kf
  have h3 := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite W (integralClosure W Kf)
  have h4 := integralClosure.isFractionRing_of_finite_extension (A := W) Qq Kf
  have hs' : s ^ 2 = algebraMap W Kf a := hs
  have hint : IsIntegral W s :=
    IsIntegral.of_pow two_pos (hs' ▸ isIntegral_algebraMap)
  exact ⟨integralClosure W Kf, Kf, inferInstance, inferInstance, h2, inferInstance, inferInstance,
    algebraMap Qq Kf, algebraMap W _, ⟨s, hint⟩, eK, h4, fun _ => rfl,
    RingHom.finite_algebraMap.2 h1, h3, Subtype.ext hs', he⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  first | exact @GlobalTheory.TameRel.main | exact GlobalTheory.TameRel.main | (intros; apply GlobalTheory.TameRel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGlobalLatticeLocalGiven
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]



end TupApx

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_constituents_charpoly_product : SSList := by
  first | exact @GlobalTheory.ssList_holds | exact GlobalTheory.ssList_holds | (intros; apply GlobalTheory.ssList_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
section
open NumberField IsDedekindDomain Formalism.L2.Col

noncomputable section
namespace GlobalTheory.GprimUnder

theorem conjO_conjO (X : Fields) (a : 𝓞 X.E) : X.conjO (X.conjO a) = a := by
  apply RingOfIntegers.ext
  show star (star (a : X.E)) = (a : X.E)
  exact star_star _

theorem conjO_algebraMap (X : Fields) (hX : X.Ok) (x : 𝓞 X.F) :
    X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) x) = algebraMap (𝓞 X.F) (𝓞 X.E) x := by
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)
  have : ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F) := rfl
  rw [this]
  exact hX.star_F _

theorem mem_divs_iff {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  rfl

def conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime X.conjO P.asIdeal
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO]
      exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← conjO_conjO X x, h1, map_zero]

theorem mem_conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (a : 𝓞 X.E) :
    a ∈ (conjPrime X P).asIdeal ↔ X.conjO a ∈ P.asIdeal := Ideal.mem_comap

theorem under_conjPrime (X : Fields) (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime X P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal
  rw [mem_conjPrime, conjO_algebraMap X hX]

theorem exists_vG_under : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)),
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  intro X Pr hX hPr i P hP
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hc0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact hg0 h1.symm
  have hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal := fun v => mem_divs_iff hc0 v
  rw [← hPr.piG_norm i] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · refine ⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩
    rw [mem_conjPrime, conjO_conjO]
    exact h
  · exact ⟨P, (hvG P).2 h, rfl⟩

end GlobalTheory.GprimUnder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnimodularLatticeLocalMatch
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace GlobalTheory.GO.SplitGlue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_smul_le {N N' : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsFullLattice E N)
    (hN' : Submodule.IsLattice E N') : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  have h0 : ∀ x : Sp E n, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span E (N : Set (Sp E n)) := Submodule.IsFullLattice.span_eq_top (self := hN) ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n)) x hx
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  obtain ⟨s, rfl⟩ := hN'.fg
  choose a ha0 ha using h0
  refine ⟨∏ y ∈ s, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ hy, mul_smul]
    exact N.smul_mem _ (ha y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy


omit [StarRing E] in
theorem mem_of_forall (N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ s ∉ w.asIdeal, s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 E) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))


omit [StarRing E] in
theorem eq_of_sameAt {N N' : Submodule (𝓞 E) (Sp E n)} (h : ∀ w, SameAt w N N') : N = N' := by
  apply le_antisymm
  · intro x hx
    refine mem_of_forall N' fun w => ?_
    obtain ⟨_, _, a', ha', _, h2⟩ := h w
    exact ⟨a', ha', h2 x hx⟩
  · intro x hx
    refine mem_of_forall N fun w => ?_
    obtain ⟨a, ha, _, _, h1, _⟩ := h w
    exact ⟨a, ha, h1 x hx⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', h3, h4⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h3 x hx)
  · rw [mul_smul]; exact h4 _ (h2 x hx)

theorem conjP_conjP (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem sameAt_dual {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt (conjPrime₂ Q) (dual (hStd E n) N) (dual (hStd E n) N') := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨cO E a', by rwa [mem_conjP, cO_cO], cO E a, by rwa [mem_conjP, cO_cO], fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h2 y hy)
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h1 y hy)

theorem exists_glue {L L' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsFullLattice E L) (hL' : Submodule.IsFullLattice E L')
    (P : HeightOneSpectrum (𝓞 E)) : ∃ L'' : Submodule (𝓞 E) (Sp E n), Submodule.IsFullLattice E L'' ∧ SameAt P L' L'' ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q L L'' := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_smul_le hL hL'.toIsLattice
  obtain ⟨b, hb0, hb⟩ := exists_smul_le hL' hL.toIsLattice
  have hI : Ideal.span {a * b} ≠ ⊥ := by simpa using ⟨ha0, hb0⟩
  obtain ⟨J, hJ, hdJ⟩ := Ideal.eq_prime_pow_mul_coprime hI P.asIdeal (hpm := P.isMaximal)
  generalize Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a * b})) = k at hdJ
  have hdvd : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∃ c, r * s = c * (a * b) := by
    intro r hr s hs
    have := Ideal.mul_mem_mul hr hs
    rw [← hdJ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  have h1 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L, (r * s) • x ∈ L' := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, ← mul_assoc, mul_smul]
    exact L'.smul_mem _ (hb x hx)
  have h2 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L', (r * s) • x ∈ L := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, mul_comm a b, ← mul_assoc, mul_smul]
    exact L.smul_mem _ (ha x hx)
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ P.asIdeal := by
    by_contra H
    push Not at H
    have : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl H
    rw [hJ] at this
    exact P.isPrime.ne_top (top_le_iff.1 this)
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP P.asIdeal.zero_mem
  let L'' : Submodule (𝓞 E) (Sp E n) := J • L' ⊔ (P.asIdeal ^ k) • L
  have hA : ∀ x ∈ L', s • x ∈ L'' := fun x hx => Submodule.mem_sup_left (Submodule.smul_mem_smul hsJ hx)
  have hB : ∀ x ∈ L'', s • x ∈ L' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L'.add_mem (L'.smul_mem _ (Submodule.smul_le_right hy)) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact h1 r hr s hsJ u hu
    · rw [smul_add]; exact L'.add_mem hu hv
  refine ⟨L'', ?_, ⟨s, hsP, s, hsP, hB, hA⟩, fun Q hQ => ?_⟩
  · have hsup : Submodule.IsLattice E (L' ⊔ L) :=
      ⟨hL'.fg.sup hL.fg, by
        intro s hs hli
        exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩
    let : Submodule.IsLattice E L'' := lattice_of_smul hL'.toIsLattice hsup (sup_le_sup Submodule.smul_le_right Submodule.smul_le_right) hs0 hA
    refine { span_eq_top := ?_ }
    apply top_unique
    intro x hx
    have hx' : x ∈ Submodule.span E (L' : Set (Sp E n)) :=
      Submodule.IsFullLattice.span_eq_top (self := hL') ▸ Submodule.mem_top
    have hspan : ∀ y ∈ L', y ∈ Submodule.span E (L'' : Set (Sp E n)) := by
      intro y hy
      have hsE : (algebraMap (𝓞 E) E s) ≠ 0 :=
        fun h => hs0 ((IsFractionRing.injective (𝓞 E) E) (by simpa using h))
      have hy' : s • y ∈ Submodule.span E (L'' : Set (Sp E n)) := Submodule.subset_span (hA y hy)
      rw [← IsScalarTower.algebraMap_smul E s y] at hy'
      have := (Submodule.span E (L'' : Set (Sp E n))).smul_mem (algebraMap (𝓞 E) E s)⁻¹ hy'
      rw [← mul_smul, inv_mul_cancel₀ hsE, one_smul] at this
      exact this
    exact (Submodule.span_le.mpr hspan) hx' 
  · obtain ⟨t, htP, htQ⟩ := exists_mem_notMem hQ.symm
    have ht : t ^ k ∈ P.asIdeal ^ k := Ideal.pow_mem_pow htP k
    have ht' : t ^ k ∉ Q.asIdeal := fun h => htQ (Q.isPrime.mem_of_pow_mem k h)
    refine ⟨t ^ k, ht', t ^ k, ht', fun x hx => ?_, fun x hx => Submodule.mem_sup_right (Submodule.smul_mem_smul ht hx)⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L.add_mem ?_ (L.smul_mem _ (Submodule.smul_le_right hz))
    refine Submodule.smul_induction_on hy (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul]; exact h2 _ ht r hr u hu
    · rw [smul_add]; exact L.add_mem hu hv

theorem exists_selfDual_prescribed (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N M : Submodule (𝓞 E) (Sp E n)) (Q : HeightOneSpectrum (𝓞 E)) (hQ : conjPrime₂ Q ≠ Q) (hN : Submodule.IsFullLattice E N)
    (hu : IsUnimodular (hStd E n) N) (hM : Submodule.IsFullLattice E M) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      localization₂ Q.asIdeal N' = localization₂ Q.asIdeal M ∧
      ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → localization₂ Q'.asIdeal N' = localization₂ Q'.asIdeal N := by
  have hsymm : (hStd E n).IsSymm := ⟨fun x y => by
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, starRingEnd_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
  have hdual := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Sp E n) (hStd E n) hsymm hStd_nondeg star_range M hM
  obtain ⟨L, hL, hLQ, hLo⟩ := exists_glue hN hM Q
  obtain ⟨N', hN', hc, ho⟩ := exists_glue hL hdual.1 (conjPrime₂ Q)
  have h1 : SameAt Q M N' := sameAt_trans hLQ (ho Q hQ.symm)
  have h2 : ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → SameAt Q' N N' :=
    fun Q' a b => sameAt_trans (hLo Q' a) (ho Q' b)
  refine ⟨N', hN'.toIsLattice, ?_, h1.localization_eq, fun Q' a b => (h2 Q' a b).localization_eq⟩
  refine eq_of_sameAt fun w => ?_
  by_cases hw : w = Q
  · subst hw
    have := sameAt_dual hc
    rw [conjP_conjP, hdual.2.1] at this
    exact sameAt_trans (sameAt_symm this) h1
  by_cases hw' : w = conjPrime₂ Q
  · subst hw'
    exact sameAt_trans (sameAt_symm (sameAt_dual h1)) hc
  have := sameAt_dual (h2 (conjPrime₂ w) (fun h => hw' (by rw [← h, conjP_conjP]))
    (fun h => hw (by rw [← conjP_conjP w, h, conjP_conjP])))
  rw [conjP_conjP, show dual (hStd E n) N = N from hu] at this
  exact sameAt_trans (sameAt_symm this) (h2 w hw hw')

end GlobalTheory.GO.SplitGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublatticeStatement
section
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMap_diagUniformizer_elementarySublattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  first | exact @GlobalTheory.DiagElem.glMap_diag_mem_subElem | exact GlobalTheory.DiagElem.glMap_diag_mem_subElem | (intros; apply GlobalTheory.DiagElem.glMap_diag_mem_subElem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixedStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.tame_vanish | exact GlobalTheory.StringRepresentationDecomposition.tame_vanish | (intros; apply GlobalTheory.StringRepresentationDecomposition.tame_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamifiedStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  first | exact @GlobalTheory.CartanCoinv.translate_mem_twKer | exact GlobalTheory.CartanCoinv.translate_mem_twKer | (intros; apply GlobalTheory.CartanCoinv.translate_mem_twKer <;> assumption)
end

