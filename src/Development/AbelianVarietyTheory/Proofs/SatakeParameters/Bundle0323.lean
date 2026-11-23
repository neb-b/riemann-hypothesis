module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CMFam

open IntermediateField

theorem exists_qcm_adjoin (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ) (hp : 0 < p) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω))
    (hn : δ ∉ Set.range (algebraMap E Ω)) :
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} :=
  _root_.GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg E Ω p hp δ hδ hn

theorem isSplitAt_of_dvd (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L) (hp : 0 < p)
    (hδ : δ ^ 2 = -(p : L)) (hq : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) (w : HeightOneSpectrum (𝓞 L))
    (hw : (q : 𝓞 L) ∈ w.asIdeal) : GlobalTheory.UnitaryBC.IsSplitAt w :=
  _root_.GlobalTheory.SplitOfNegPrime.isSplitAt L p q δ hp hδ hq w hw

theorem not_isUnramifiedAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (δ : K) (hδ : δ ^ 2 = -(p : K))
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal :=
  _root_.GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg E K p hp hd δ hδ w hw

theorem exists_unram (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K]
      (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal :=
  _root_.GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield E

theorem even_finrank (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) :=
  _root_.GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield E Ω Q

end GlobalTheory.CMFam

namespace GlobalTheory.CMFam

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q n : ℕ} (hq : q.Prime)
    (hqw : (q : 𝓞 K) ∈ w.asIdeal) (hn : (n : 𝓞 K) ∈ w.asIdeal) : q ∣ n := by
  by_contra h
  have hc : Nat.gcd q n = 1 := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hm : (((Nat.gcd q n : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab q n]
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hqw) (w.asIdeal.mul_mem_right _ hn)
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem natCast_mem_under {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal ↔ (n : 𝓞 K) ∈ w.asIdeal := by
  change _ ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, map_natCast]

end GlobalTheory.CMFam


open GlobalTheory.CMFam GlobalTheory.ExSplitCM in
theorem GlobalTheory.GalCut.infinite_qcm_split_good : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  intro hAF E Ω _ _ _ _ _ _ l _ a π w₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q₀, hq₀, hq₀w⟩ := exists_prime_mem w₀
  haveI : Fact q₀.Prime := ⟨hq₀⟩
  obtain ⟨N, hN0, hN⟩ := exists_unram E
  set S : Set (HeightOneSpectrum (𝓞 E)) := {v | ¬ ∃ B, (CG.mk π).HasSat v B} with hSdef
  have hS : S.Finite := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π)
  set T : Finset ℕ := ({2, l, q₀} : Finset ℕ) ∪ N.primeFactors ∪ (discr E).natAbs.primeFactors ∪
    (finite_primes_of_finite hS).toFinset with hTdef
  set M : ℕ := 8 * ∏ q ∈ T, q with hM
  have hT2 : 2 ∈ T := by simp [hTdef]
  have hTl : l ∈ T := by simp [hTdef]
  have hTq₀ : q₀ ∈ T := by simp [hTdef]
  have hTN : ∀ r : ℕ, r.Prime → r ∣ N → r ∈ T := fun r hr hd => by
    simp [hTdef, Nat.mem_primeFactors, hr, hd, hN0]
  have hTd : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ T := fun r hr hd => by
    have : r ∈ (discr E).natAbs.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hr, Int.natCast_dvd.1 hd, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩
    simp [hTdef, this]
  have hTS : ∀ r : ℕ, r.Prime → ∀ v ∈ S, (r : 𝓞 E) ∈ v.asIdeal → r ∈ T := fun r hr v hv h => by
    have : r ∈ (finite_primes_of_finite hS).toFinset := by simpa using ⟨hr, v, hv, h⟩
    simp [hTdef, this]
  have hM0 : M ≠ 0 := by
    rw [hM]
    refine mul_ne_zero (by norm_num) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq h0
    subst h0
    simp [hTdef] at hq
    rcases hq with h | h | h
    · exact (Fact.out : l.Prime).ne_zero h.symm
    · exact hq₀.ne_zero h.symm
    · exact Nat.not_prime_zero h.1
  haveI : NeZero M := ⟨hM0⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  set Gd : Set ℕ := {p | p.Prime ∧ p ∉ T ∧ (M : ℤ) ∣ (p : ℤ) + 1} with hGd
  have hGood : Gd.Infinite := by
    refine ((Nat.infinite_setOfPred_prime_and_eq_mod (q := M) isUnit_one.neg).diff T.finite_toSet).mono ?_
    rintro p ⟨⟨hp, hpe⟩, hpT⟩
    refine ⟨hp, hpT, ?_⟩
    have : (((p : ℤ) + 1 : ℤ) : ZMod M) = 0 := by push_cast; rw [hpe]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h8 : ∀ p ∈ Gd, ∀ q ∈ T, ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 := fun p hp q hq => by
    refine dvd_trans ?_ hp.2.2
    rw [Int.natCast_dvd_natCast, hM]
    exact Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem _ hq)
  have hodd : ∀ p ∈ Gd, p ≠ 2 := fun p hp h => hp.2.1 (h ▸ hT2)
  have hdisc : ∀ p ∈ Gd, ¬ (p : ℤ) ∣ discr E := fun p hp h => hp.2.1 (hTd p hp.1 h)
  have hmove : ∀ p ∈ Gd, ∀ (u : HeightOneSpectrum (𝓞 E)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 E) ∈ u.asIdeal →
      IsPlaceOver A' u → ∃ s ∈ Ine (F := E) A', s (δ p) ≠ δ p := fun p hp u A' hu hA' =>
    GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia E Ω p hp.1 (hodd p hp) (hdisc p hp) (δ p) (hδ p) u A' hu hA'
  have hnot : ∀ p ∈ Gd, δ p ∉ Set.range (algebraMap E Ω) := by
    rintro p hp ⟨x, hx⟩
    obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
    obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
    obtain ⟨s, -, hs⟩ := hmove p hp u A' hu hA'
    exact hs (by rw [← hx]; exact s.commutes x)
  have hQ : ∀ p ∈ Gd, ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} := fun p hp =>
    exists_qcm_adjoin E Ω p hp.1.pos (δ p) (hδ p) (hnot p hp)
  have hmem : ∀ p ∈ Gd, ∀ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} →
      Q ∈ {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P} := by
    intro p hp Q hQK
    have hδK : δ p ∈ Q.K := by rw [hQK]; exact IntermediateField.mem_adjoin_simple_self E (δ p)
    set y : ↥Q.K := ⟨δ p, hδK⟩ with hy
    have hy2 : y ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hδ p)
    have hsplit : ∀ q ∈ T, ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), (q : 𝓞 ↥Q.K) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w :=
      fun q hq w hw => isSplitAt_of_dvd _ p q y hp.1.pos hy2 (h8 p hp q hq) w hw
    refine ⟨fun A hA s hs => ?_, fun w hw => ?_, ?_, fun P hP => ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic E Ω w₀ A hA q₀ hq₀w (-(p : ℤ)) (δ p)
        (by push_cast; exact hδ p)
        (by push_cast; exact GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q₀ p (h8 p hp q₀ hTq₀)) s hs
    · refine hsplit q₀ hTq₀ w ?_
      rw [← natCast_mem_under (E := E), hw]
      exact hq₀w
    · obtain ⟨w, hw⟩ := exists_mem_of_prime (F := ↥Q.K) hp.1
      refine ⟨w, not_isUnramifiedAt E ↥Q.K p hp.1 (hdisc p hp) y hy2 w hw, ?_⟩
      by_contra hB
      exact hp.2.1 (hTS p hp.1 _ hB ((natCast_mem_under w p).2 hw))
    · refine ⟨⟨y, p, hp.1.pos, by rw [hy2]⟩, even_finrank E Ω Q, fun w hw => ?_⟩
      obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
      have hqT : q ∉ T := fun h => hw (hsplit q h w hqw)
      refine ⟨fun hl => hqT (prime_eq_of_mem w (Fact.out : l.Prime) hq hl hqw ▸ hTl), ?_, ?_⟩
      · refine hN ↥Q.K w fun h => hqT (hTN q hq (dvd_of_mem w hq hqw h))
      · have hB : ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B := by
          by_contra hB
          exact hqT (hTS q hq _ hB ((natCast_mem_under w q).2 hqw))
        obtain ⟨B, hB⟩ := hB
        exact ⟨_, hP.sat w _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow w) hB⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : GlobalTheory.RealGal.QCM E Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 E) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := E) A' ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 E) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds E ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  refine ⟨u, fun hall => ?_, hu⟩
  obtain ⟨s, hs, hne⟩ := hmove p hp u A' hu hA'
  refine hne ((mem_range_res_iff Q.K s).1 (hall A' hA' hs) (δ p) ?_)
  rw [hQK]
  exact IntermediateField.mem_adjoin_simple_self E (δ p)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseAtCompan

theorem mem_reL_symm {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin b → E))
    (x : Fin a → E) : x ∈ reL h.symm L ↔ reV h E x ∈ L := by
  subst h
  show x ∈ reL rfl L ↔ reV rfl E x ∈ L
  rw [reL_rfl, reV_rfl]

theorem mem_mvL_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (co : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (y : Fin N → E) : (co : Matrix (Fin N) (Fin N) E) *ᵥ y ∈ mvL co Λ ↔ y ∈ Λ := by
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : toLE co z = toLE co y := e
    rwa [(toLE co).injective e'] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem smul_mem_of_mem_compan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {R : Ranks} (sp : Spaces R F E) {σ : E →ₐ[F] E} (hσ : (σ : E →+* E) = (sp.cm.sig : E →+* E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (a : 𝓞 E)
    (y : Fin n → E) (hy : y ∈ compan (sp := sp) J a S.Lb) : (T : E) • y ∈ S.Lb := by
  let M : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {y | (T : E) • y ∈ S.Lb}
      add_mem' := fun {x z} hx hz => by
        show (T : E) • (x + z) ∈ S.Lb
        rw [smul_add]; exact add_mem hx hz
      zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        show (T : E) • (c • x) ∈ S.Lb
        rw [smul_comm]; exact S.Lb.smul_mem c hx }
  have hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hσ] at hz
    exact S.Lb_dual z hz
  have hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) := by
    intro x hx
    apply Submodule.subset_span
    have := S.Lb_int x hx
    rwa [hσ] at this
  exact hd (sup_le hL Submodule.smul_le_right hy)

theorem isBaseAt_inv_of_latCo : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  intro D X0 u w hg i hi T bad S co a hT hstd
  have hr := rankN D (i + 1) hi
  set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC
  have h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩
  have hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1)) := by
    rw [← hstd, GlobalTheory.TwU.latCo, h1]
  have hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [← mem_mvL_iff co C y, hm]
    unfold StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]
  have hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb :=
    smul_mem_of_mem_compan D.sp rfl S a
  refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_
  · rw [mem_reL_symm, hCi]
    exact free_re (rankN D (i + 1) hi) co _ x
  · have hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal :=
      natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT
    refine (loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm
    · intro x hx
      rw [mem_reL_symm hr] at hx ⊢
      exact le_sup_left (a := S.Lb) hx
    · intro y hy
      rw [mem_reL_symm hr] at hy ⊢
      rw [map_smul]
      exact hTC _ hy

end GlobalTheory.BaseAtCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) : ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u (n := a) → ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist


open GlobalTheory.ContraPair.SphTwist in
theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := GlobalTheory.ContraPair.SphTwist.conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2 (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerThEntireAlgCoef
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.KerInert.RepComb Formalism.L2.Th1.H

namespace GlobalTheory

theorem kerTh_entire_algCoef : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ), TaylorLogMetric.admitted D a b N N' → SNum S cl → (∀ x, IntOff S (Ξ x)) → Differentiable ℂ (kerTh B χ SS cl N N' Ξ) ∧ TaylorLogMetric.CoefIn D (kerTh B χ SS cl N N' Ξ) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hcc hδ hχ a b SS cl N N' Ξ S hA hS hΞ
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' (laFacts_of_adm B hcc hδ hA)
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hA.2.2.2.1
    hA.2.2.1.2.1 (aaOf_fg cc)
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hS.1 hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hfun : kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [Formalism.L2.KerInert.RepComb.U_eq_opU]
    exact congrFun hΘ z
  rw [hfun]
  refine entire_algCoef_comb D r _ (fun k => (hr k).1) fun k => ?_
  obtain ⟨m, hm, hmt⟩ := ht k
  exact TwV.translate_entire_algebraic D cc δ B χ hcc hδ hχ a b N N' hA (t k) ⟨m, hm.1, lambda_in_lattice_pair cc δ N N' hmt⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem Joint.pt_succ_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  obtain ⟨x0, hx0⟩ := exists_unitary_pt hG ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2)
  have hspec := Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
      (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
        (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (j + 1) La).y = _
    simp only [chAt, dif_pos hj]
  have hre : ∀ {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y := by
    intro R _ m n h y
    subst h
    ext a b
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have key : ∃ x, J.IsPt std (j + 1) hj La x :=
    ⟨⟨_, hspec.2⟩, ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk, by
      rw [hy]
      exact (hre ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm _).symm⟩
  have hpt : J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) := Classical.epsilon_spec key
  refine ⟨hpt, ?_⟩
  obtain ⟨hr, hx⟩ := hpt
  rw [hx, hy, hre]
  exact hspec.1

end GlobalTheory.TwV
end

