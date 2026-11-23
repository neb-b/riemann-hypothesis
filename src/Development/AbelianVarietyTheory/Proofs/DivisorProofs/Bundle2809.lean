module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulCoeffIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrime
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompareOff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Formalism.HermitianLatticesTheory (localization₂)

theorem mem_localization_iff {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L : Submodule Rr W) (x : W) : x ∈ localization₂ p L ↔ ∃ s : Rr, s ∉ p ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem localization_le_of_le_localization' {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L M : Submodule Rr W) (h : L ≤ localization₂ p M) : localization₂ p L ≤ localization₂ p M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, hy⟩ := (mem_localization_iff p M _).1 (h hx)
  refine (mem_localization_iff p M x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hne : Formalism.EigenvalueLevelCeiling.plc lam ≠ p) : ((p : 𝓞 K)) ∉ lam.asIdeal := by
  intro hm
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have h0 : ((p : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ p := ringChar.dvd h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne h1

theorem splitOffBad_of_mul {D : D7} {V : HSp D} {a b : ℕ} {h : GA D V} (H : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hPP hm => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem singleSeries_transl (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ} (hK : KerDat R i ξ χ ξR Q ω φ)
    {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω (c • ω (k, 1) φ) h w v = c • singleSeries R i ω φ (h * k) w v := by
  funext g
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  simp only [singleSeries, Datum.thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ k hk 1
    (one_mem _) _ _ _ _ φ _ hth, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compareOffOwn_run : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  intro lam hlam
  refine localization_le_of_le_localization' _ _ _ (Submodule.span_le.2 ?_)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, s, f', Λ, h, N, x₀, P, x, hs, hsf, hSplit, hLat, hΛlam, hUni, hTriv, hTrivM, hLevN, hAdm, hP, hx⟩ :=
    GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins ℓ U lam f hf
  obtain ⟨y, s', hy, hs', hyLat⟩ := GlobalTheory.HarmInCoef.harm_mem_coefLat D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins Λ h (splitOffBad_of_mul hSplit) hLat lam hΛlam P hP
  obtain ⟨ω, φ, hBase⟩ := GlobalTheory.OnCmp.exists_baseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu
  obtain ⟨χ, ξR, hKer⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu ω φ hBase
  have hEx := GlobalTheory.OneMapExact.trace_short_eq D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu
    hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  obtain ⟨y₀, c, hy₀, hcInt, hSer⟩ :=
    hEx χ ξR ω φ hKer Λ h hSplit hLat N x₀ P x f' y hUni hTriv hTrivM hLevN hAdm hP hx hy
  obtain ⟨φ', hVec, k, hk, c', m, hφ', hpc, -, hc'0, hLatk⟩ := _root_.GlobalTheory.FreeBlockMove.vecFree_translate D G Pl0 T0 A T.J.Q.c.F R F hC i _ χ ξR _ ω φ hKer
    (ownAt D v) (fun PP hPP => by classical exact (Finset.mem_filter.1 hPP).2) hξ hVal y₀ hy₀
  obtain ⟨s'', hs'', hs''c⟩ := hcInt lam hΛlam
  obtain ⟨g', hg'⟩ : ∃ g', g' = ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f' u) := ⟨_, rfl⟩
  rw [← hg'] at hSer
  have hp : (ownAt D v).Prime := by
    rcases hFO.own with e | e <;> rw [e]
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hpl : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := natCast_not_mem lam hp hlam
  have hA : ((s : ℕ) : D.what₂.LL) • (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
      algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • g' := by
    classical
    have e1 : ∀ u, ((s : ℕ) : D.what₂.LL) • cuspTo hT.p fw i (f u) =
        algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • cuspTo hT.p fw i (f' u) := by
      intro u
      have e2 : ((s : ℕ) : T.J.Q.c.F) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f u) =
          (show T.J.Q.c.F from (a : T.Q.c.F)) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f' u) :=
        Subtype.ext (hsf u)
      have e3 := congrArg (cutTo fw i) e2
      rw [map_smul, map_smul] at e3
      rw [← algebraMap_smul D.what₂.LL ((s : ℕ) : T.J.Q.c.F), ← algebraMap_smul D.what₂.LL (show T.J.Q.c.F from (a : T.Q.c.F)),
        map_natCast] at e3
      exact e3
    rw [hg', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_comm, e1 u, smul_comm]
  have hdet : ∀ x : Fin (R.nW i) → D.what₂.LL,
      (∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => w ρ) = 0) → x = 0 := by
    intro x hx
    have h4 : (R.FW i).j (sg0 D A) x = 0 := by
      obtain ⟨u, hu, -⟩ := hIo i
      exact GlobalTheory.TraceIncl.eq_of_low (R := R) (i := i) hC.models.HW ⟨u, hu⟩
        (x := (R.FW i).j (sg0 D A) x) (y := 0) fun w => by rw [map_zero]; exact hx w
    by_contra hne
    exact ((hLU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 h4
  by_cases hc : c = 0
  · have hz : g' = 0 := hdet g' fun w => by rw [hSer φ' hVec w, hc, map_zero, zero_smul]
    refine (mem_localization_iff _ _ _).2 ⟨(s : 𝓞 D.what₂.LL), hs, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.what₂.LL, hA, hz, smul_zero]
    exact zero_mem _
  · have hs'n : s' ≠ 0 := by
      rintro rfl
      exact hs' (by simp)
    have hs'0 : (s' : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hs'n
    have hp0 : ((ownAt D v : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hc0 : c ≠ 0 := hc
    have hce : D.what₂.embLL c ≠ 0 := (map_ne_zero _).2 hc
    have hce' : D.what₂.embLL c' ≠ 0 := (map_ne_zero _).2 hc'0
    obtain ⟨e, he⟩ : ∃ e, e = (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (c * c')⁻¹) • g' := ⟨_, rfl⟩
    have hmem : e ∈ thetaBase R i U ψ 1 v (ownAt D v) := by
      refine Submodule.subset_span ⟨ω, φ, hKer.isKernel, h * k, mul_mem hSplit.1 hk,
        ((ownAt D v : ℂ)) ^ m • ((s' : ℂ) • (O i).c0' y), hLatk h hSplit.1 _ hyLat, fun w => ?_⟩
      rw [he, adForm_smul, MultilinearMap.smul_apply, hSer φ' hVec w, hφ', singleSeries_transl R i hKer hk,
        singleSeries_smul, singleSeries_smul, map_smul, map_smul, map_smul, one_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
    have hgg : g' = (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹) • e := by
      rw [he, smul_smul]
      conv_lhs => rw [← one_smul D.what₂.LL g']
      congr 1
      field_simp
    have hint : IsIntegral ℤ (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) *
        (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')) :=
      ((RingOfIntegers.isIntegral_coe a).algebraMap.mul hs''c).mul hpc
    have hpr := lam.isPrime
    have ht : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal := by
      simp only [Ideal.IsPrime.mul_mem_iff_mem_or_mem hpr, not_or]
      exact ⟨⟨⟨⟨fun h1 => hpl (hpr.mem_of_pow_mem _ h1), fun h1 => hpl (hpr.mem_of_pow_mem _ h1)⟩, hs'⟩, hs''⟩, hs⟩
    refine (mem_localization_iff _ _ _).2 ⟨_, ht, ?_⟩
    have key : (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) •
        (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
        (⟨_, hint⟩ : 𝓞 D.what₂.LL) • e := by
      rw [← algebraMap_smul D.what₂.LL, ← algebraMap_smul D.what₂.LL (⟨_, hint⟩ : 𝓞 D.what₂.LL)]
      have et : algebraMap (𝓞 D.what₂.LL) D.what₂.LL
          (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) =
          ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
            (s : D.what₂.LL) := by
        simp
      have hsc : ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
          (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹)) =
          algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c') := by
        field_simp
      rw [et, mul_smul, hA, hgg, smul_smul, smul_smul]
      congr 1
      show _ = algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')
      rw [← hsc]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory.CompareOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripleWeilTransfer

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (ε : Bool) {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ algF ψ θ ε A B) : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem eq_on_theta {ψ : AddChar (AF D.host.F) ℂ} (ε : Bool) {M X : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω ω' : GlobalTheory.Grid.WRep M X} (h : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) (h' : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω')
    (p : GA D M × GA D X) (f : WO M X → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f) : ω p f = ω' p f := by
  have e := GlobalTheory.WeilUniq.weilDatum_unique D ψ h.std _ X χ χ' _ _ h h' ((GlobalTheory.Grid.ofSgn ε M).symm p.1, p.2) f hf
  simpa [GlobalTheory.Grid.WRep.toSgn] using e

theorem isCoinvMap_congr {θ : InfFam D} {M X : HSp D} {ω ω' : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)}
    {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
    {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO M X → ℂ) →ₗ[ℂ] Pi}
    (he : ∀ q, ∀ Φ ∈ S, ω q Φ = ω' q Φ) (h : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω S Pi rf rl p) : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω' S Pi rf rl p := by
  obtain ⟨⟨sM1, sM2⟩, ⟨sX1, sX2⟩, onto, invf, invl, eqf, eql⟩ := h
  refine ⟨⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, onto,
    fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_, fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_⟩
  · rw [← he _ Φ hΦ]; exact sM1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sM2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact sX1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sX2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact invf g hg Φ hΦ
  · exact invl τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)
  · rw [← he _ Φ hΦ]; exact eqf g hg Φ hΦ
  · exact eql τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)

end GlobalTheory.TripleWeilTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorIdent

theorem squareGroup_hom_ext_projections {S : Scheme.{0}} (H : Over S) {X : Scheme.{0}} (a b : X ⟶ (G2 H).left)
    (h1 : a ≫ (fst H H).left = b ≫ (fst H H).left) (h2 : a ≫ (snd H H).left = b ≫ (snd H H).left) : a = b :=
  pullback.hom_ext h1 h2

theorem samePol_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → ∀ (A₉ : PolAV (Sp (FractionRing R₉))) (D₉' : DegData R₉ (maximalIdeal R₉)) (U₉ : Unif (maximalIdeal R₉) D₉' A₉ G₉), U₉.LG = P₉.L → ∃ D₉ : DegData R₉ (maximalIdeal R₉), Nonempty (IsPullDeg ρ₉ D.toPre D₉.toPre) ∧ SamePol D₉.toPre D₉'.toPre := by
  intro R _ _ _ hB D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉
    hfin hpb₉ hsq₉ hsa₉ hlam₉ A₉ D₉' U₉ hLG
  obtain ⟨hadm, hinj, hfinite⟩ := hfin
  haveI : CharZero R := hB.2
  have hloc : IsLocalHom ρ₉ := RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hfinite) hinj
  have hB₉ : Base R₉ := ⟨hadm, charZero_of_injective_ringHom hinj⟩
  obtain ⟨D₁, D₁', F₁, A₁', G₁', _, _, U₁', oA₁, oG₁, G₁, _, _, β, β₂, inc₁, pr₁, hpd, hsa₁', hlin₁, hsa₁, hinc₁, hpr₁,
      hip₁, hpi₁, hpb₁, hsq₁, hlb₁⟩ :=
    _root_.GlobalTheory.FactorPull.factor_baseChange R hB.1 D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ hadm hinj hloc
  obtain ⟨e, he, hβ⟩ := grpPullback_iso hpb₉ hpb₁
  have hei : IsMonHom e.inv := inferInstance
  let m : G2 G₉ ⟶ G2 G₁ := lift (fst G₉ G₉ ≫ e.hom) (snd G₉ G₉ ≫ e.hom)
  have hm : β₉₂ = m.left ≫ β₂ := by
    apply squareGroup_hom_ext_projections G
    · rw [hsq₉.1, Category.assoc, hsq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, hβ]
    · rw [hsq₉.2, Category.assoc, hsq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hβ]
  have hℓ : (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left =
      m.left ≫ (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left := by
    rw [← Over.comp_left]
    congr 1
    simp [m]
  have hL' : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hL₁ : (abelian₂ G₁' U₁'.LG.L).IsLB := LB.isLB_linComb U₁'.LG.isLB _ _
  have h1 : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G' U'.LG.L).pull
      (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
    rw [hLG]; exact hlam₉
  have h2 := GlobalTheory.GenSpread.lbIso_pull_pull hL'
    (a := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ rfl
  have h3 := GlobalTheory.GenSpread.lbIso_pull_comp m.left hℓ hm hlb₁
  have hLam : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G₁' U₁'.LG.L).pull
      (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left) :=
    LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB (pull_isLB hL' _) _) (pull_isLB hL₁ _)
      (LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h1 h2)
      (LBIso.symm h3)
  have hsame : SamePol D₁.toPre D₉'.toPre :=
    _root_.GlobalTheory.Mum.FactorPol.samePol_of_unif_factor R₉ hB₉ D₁ D₁' F₁ A₁' G₁' hsa₁' U₁' oA₁ oG₁ hlin₁ G₉ hsa₉ (e.hom ≫ inc₁) (pr₁ ≫ e.inv)
      inferInstance inferInstance
      (by rw [Category.assoc, ← Category.assoc inc₁, hip₁, Category.id_comp, Iso.hom_inv_id])
      (by rw [Category.assoc, ← Category.assoc e.inv, Iso.inv_hom_id, Category.id_comp, hpi₁]) D₉' A₉ U₉ hLam
  exact ⟨D₁, hpd, hsame⟩

end GlobalTheory.Mum.FactorIdent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolGeOfHilbertSamuel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.VolBr

theorem volGe_of_hilbertSamuel :
    GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.VolGe := by
  intro hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI
  obtain ⟨P, b, s, t, hPL, hG⟩ := _root_.GlobalTheory.VolBr.exists_good_pair hAC k X p D hX L
  subst hPL
  obtain ⟨α, hα, hαlim⟩ := _root_.GlobalTheory.SelfInterGrowth.main hAC k X p D hX P.L P.A a hSI
  obtain ⟨hRL, hRA, -⟩ := _root_.GlobalTheory.VolBr.Pair.rep_base k X p P
  apply _root_.GlobalTheory.VolBr.le_arVol_of_frequently_le k X p D P.L a
  intro ε hε
  have hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hε3 : 0 < ε / 3 := by positivity
  have hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1) :=
    hαlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hnα, hcont⟩ := ((eventually_ge_atTop 1).and
    (hlim.and (_root_.GlobalTheory.VolBr.lc_add_A_le hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists
  have hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L n hRL
    have h2 := _root_.GlobalTheory.VolBr.Pair.rep_tens k X p P _ _ 0 1 _ P.A h1 hRA
    simpa using h2
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.VolBr.exists_isNef_shift_pow_tens hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef
  have hstep := _root_.GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨m, hm, hm1, hm2⟩ := ((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists
  have hmN : N₀ ≤ m := le_of_max_le_left hm
  refine ⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩
  have hsm := (_root_.GlobalTheory.VolBr.SmallBall.main k X p P 1 0 P.L hRL 0 (n * m)).2.1
  rw [mul_one, mul_zero] at hsm
  have hfin := _root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC
  have hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard := by
    rw [Set.ncard_def, Set.ncard_def, hsm]
  refine ⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩
  rw [hnc]
  change _ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1
  have hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mul_one] at hm1
  set F : ℝ := ((D + 1).factorial : ℝ)
  set x : ℝ := (n : ℝ) ^ (D + 1) with hx
  set y : ℝ := (m : ℝ) ^ (D + 1) with hy
  have hx1 : 1 ≤ x := one_le_pow₀ (by exact_mod_cast hn1)
  have hy0 : 0 ≤ y := by positivity
  have hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y := by push_cast; rw [mul_pow]
  rw [mul_pow] at hm2
  rw [hN]
  have hαx : (a - ε / 3) * x ≤ α n := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα
    linarith
  have hF0 : 0 < F := by linarith
  have e1 : (a - ε / 3) * x * y / F ≤ α n / F * y := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le
  have e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y) :=
    div_le_self (by positivity) hF1
  have e3 : ε / 3 * y ≤ ε / 3 * (x * y) := by
    have : y ≤ x * y := le_mul_of_one_le_left hy0 hx1
    exact mul_le_mul_of_nonneg_left this hε3.le
  have e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y) := by
    field_simp
    ring
  linarith [e1, e2, e3, e4, hm1, hm2]

end GlobalTheory.VolBr
end
end

