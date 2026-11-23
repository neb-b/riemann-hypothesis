module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerPosOfInnerNe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem innerPos_of_innerNe {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : InnerNe R i t S) : InnerPos R i t S := by
  unfold InnerPos
  intro th hth c
  have h' := h th hth c
  obtain ⟨l, hl, hx⟩ := h'
  have key := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).2 (part R i S c) l hl hx
  obtain ⟨l', hl', hx', -⟩ := key
  exact ⟨l', hl', hx'⟩

theorem rawLift_main : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D →
    ThOnto R ∧ ∀ i t, UpInj R i t ∧ InnerPos R i t ∅ ∧ PartsSpan R i ∅ := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF hR
  have lp : ∀ i, LevProd R i := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF
  have tr : ∀ i, TransLaws R i := GlobalTheory.RawLiftTrans.transLaws hC D G Pl0 T A Ks R F hL hF
  have lf : ∀ i t, LevFix R i t := GlobalTheory.RawLift.LevelFix.levFix D G Pl0 T A Ks R F hL hF
  have vn : ∀ i t, VecNe R i t := vecNe D G Pl0 T A Ks R F hL hF
  have fs : ∀ i t, FinSum R i t := fun i t =>
    GlobalTheory.RawLift.finSum_of_rallis hC D G Pl0 T A Ks R F hL hF hR i t (_root_.GlobalTheory.AdjUp.adjFormula_holds hC D G Pl0 T A Ks R F hL hF i t) (lf i t)
      (GlobalTheory.RawLift.FactorInf.factInf D G Pl0 T A Ks R F hL hF i t) (GlobalTheory.RawLift.RealLowPf.realLow D G Pl0 T A Ks R F hL hF i t) (vn i t) (lp i) (tr i)
  have fm : ∀ i t, FinMult R i t := GlobalTheory.RawLift.LocalFactor.finMult D G Pl0 T A Ks R F hL hF
  have bs : ∀ i t, BadSupp R i t := _root_.GlobalTheory.BadSuppPf.badSupp D G Pl0 T A Ks R F hL hF
  have ls : ∀ i t, LocSmall R i t := fun i t =>
    GlobalTheory.RawLift.Small.locSmall D G Pl0 T A Ks R F hL hF i t (bs i t) (GlobalTheory.RawLift.GoodModulus.goodMod D G Pl0 T A Ks R F hL hF i t)
      (GlobalTheory.IndexCount.indexSum_holds D G Pl0 T A Ks R F hL hF i)
  have up : ∀ i t, UpInj R i t := fun i t =>
    GlobalTheory.UpInj.upInj_holds D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (lp i) (tr i)
  refine ⟨GlobalTheory.rawLift_onto_of_upInj D G Pl0 T A Ks R F hL hF (GlobalTheory.RatSpanProof.ratSpan_of_laws D G Pl0 T A Ks R F hL hF) (fun i => up i A.μ0),
    fun i t => ⟨up i t, ?_, GlobalTheory.PartsSpanProof.partsSpan hC D G Pl0 T A Ks R F hL hF i ∅⟩⟩
  exact innerPos_of_innerNe R i t ∅
    (GlobalTheory.RawLift.innerNe_spherical D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (bs i t) (lp i) (tr i))

end GlobalTheory.RawLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelChoiceMuUnramifiedOutsideTypePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlaceUnram

open GlobalTheory.IdemSupport GlobalTheory.LevelPlaces GlobalTheory.SplitOffPlaces

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem unramOutside_mu0_of_splitSet : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → SplitSet L.Pg → ∀ j : Fin D.R.m, UnramOutside (L.mu0 ((j : ℕ) + 1)) L.Pg := by
  intro D T0 L μ0 hL hS j x hinf h1 h2 hx
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hk : ∀ PP ∈ L.Pg, idemAt PP * idem L.Pg = idemAt PP := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hS.isIdemAt ha).1) (fun a ha b hb hab => hS.mul_eq_zero ha hb hab) hl
  have hc0 : ∀ PP ∈ L.Pg, idemAt PP * cA D (idem L.Pg) = 0 := fun PP hPP => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => hS.mul_conj hPP hi
  have hc1 : ∀ PP ∈ L.Pg, cA D (idemAt PP) * idem L.Pg = 0 := fun PP hPP => by
    rw [idem, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact hS.mul_conj hi hPP
  have hx1 : ∀ PP ∈ L.Pg, Φ (x : AE D) PP = 1 ∧ Φ (x : AE D) (cP PP) = 1 := fun PP hPP => by
    have hd := delta_of_isIdemAt hΦ (hS.isIdemAt hPP)
    have hd' := delta_conj hΦ hd
    have a : idemAt PP * (x : AE D) = idemAt PP := by
      have e : idemAt PP * (idem L.Pg + cA D (idem L.Pg)) = idemAt PP := by rw [mul_add, hk PP hPP, hc0 PP hPP, add_zero]
      calc idemAt PP * (x : AE D) = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = idemAt PP := e
    have b : cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) := by
      have e : cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) = cA D (idemAt PP) := by
        rw [mul_add, hc1 PP hPP, zero_add, ← map_mul, hk PP hPP]
      calc cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = cA D (idemAt PP) := e
    constructor
    · have h := congrArg (fun z => Φ z PP) a
      rwa [ev_mul, hd.2.1, one_mul] at h
    · have h := congrArg (fun z => Φ z (cP PP)) b
      rwa [ev_mul, hd'.2.1, one_mul] at h
  have hg : ∀ k, (D.host.g k : D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  set m : ℕ := D.host.g 0 * D.host.g 1 with hmdef
  have hm0 : (m : D.host.E) ≠ 0 := by rw [hmdef, Nat.cast_mul]; exact mul_ne_zero (hg 0) (hg 1)
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → (L.C.mu0 j).UnrAt P :=
    fun P hP => (L.C.isMu0 j).unr P fun k hk => hP (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
      rw [hmdef, Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk'
      · exact Ideal.mul_mem_left _ _ hk')
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ (L.C.mu0 j) (hL.mu0 j) (L.C.isMu0 j).tame m hunr x ⟨hinf, h1, h2⟩
    ⟨finPart D (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · have e : Φ (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)) Q =
        (Φ (x : AE D) Q - 1) * algebraMap D.host.E (Q.adicCompletion D.host.E) ((m : D.host.E)⁻¹) := by
      rw [ev_mul, hΦ.inc, map_sub, map_one]
      rfl
    rw [e]
    by_cases hQ : (m : 𝓞 D.host.E) ∈ Q.asIdeal
    · have hq : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
        rw [hmdef, Nat.cast_mul] at hQ
        rcases Q.isPrime.mem_or_mem hQ with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨k, hk⟩ := hq
      have h1Q : Φ (x : AE D) Q = 1 := by
        rcases div_or_div_conj L.C.P k Q hk with h | h
        · exact (hx1 Q ((hL.Pg Q).2 ⟨k, h⟩)).1
        · have e2 : conjSpec Q = cP Q := (isConjPl_iff _ _).1 (isConjPl_conjSpec Q)
          rw [e2] at h
          have := (hx1 (cP Q) ((hL.Pg _).2 ⟨k, h⟩)).2
          rwa [cP_cP] at this
      rw [h1Q, sub_self, zero_mul]
      exact zero_mem _
    · refine mul_mem (sub_mem ((hΦ.int _).1 h1 Q) (one_mem _)) ?_
      have hm' : (m : 𝓞 D.host.E) ≠ 0 := fun h => hm0 (by exact_mod_cast congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h)
      have := (inv_mem_iff Q hm').2 hQ
      simpa using this
  · rw [nsmul_eq_mul, ← map_natCast (finPart D) m, ← map_mul, ← map_natCast (incA D) m, ← mul_assoc, mul_comm _ ((x : AE D) - 1),
      mul_assoc, ← map_mul, mul_inv_cancel₀ hm0, map_one, mul_one, map_sub, map_one]

end GlobalTheory.TypePlaceUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRankinSelberg_logarithm_formula : (∀ (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ), 1 < q → (∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ) * (β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) → ∃ L : ℂ, HasSum (fun r : ℕ => (A.map fun α => (α : ℂ) ^ (r + 1)).sum * (B.map fun β => (β : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r : ℂ) + 1) * s)) / ((r : ℂ) + 1)) L ∧ locL q A B s = Complex.exp L) ∧ (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)‖) ∧ HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)))) := by
  first | (exact @GlobalTheory.JSLog.logRankinSelberg) | (exact GlobalTheory.JSLog.logRankinSelberg) | (intros; apply GlobalTheory.JSLog.logRankinSelberg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCuspStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a → σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w, ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  first
  | exact @GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | exact GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | (intros; apply GlobalTheory.RSStrict.norm_sq_lt_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add (f := _), map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add (f := _), map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add (f := _), map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
end

