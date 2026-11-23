module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinVecMemGLatOne
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LatRatStd

variable {D : D7}

theorem finVec_mem_gLat_one (T : HSp D) (v : Fin T.rank → D.host.E) :
    Formalism.L2.Pj.finVec T v ∈ Formalism.L2.Pj.gLat T 1 ↔ v ∈ L0c D T := by
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.mem_coe]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem mem_latRat_iff_cols {S T : HSp D} (hG : S.gram = 1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)}
    (hS : LS = (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E))) (hT : LT = L0c D T)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ GlobalTheory.LatVac.latRat S T LS LT ↔ ∀ b, (fun a => M a b) ∈ Formalism.L2.Pj.latG T 1 := by
  subst hS hT
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 (SetLike.mem_coe.1 hs)) b trivial)
      obtain ⟨c', hc'⟩ := GlobalTheory.DatumFourier.star_int c
      have h1 : a • t ∈ Formalism.L2.Pj.latG T 1 :=
        Submodule.subset_span ⟨a, ha, t, (finVec_mem_gLat_one T t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ Formalism.L2.Pj.latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        GlobalTheory.LatVac.latRat S T (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E)) (L0c D T) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (finVec_mem_gLat_one T t).1 ht, ?_⟩
        · rw [SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (GlobalTheory.LatVac.latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert GlobalTheory.LatVac.smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

end GlobalTheory.LatRatStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ChiUnit

open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  exact ⟨inv_ne_zero hu0, n, hn2, by rw [inv_inv]; exact hn1⟩

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem unitOff_pow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℕ) : UnitOff N (u ^ k) := by
  induction k with
  | zero => simpa using unitOff_one N
  | succ k ih => rw [pow_succ]; exact unitOff_mul ih hu

theorem unitOff_zpow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℤ) : UnitOff N (u ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact unitOff_pow hu m
  · rw [_root_.zpow_neg, zpow_natCast]; exact unitOff_inv (unitOff_pow hu m)

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitOff_one N
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_pow {N : ℕ} {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : UnitOff N (u ^ k)) : UnitOff N u := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  have hN : IsIntegral ℤ ((N : ℂ) ^ (n * (k - 1))) := by
    have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
    exact this.pow _
  refine ⟨fun h => hu0 (by rw [h, zero_pow hk.ne']), n, ?_, ?_⟩
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * u ^ k) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn1
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u⁻¹) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * (u ^ k)⁻¹) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, inv_pow]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn2

theorem unitOff_of_pow_eq_one (N : ℕ) {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : UnitOff N u :=
  unitOff_of_pow hk (by rw [hu]; exact unitOff_one N)

theorem unitOff_of_mul_eq {N m : ℕ} {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (hab : a * b = (N : ℂ) ^ m) (hN : N ≠ 0) : UnitOff N a := by
  have hNm : (N : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  have ha0 : a ≠ 0 := fun h => hNm (by rw [← hab, h, zero_mul])
  refine ⟨ha0, m, ?_, ?_⟩
  · have : IsIntegral ℤ ((N : ℂ) ^ m) := by
      have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      exact this.pow _
    exact this.mul ha
  · have e : (N : ℂ) ^ m * a⁻¹ = b := by rw [← hab]; field_simp
    rw [e]; exact hb

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem LR {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (n : ℕ) (h : χ ^ n = 1)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (k : Lˣ) : (χ.locK w k) ^ n = 1 := by
  have e : (χ ^ n).locK w k = (χ.locK w k) ^ n := by
    simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  rw [← e, h]
  simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) : χ.locK w k = χ.val w :=
  χ.val_eq hw _ (by
    unfold Formalism.L2.Host.IsUnifAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk, GlobalTheory.TypeValues.intValuation_eq_of_mem h1 h2])

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem finite_ramified_places_hecke_character {D : D7} (χ : Formalism.L2.Host.HChar D.host.E)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬Formalism.L2.Host.OverP D.host (D.host.g k) v) → χ.UnrAt v) :
    {w | ¬ χ.UnrAt w}.Finite := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hc
  refine hw (h w fun k hk => hc ?_)
  unfold Formalism.L2.Host.OverP at hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hk
  · exact Ideal.mul_mem_left _ _ hk

theorem not_mem_of_prime_ne {L : Type} [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∉ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | (apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne ..)

end GlobalTheory.ChiUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsIntegral
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem valuation_le_one_of_mem {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    P.valuation D.host.E a ≤ 1 := by
  by_cases h0 : a = 0
  · simp [h0]
  have h1 := FractionalIdeal.count_mono D.host.E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr h0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr ha)
  rw [hP, ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton D.host.E P h0] at h1
  have hv : P.valuation D.host.E a ≠ 0 := by simpa using h0
  have h2 : WithZero.log (P.valuation D.host.E a) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.log_one]; linarith
  exact (WithZero.log_le_log hv one_ne_zero).1 h2

theorem toEAf_mul_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (f * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨t, ht, H⟩ := GlobalTheory.DetSelfDual.exists_denom Q {a} (by simpa using valuation_le_one_of_mem hQ ha)
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (H a (Finset.mem_singleton_self a))
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D o)
  have e : a = (t : D.host.E)⁻¹ * (o : D.host.E) := by
    have : (o : D.host.E) = (t : D.host.E) * a := by
      rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]
    rw [this, inv_mul_cancel_left₀ ht0']
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (cA D (idem Pg) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine toEAf_mul_mem ht.conj ?_ ha
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem isIntM_mul {m n k : ℕ} {A : Matrix (Fin m) (Fin n) (EAf D)} {B : Matrix (Fin n) (Fin k) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isIntM_smul {m n : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {A : Matrix (Fin m) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hA i j)

theorem frame_col_int {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : Fin n → D.host.E} (hv : v ∈ Λ) :
    IsIntM ((β⁻¹).val * Matrix.of fun i (_ : Fin 1) => eToEAf D (v i)) := fun i _ =>
  (hβ _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL Λ 1 (one_mem _) v hv) i

theorem pair_row_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β Λ) {s : Fin V.rank → D.host.E} (hs : s ∈ Λ) :
    IsIntM ((Matrix.of fun (_ : Fin 1) l => eToEAf D (∑ k, star (s k) * V.gram k l)) * β.val) := fun _ j => by
  have hcol : (fun k => β.val k j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hβ _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k j) i = ((β⁻¹).val * β.val) i j := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine GlobalTheory.PairIntegral.sum_mem_intAf Λ (fun l => ∑ k, star (s k) * V.gram k l) (fun y hy => ?_) _ hcol
  obtain ⟨b, hb⟩ := (hΛ.2 y).1 hy s hs
  refine ⟨b, ?_⟩
  rw [show algebraMap (𝓞 D.host.E) D.host.E b = (b : D.host.E) from rfl, hb]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem gram_inv_star (S : HSp D) (s : Fin S.rank → D.host.E) (e : Fin S.rank) :
    ∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b) = s e := by
  have : ∀ b, star (∑ k, star (s k) * S.gram k b) = (S.gram *ᵥ s) b := by
    intro b
    simp [star_sum, GlobalTheory.LatVac.gram_star, Matrix.mulVec, dotProduct, mul_comm]
  simp_rw [this]
  change (S.gram⁻¹ *ᵥ (S.gram *ᵥ s)) e = _
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.one_mulVec]

theorem map_gen (α : Af D.host.F) (c : AE D) (a : D.host.E) (S T : HSp D) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ((c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t) : WO S T).map (toEAf D)) =
      (toEAf D (c * incA D a) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D)) •
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)) *
          Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
    GlobalTheory.LatVac.finTens, GlobalTheory.LatVac.genMap, map_mul]
  change toEAf D c * ((a * t i * ∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] α) =
    toEAf D c * (a ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) *
      ((t i ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem adj_shape {m n : ℕ} (c : EAf D) (C : Matrix (Fin m) (Fin 1) (EAf D)) (R : Matrix (Fin 1) (Fin n) (EAf D)) :
    ((c • (C * R)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      GlobalTheory.AdelicLatMove.cF D c • ((R.map (GlobalTheory.AdelicLatMove.cF D))ᵀ * (C.map (GlobalTheory.AdelicLatMove.cF D))ᵀ) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [map_mul, mul_comm]

theorem cF_eToEAf (x : D.host.E) : GlobalTheory.AdelicLatMove.cF D (eToEAf D x) = eToEAf D (star x) := rfl

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem frMapAdj_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_neg x

theorem frMapAdj_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapO S T βS βT (-x) = -frMapO S T βS βT x :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_neg x

theorem frMapO_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapO S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_zero

end GlobalTheory.ConjHalfInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this


end GlobalTheory.StdAtPrime
end

