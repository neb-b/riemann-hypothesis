module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhIUnionTrans
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinf
section
noncomputable section

namespace GlobalTheory.ExpImage.Tail

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}

abbrev Fr (l : ℕ) [Fact l.Prime] (n : ℕ) : Ainf l →+* Ainf l :=
  (WittVector.frobenius : Ainf l →+* Ainf l) ^ n

theorem Fr_succ (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = WittVector.frobenius (Fr l n a) := by
  rw [Fr, pow_succ']; rfl

theorem Fr_succ' (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = Fr l n (WittVector.frobenius a) := by
  rw [Fr, pow_succ]; rfl

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem Fr_teich (n : ℕ) (x : OCb l) :
    Fr l n (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ n := by
  induction n with
  | zero => simp [Fr]
  | succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']

theorem lifts_Fr {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (n : ℕ) :
    Lifts AI K (Fr l n w) ((frK P K ^ n) c) := by
  induction n with
  | zero => simpa [Fr] using h
  | succ n ih =>
    rw [Fr_succ, pow_succ']
    exact ih.frob

theorem lifts_sum {ι : Type} (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K))
    (h : ∀ i ∈ T, Lifts AI K (w i) (c i)) : Lifts AI K (∑ i ∈ T, w i) (∑ i ∈ T, c i) := by
  unfold Lifts at h ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  exact Finset.sum_congr rfl h

def oK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →+* P.R.BdR :=
  (oB P).comp (algebraMap ↥(K0 K) (Om l))

theorem oK_apply (c : ↥(K0 K)) : oK P K c = oB P (c : Om l) := rfl

def u (P : LocPrime l) (j : ℕ) : P.R.BdR := qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j

theorem u_mem (j : ℕ) : u P j ∈ FilB P 0 := by
  refine qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))
  simp

theorem taylor0 (hT : LocTied l P AI) (m M : ℕ) :
    io AI (WittVector.teichmuller l AI.ε ^ m) - ∑ j ∈ Finset.range M, (m : P.R.BdR) ^ j * u P j ∈
      FilB P (M : ℤ) := by
  have h := _root_.GlobalTheory.ExpImage.epsT_pow_taylor l P AI hT 0 m M
  rw [P.ζQ_zero, one_pow, map_one, one_mul] at h
  convert h using 3 with j hj
  · rfl
  · rw [pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]

theorem span_mem_Lat {M n : ℕ} {a : Ainf l}
    (ha : a ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI a ∈ Lat AI M n := by
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
  refine ⟨x, ?_⟩
  have h := FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)
  rw [mul_one] at h
  convert h using 1
  simp only [map_add (f := _), map_mul, map_pow]
  ring

theorem tail (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ)
    (d : ℕ → ↥(K0 K)) (hM : 1 ≤ M) (hw : ∀ i ∈ T, Lifts AI K (w i) (c i))
    (hd : ∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧
      d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) :
    ∃ y : Ainf l, y - WittVector.frobenius y =
        ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧
      io AI y - ∑ j ∈ Finset.range M,
        qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨D, hD⟩ := _root_.GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI hT K (d j) (hd j hj).1
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using hD
  have h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i := by
    have h1 := (hD 0 hM).sub (hD 0 hM).frob
    have h2 := (hd 0 hM).2
    simp only [pow_zero, one_mul, mul_one] at h2
    rw [h2] at h1
    exact h1.unique (lifts_sum T w c hw)
  obtain ⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    have := sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)
    rwa [one_pow] at this
  obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.ExpImage.Conv.main l P AI
  obtain ⟨y', hy'⟩ := hc1 q
  have hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') =
      ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq
    rw [map_add (f := _)]
    linear_combination h0 + hy' - hq
  refine ⟨D 0 + AI.μ * y', hy, ?_⟩
  set y := D 0 + AI.μ * y' with hydef
  let E : ℕ → P.R.BdR := fun n => io AI (Fr l n y) -
    ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j
  have hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ) := by
    intro n
    have h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
          io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul,
        mul_comm (l ^ n), oK_apply]
    have h2 : ∀ j ∈ Finset.range M,
        (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j -
          (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      intro j hj
      have h3 := congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3
      have h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j)) := by
        rw [pow_succ]; rfl
      have h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)
          = (l : P.R.BdR) ^ (j * n) * u P j *
            ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h4, h5, ← h3]
      ring
    have h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
        (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) -
          ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      simp only [E]
      ring
    rw [h6]
    refine Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)
    rw [oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]
    exact io_mem AI _
  have htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (hstep n)
      rwa [sub_add_sub_cancel] at this
  have hE0 : E 0 ∈ FilB P (M : ℤ) := by
    refine GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_
    obtain ⟨k₀, hk₀⟩ := hc2 M r
    have hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r := fun j =>
      (_root_.GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat l P AI hT _ (u_mem j) M r).1
    choose k hk using hk
    set n := k₀ + ∑ j ∈ Finset.range M, k j with hn
    have hEn : E n ∈ Lat AI M r := by
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      have e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0)) := by
        rw [oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]
      have e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M',
          (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1) := by
        simp only [E, hydef]
        rw [Finset.sum_range_succ', e0]
        simp only [map_add (f := _), map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one,
          inv_one, map_one]
        ring
      rw [e1]
      refine sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)
      · have := hk₀ n (Nat.le_add_right _ _)
        rwa [← RingHom.coe_pow] at this
      · have hj' : j + 1 < M' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hle : k (j + 1) ≤ (j + 1) * n := by
          have a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j :=
            Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')
          have a2 : n ≤ (j + 1) * n := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
          omega
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        have := io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))
        convert this using 1
        rw [he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]
        ring
    have := add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn
    rwa [sub_add_cancel] at this
  convert hE0 using 1
  simp only [E, Fr, pow_zero, mul_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u, oK_apply, AlgHom.one_apply]
  ring

end GlobalTheory.ExpImage.Tail
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalTwoCocycleMultipleNotCoboundaryStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  first | exact @GlobalTheory.TateNat.free_inj | exact GlobalTheory.TateNat.free_inj | (intros; apply GlobalTheory.TateNat.free_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.RedAct

theorem ringHom_padicInt_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k)
    (z : ℤ_[l]) : f z = ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) z := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.zmodRepr : ℤ_[l]) + l * c := by rw [← hc]; ring
  rw [hz]
  simp only [map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem map_act {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l]
    (f : O →+* k) (c : ℤ_[l]) (a : O⟦X⟧) :
    PowerSeries.map f (GlobalTheory.CycFr.act O c a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l c (PowerSeries.map f a) := by
  have hb : PowerSeries.map f (GlobalTheory.CycFr.bin O c) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l c := by
    ext n
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
    exact ringHom_padicInt_eq (f.comp (algebraMap ℤ_[l] O)) _
  rw [GlobalTheory.CycFr.act_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, ← hb]
  have h := PowerSeries.map_subst (GlobalTheory.CycFr.hasSubst_bin O c) (h := f) a
  have h2 : PowerSeries.map f (GlobalTheory.CycFr.bin O c - 1) = PowerSeries.map f (GlobalTheory.CycFr.bin O c) - 1 := by
    rw [map_sub, map_one]
  rw [← h2]
  exact h

theorem deltaPi_one_add {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (b : k⟦X⟧) :
    GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (1 + l) b = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l b := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) (1 + l)
  rw [Nat.cast_add, Nat.cast_one] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, h]
  simp

theorem chi_surjective {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) :
    Function.Surjective χ := by
  intro u
  obtain ⟨χ', h1, -, h3⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨g, hg, hgu⟩ := h3 K 0 (le_trans (le_inf le_rfl hK) le_sup_left) u (by simp)
  refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (GlobalTheory.algebraMap_padicInt_OL_injective LL ?_)⟩
  rw [hχ]
  apply Subtype.ext
  have h := W.χΓ_res ⟨g, hg⟩
  rw [P.PD_χ, ← h1] at h
  refine h.trans ?_
  change algebraMap ℚ_[l] ↥LL.1 ((χ' g : ℤ_[l]) : ℚ_[l]) = _
  rw [hgu]
  rfl

theorem card_torsion {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) (h : K.1 ≤ Ks K 1) :
    W.DelF.card = l - 1 := by
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h
  rw [p1, mul_one] at hc
  exact hc

theorem gamma_eq_act {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : W.Gam) :
    W.γ₀ g = GlobalTheory.CycFr.act ↥(OL LL) (χ g : ℤ_[l]) :=
  GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ hχ g

theorem action_of_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (hs : Function.Surjective χ)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.CycFr.act O (χ g : ℤ_[l])) (hc : W.DelF.card = l - 1)
    {k : Type} [Field k] [CharP k l] (r : O →+* k) :
    (∃ γ : W.Gam, (W.χΓ γ : O) = 1 + (l : O) ∧
      ∀ a, PowerSeries.map r (W.γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map r a)) ∧
    ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
      PowerSeries.map r (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map r a) := by
  have h2l := (Fact.out : l.Prime).two_le
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hcard : Nat.card (CommGroup.torsion W.Gam) = l - 1 := by
    rw [← hc, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [CommGroup.mem_torsion, Finset.mem_coe, GlobalTheory.WachTie.mem_DelF_iff]
  have hpow : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := fun δ hδ => by
    have h1 : (⟨δ, (GlobalTheory.WachTie.mem_DelF_iff W δ).1 hδ⟩ : CommGroup.torsion W.Gam) ^ (l - 1) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  constructor
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
      rw [sub_neg_eq_add, IsUnit.neg_iff] at h1
      exact h1.resolve_left PadicInt.p_nonunit
    obtain ⟨g, hg⟩ := hs hu.unit
    have hg' : (χ g : ℤ_[l]) = 1 + l := by rw [hg, hu.unit_spec]
    refine ⟨g, by rw [← hχ, hg', map_add (f := _), map_one, map_natCast], fun a => ?_⟩
    rw [hγ, map_act, hg', deltaPi_one_add]
  · let f : {δ // δ ∈ W.DelF} → {z : ℤ_[l] // z ^ (l - 1) = 1} := fun δ =>
      ⟨χ δ.1, by rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow δ.1 δ.2, map_one, Units.val_one]⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Subtype.ext (hχi (Units.ext (congrArg Subtype.val hab))), fun z => ?_⟩
      have hu : IsUnit z.1 := IsUnit.of_pow_eq_one z.2 (by omega)
      obtain ⟨g, hg⟩ := hs hu.unit
      have hg' : (χ g : ℤ_[l]) = z.1 := by rw [hg, hu.unit_spec]
      refine ⟨⟨g, (W.DelF_def g).2 ⟨l - 1, by omega, hχi (Units.ext ?_)⟩⟩, Subtype.ext hg'⟩
      rw [map_pow, Units.val_pow_eq_pow_val, hg', z.2, map_one, Units.val_one]
    refine ⟨Equiv.ofBijective f hf, fun δ a => ?_⟩
    rw [hγ, map_act]
    rfl

theorem gamma_action_reduction : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  intro l _ P H S k _ _ _
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P S.K S.LL (S.W H)
  exact action_of_surjective (S.W H) χ hχ (chi_surjective P S.K S.LL _ S.hyp.1.2.1.1 χ hχ)
    (gamma_eq_act P S.K S.LL _ χ hχ)
    (card_torsion P S.K S.LL _ S.hyp.1.2.1.1 S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1) (algebraMap S.O k)

end GlobalTheory.RedAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalEulerChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.EulerScalars

noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem global_euler_char : GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S ρ hl hS hc

  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M) :=
    ⟨AddCommGroup.zmodModule (n := l ^ 1) (by simpa using hl)⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M,
      ∀ g m, ρ' g m = ρ g m := ⟨zmodRep (l ^ 1) ρ, fun _ _ => rfl⟩

  have hc' : ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction at hc ⊢
    simpa only [hρ'] using hc
  have hd : ∀ c : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M,
      ReciprocityTheory.Gal.d1 ρ c = ReciprocityTheory.Gal.d1 ρ' c := by
    intro c
    funext p
    rcases p with ⟨g, h⟩
    simp only [ReciprocityTheory.Gal.d1_apply, hρ']
  have e0 : {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ} ≃ {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ'} := by
    refine Equiv.subtypeEquivRight fun m => ?_
    rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    simp only [hρ']
  have c0 : Nat.card (ReciprocityTheory.Gal.H0 ρ) = Nat.card (ReciprocityTheory.Gal.H0 ρ') := Nat.card_congr e0
  have e1 : ReciprocityTheory.Gal.H1 ρ ≃ ReciprocityTheory.Gal.H1 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle, ReciprocityTheory.Gal.mem_Z1_iff_cocycle]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.mem_coboundaries1, ReciprocityTheory.Gal.mem_coboundaries1]; simp only [hρ'])
  have e2 : ReciprocityTheory.Gal.H2 ρ ≃ ReciprocityTheory.Gal.H2 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_cocycles2, ReciprocityTheory.Gal.mem_cocycles2]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]; simp only [hd])

  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hc'
  have hreal : ∀ w : InfinitePlace F, ¬ w.IsReal := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  have heq := hE F Ω l 1 M S ρ' one_pos hS hc' (fun _ => 1) (fun w hw => absurd hw (hreal w))

  have harch : archH0Card S ρ' (fun _ => 1) = Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
    classical
    unfold archH0Card
    rw [Finset.prod_eq_one, one_mul]
    intro w hw
    exact absurd (Finset.mem_filter.mp hw).2 (hreal w)
  rw [harch, IsTotallyComplex.finrank] at heq
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e1, c0, Nat.card_congr e2]
  have hpos : 0 < Nat.card M ^ InfinitePlace.nrComplexPlaces F := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← heq, two_mul, pow_add]
  ring

end GlobalTheory.EulerScalars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientsExplicitSumsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficients_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.goodO_coeff_explicit_sums | exact GlobalTheory.goodO_coeff_explicit_sums | (intros; apply GlobalTheory.goodO_coeff_explicit_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchange
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem tr_eJ_eq_tr_eJ' : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ →
      tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ hψ N k s hN χ hχ
  have key : ∀ i, i ≤ s →
      tr (GlobalTheory.GLm.ePat g N (GlobalTheory.GLm.phI k s i) (GlobalTheory.GLm.eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
    intro i
    induction i with
    | zero => intro _; exact GlobalTheory.GLm.FirstPattern.tr_first_pattern g ψ N k s hN χ hχ
    | succ n ih =>
      intro hn
      rw [GlobalTheory.RootExch.step g ψ hψ N k s (n + 1) hN (by omega) hn χ hχ]
      exact ih (by omega)
  rw [← GlobalTheory.GLm.ePat_last_eq_eJ g ψ N k s hN]
  exact key s le_rfl

end GlobalTheory.GLq
end

