module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGenerat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.ShMem

theorem coeff_iterate_derivative' {R : Type} [CommRing R] (f : R⟦X⟧) (i n : ℕ) :
    coeff n ((PowerSeries.derivative (R := R))^[i] f) = ((n + i).descFactorial i : R) * coeff (n + i) f := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, ← add_assoc,
      Nat.succ_descFactorial_succ]
    push_cast; ring

theorem charZero_of_ql {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem coeff_sh {K : Type} [NormedField K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (e : ℕ) (f : K⟦X⟧) (i n : ℕ) :
    ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (sh f)) =
      (((n / e).factorial * (n + i).descFactorial i : ℕ) : K) * coeff (n + i) f := by
  have h := congrArg (coeff n) (hsh f i)
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_iterate_derivative'] at h
  push_cast
  rw [mul_comm (i.factorial : K), mul_assoc, h]; ring

theorem eventually_dvd {l : ℕ} [hl : Fact l.Prime] {e : ℕ} [NeZero e] (r : ℕ) :
    ∀ᶠ p : ℕ × ℕ in cofinite, l ^ r ∣ (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat (l ^ r)).prod (Set.finite_lt_nat (e * l ^ r))).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq] at h
  refine ⟨?_, ?_⟩
  · show i < l ^ r
    by_contra hi; push_neg at hi
    exact h (Dvd.dvd.mul_left ((Nat.dvd_factorial (pow_pos hl.out.pos r) hi).trans
      (Nat.factorial_dvd_descFactorial _ _)) _)
  · show n < e * l ^ r
    by_contra hn; push_neg at hn
    apply h
    apply Dvd.dvd.mul_right
    apply Nat.dvd_factorial (pow_pos hl.out.pos r)
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne e))).2 (by rw [mul_comm]; exact hn)

theorem dvd_descFactorial {l n i : ℕ} (hi : i ≠ 0) (h : l ∣ n + i) : l ∣ (n + i).descFactorial i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [show n + j.succ = (n + j) + 1 from rfl, Nat.succ_descFactorial_succ]
  exact h.mul_right _

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

def nSh (e : ℕ) (p : ℕ × ℕ) : ℕ := (p.2 / e).factorial * (p.2 + p.1).descFactorial p.1


variable (l a) in
def wSh (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  (nSh e p : Wq l a) * coeff (p.2 + p.1) (frobS l a x)

def wDiff (e : ℕ) (x : (Wq l a)⟦X⟧) (p : ℕ × ℕ) : Wq l a :=
  if p.1 ≠ 0 ∧ l ∣ nSh e p then ((nSh e p / l : ℕ) : Wq l a) * coeff (p.2 + p.1) (frobS l a x) else 0

theorem coeff_frobS_eq_zero (x : (Wq l a)⟦X⟧) {m : ℕ} (h : ¬ l ∣ m) : coeff m (frobS l a x) = 0 := by
  have : coeff m (frobS l a x) = if l ∣ m then sigma l a (coeff (m / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [this, if_neg h]

theorem tendsToZero_crystallinePrismShiftedFrobeniusCoeff {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wSh l a e x) := fun r =>
  (eventually_dvd (l := l) (e := e) r).mono fun p hp => by
    have h := Nat.cast_dvd_cast (α := Wq l a) hp
    rw [Nat.cast_pow] at h
    exact h.mul_right _

theorem tendsToZero_crystallinePrismShiftedCoeffDivPrime {e : ℕ} [NeZero e] (x : (Wq l a)⟦X⟧) : LTo0 l (wDiff e x) := fun r =>
  (eventually_dvd (l := l) (e := e) (r + 1)).mono fun p hp => by
    unfold wDiff
    split_ifs with h
    · have h2 : l ^ r ∣ nSh e p / l := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hp)
      have h3 := Nat.cast_dvd_cast (α := Wq l a) h2
      rw [Nat.cast_pow] at h3
      exact h3.mul_right _
    · exact dvd_zero _

end Main

theorem shP_frob_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh x
  haveI : CharZero K := charZero_of_ql (l := l)
  have hkey : ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) *
      coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧))) = algebraMap O K (emb t τ (wSh l a e x (i, n))) := by
    intro τ i n
    rw [coeff_sh sh hsh e, coeff_toAc]
    simp only [wSh, nSh, map_mul, map_natCast, Nat.cast_mul]
  have hD : ∀ i n : ℕ, ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := fun i n =>
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  refine ⟨⟨wSh l a e x, tendsToZero_crystallinePrismShiftedFrobeniusCoeff x, fun τ i n => hkey τ i n⟩,
    fun τ => mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
      ((i.factorial * (n / e).factorial : ℕ) : K), ⟨wDiff e x, tendsToZero_crystallinePrismShiftedCoeffDivPrime x, fun τ i n => ?_⟩, ?_⟩
  · simp only [coeff_mk]; exact mul_div_cancel₀ _ (hD i n)
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    change coeff n (coeff i (sh (toAc t K (frobS l a x) τ : K⟦X⟧) - C (toAc t K (frobS l a x) τ : K⟦X⟧))) =
      coeff n (coeff i ((l : K⟦X⟧⟦X⟧) * mk fun i => mk fun n => algebraMap O K (emb t τ (wDiff e x (i, n))) /
        ((i.factorial * (n / e).factorial : ℕ) : K)))
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul,
      coeff_mk, coeff_mk, map_sub, map_sub, coeff_C]
    by_cases hi : i = 0
    · subst hi
      have h0 : wDiff e x (0, n) = 0 := by simp [wDiff]
      rw [if_pos rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_sh sh hsh, sub_self, h0]
      simp
    · rw [if_neg hi, map_zero, sub_zero]
      apply mul_left_cancel₀ (hD i n)
      rw [hkey, mul_left_comm, mul_div_cancel₀ _ (hD i n)]
      unfold wDiff
      split_ifs with h
      · have h1 : (nSh e (i, n) : Wq l a) = l * ((nSh e (i, n) / l : ℕ) : Wq l a) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' h.2]
        simp only [wSh, h1, map_mul, map_natCast]
        ring
      · have hn : ¬ l ∣ n + i := fun hd => h ⟨hi, (dvd_descFactorial hi hd).mul_left _⟩
        simp [wSh, coeff_frobS_eq_zero x hn]

end GlobalTheory.CrysPrism.ShMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_eq {ε δ : OCb l} (h : δ ^ l = ε) : δ = (frobeniusEquiv (OCb l) l).symm ε := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, ← h]
  rfl

theorem coeff_zero_muOf (x : OCb l) : (muOf x).coeff 0 = x - 1 := by
  change WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem frob_iterate_muOf (x : OCb l) (n : ℕ) :
    WittVector.frobenius^[n] (muOf x) = muOf (x ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]

theorem theta_muOf (x : OCb l) : Per.θ l (muOf x) = x.untilt - 1 := by
  rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]


variable (l) in
def kerAll : Ideal (Ainf l) := ⨅ n : ℕ, RingHom.ker ((Per.θ l).comp (WittVector.frobenius ^ n))

theorem mem_kerAll (a : Ainf l) : a ∈ kerAll l ↔ ∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0 := by
  simp only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]

theorem muOf_mem_kerAll {x : OCb l} (hx : x.untilt = 1) : muOf x ∈ kerAll l := by
  rw [mem_kerAll]
  intro n
  rw [frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]

theorem kerAll_sat (a : Ainf l) (h : (l : Ainf l) * a ∈ kerAll l) : a ∈ kerAll l := by
  rw [mem_kerAll] at h ⊢
  intro n
  have h1 := h n
  rw [← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)

theorem isEps_mem {ε : OCb l} (hε : IsEps ε) :
    GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hδ1⟩ := hε
  exact ⟨h1, by rw [← root_eq hδ]; exact hδ1⟩

theorem ne_one {ε : OCb l} (hε : IsEps ε) : ε ≠ 1 := by
  obtain ⟨-, δ, hδ, hδ1⟩ := hε
  rintro rfl
  have : δ = 1 := by rw [root_eq hδ, map_one]
  exact hδ1 (by rw [this, map_one])

theorem muOf_dvd {ε : OCb l} (hε : IsEps ε) {x : OCb l} (hx : x.untilt = 1) : muOf ε ∣ muOf x :=
  _root_.GlobalTheory.wittVector_dvd_of_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat
    (fun a ha => by rw [coeff_zero_muOf]; exact _root_.GlobalTheory.eps_sub_one_dvd_coeff_zero l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAll hx)

theorem muOf_ne_zero {ε : OCb l} (hε : IsEps ε) : muOf ε ≠ 0 := fun h => by
  have := congrArg (fun y : Ainf l => y.coeff 0) h
  simp only [coeff_zero_muOf, WittVector.zero_coeff] at this
  exact ne_one hε (sub_eq_zero.1 this)

theorem σA_muOf (g : GQ l) (x : OCb l) : Per.σA g (muOf x) = muOf (Per.σF g x) := by
  rw [muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]

theorem untilt_σF_eq {x : OCb l} (hx : x.untilt = 1) (g : GQ l) : (Per.σF g x).untilt = 1 := by
  rw [GlobalTheory.RingBasics.untilt_σF, hx, map_one]

end GlobalTheory.MuOfEps

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  exact ⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩

theorem units_σA {ε : OCb l} (hε : IsEps ε) (g : GQ l) :
    ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε := by
  obtain ⟨a, ha⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g)
  obtain ⟨b, hb⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)
  rw [← σA_muOf] at ha hb
  have h : muOf ε = Per.σA g b * a * muOf ε := by
    have := congrArg (Per.σA g) hb
    rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha] at this
    linear_combination this
  have h1 : Per.σA g b * a = 1 := by
    have h2 : (Per.σA g b * a - 1) * muOf ε = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))
  refine ⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩
  rw [ha, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  intro l _
  refine ⟨exists_isEps l, fun ε δ hε hδ => ?_⟩
  have hr := root_eq hδ
  have hE := isEps_mem hε
  refine ⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε,
    fun x hx => muOf_dvd hε hx⟩
  · rw [GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]
  · rw [muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, hδ]
  · rw [theta_muOf, sub_ne_zero]
    obtain ⟨-, δ', hδ', hδ'1⟩ := hε
    rwa [root_eq hδ', ← hr] at hδ'1
  · exact GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)
  · refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
    have h0 : (muOf ε).coeff 0 = 0 :=
      IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
    rw [coeff_zero_muOf] at h0
    exact ne_one hε (sub_eq_zero.1 h0)

end GlobalTheory.MuOfEps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGood
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.GoodLiftPoint

theorem good_of_lift : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  intro D h42 i σ P x hg hth hpt
  have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro h
    apply hth.1
    rw [h, Submodule.map_bot]
  obtain ⟨Sig, hW, hBC⟩ := (h42 i σ hne).2.1
  have hX : HasParamX D.nd D.naut i x Sig := ⟨P, hpt, hBC P hth⟩
  have hZ : x ∈ ZN D.nd D.naut i := by
    refine ⟨P, hpt, _, hBC P hth, ?_⟩
    unfold twistIso
    exact List.mem_map.2 ⟨muPart D.nd D.naut i, by simp, rfl⟩
  have hgood : x ∈ ZgoodN D.nd D.naut i :=
    ⟨hZ, Sig, hX, (GlobalTheory.LabelCompat.labCompat D i σ Sig hW).1 hg⟩
  exact ⟨hgood, GlobalTheory.LiftLeaf.atMOfParam D i x hgood Sig hX σ hW⟩

end GlobalTheory.GoodLiftPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarev
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ZDecompAt

theorem zDecomp_of_cheb : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  intro hC D hG i π hπ r hr
  obtain ⟨ρ, hρ⟩ := GlobalTheory.BlockComplement.complement_at hC D hG i π hπ r hr
  obtain ⟨e, he⟩ := hρ.rho
  exact ⟨ρ, e, fun g u => he g u⟩

end GlobalTheory.ZDecompAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) → (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T), (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | exact GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | (intros; apply GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceFormNondegenerate
section
open Formalism.MainNotions.N GlobalTheory.TraceSemisimple

namespace GlobalTheory.SemisimpleTraceForm

theorem idem_eq_zero_of_trace {k : Type} [Field k] [CharZero k] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : e.trace = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' e)) (Matrix.toLin' e) :=
    ⟨fun v => ⟨v, rfl⟩, by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun f : Module.End k (Fin n → k) => f v) hf⟩
  have h1 := hp.trace
  rw [Matrix.trace_toLin'_eq, ht] at h1
  have h2 : Module.finrank k (LinearMap.range (Matrix.toLin' e)) = 0 := by
    exact_mod_cast h1.symm
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h2
  exact (LinearEquiv.map_eq_zero_iff _).1 h2

theorem semisimple_span {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (h : IsSSRep ρ) : IsSemisimpleRing (spanAlg ρ) := by
  let φ : spanAlg ρ →+* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  letI : Module (spanAlg ρ) (Fin n → k) := Module.compHom _ φ
  have hs : ∀ (a : spanAlg ρ) (v : Fin n → k),
      a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v := fun _ _ => rfl
  have hinv : ∀ W, IsInv ρ W → ∀ a : spanAlg ρ, ∀ v ∈ W, a • v ∈ W := by
    rintro W hW ⟨a, ha⟩ v hv
    rw [hs]
    show a.mulVec v ∈ W
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add y z _ _ hy hz => rw [Matrix.add_mulVec]; exact W.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mulVec]; exact W.smul_mem c hy
  have hV : IsSemisimpleModule (spanAlg ρ) (Fin n → k) := by
    rw [isSemisimpleModule_iff]
    refine ⟨fun U => ?_⟩
    let W : Submodule k (Fin n → k) :=
      { toAddSubmonoid := U.toAddSubmonoid
        smul_mem' := fun c v hv => by
          have h1 : (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v ∈ U :=
            U.smul_mem (c • (1 : spanAlg ρ)) hv
          rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h1
          exact h1 }
    have hW : IsInv ρ W := fun g v hv =>
      U.smul_mem ⟨(ρ g : GL (Fin n) k), Submodule.subset_span ⟨g, rfl⟩⟩ hv
    obtain ⟨W', hW', hc⟩ := h W hW
    let U' : Submodule (spanAlg ρ) (Fin n → k) :=
      { toAddSubmonoid := W'.toAddSubmonoid
        smul_mem' := fun a v hv => hinv W' hW' a v hv }
    refine ⟨U', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      exact fun v hv hv' => Submodule.disjoint_def.1 hc.disjoint v hv hv'
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
      exact Submodule.add_mem_sup hy hz
  let ψ : spanAlg ρ →ₗ[spanAlg ρ] (Fin n → Fin n → k) :=
    LinearMap.pi fun j => LinearMap.toSpanSingleton _ _ (Pi.single j 1)
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    ext i j
    have h1 : (a : Matrix (Fin n) (Fin n) k).mulVec ((Pi.single j 1 : Fin n → k)) i = 0 :=
      congrFun (congrFun ha j) i
    simpa using h1
  have hP : IsSemisimpleModule (spanAlg ρ) (Fin n → Fin n → k) :=
    instIsSemisimpleModuleForallOfFinite fun _ => Fin n → k
  exact IsSemisimpleModule.of_injective ψ hψ

theorem trace_form_nondegenerate :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (ρ : Γ →* GL (Fin n) k),
      IsSSRep ρ → ∀ x ∈ spanAlg ρ,
        (∀ g : Γ, Matrix.trace (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = 0) →
        x = 0 := by
  intro Γ k _ _ _ n ρ h x hx ht
  have := semisimple_span ρ h
  have hA : ∀ a ∈ spanAlg ρ, (x * a).trace = 0 := by
    intro a ha
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact ht g
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  let y : spanAlg ρ := ⟨x, hx⟩
  obtain ⟨C, hC⟩ := exists_isCompl (Submodule.span (spanAlg ρ) {y})
  have h1 : (1 : spanAlg ρ) ∈ Submodule.span (spanAlg ρ) {y} ⊔ C := by
    rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  have key : ∀ z ∈ Submodule.span (spanAlg ρ) {y}, z * e = z := by
    intro z hz
    have h2 : z * f = z - z * e := by
      rw [eq_sub_iff_add_eq', ← mul_add, hef, mul_one]
    have h3 : z * f = 0 :=
      Submodule.disjoint_def.1 hC.disjoint _
        (h2 ▸ Submodule.sub_mem _ hz (Submodule.smul_mem _ z he)) (C.smul_mem z hf)
    rw [h3] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  have he0 : (e : Matrix (Fin n) (Fin n) k) = 0 := by
    refine idem_eq_zero_of_trace _ (congrArg Subtype.val (key e he)) ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 he
    show ((a : Matrix (Fin n) (Fin n) k) * x).trace = 0
    rw [Matrix.trace_mul_comm]
    exact hA a a.2
  have h4 : x * (e : Matrix (Fin n) (Fin n) k) = x :=
    congrArg Subtype.val (key y (Submodule.mem_span_singleton_self y))
  rw [← h4, he0, mul_zero]

end GlobalTheory.SemisimpleTraceForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n : ℕ) (x : ℤ_[l]), x ≠ 0 → (l : Per.Acris l) ^ n ∣ ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) x) → (l - 1) * n ≤ (l - 1) * x.valuation + 2 * j := by
  first | exact @GlobalTheory.AcrisMuBound.main | exact GlobalTheory.AcrisMuBound.main | (intros; apply GlobalTheory.AcrisMuBound.main <;> assumption)
end

