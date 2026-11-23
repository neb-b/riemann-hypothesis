module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0169
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import GroundTheory.AutomorphicForms.GL2.Bundle0003
public import GroundTheory.GlobalFields.TateThesis.TateMain

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductions
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem mem_span_pow_of_factorial_mul_eq {S : Type} [CommRing S] (hS : R.TF S) {l : ℕ}
    (hl : l.Prime) (n : ℕ) {x : S} (hx : x ∈ Ideal.span {(l : S) ^ n}) {k : ℕ} (hk : k ≠ 0)
    {y : S} (e : (k.factorial : S) * y = x ^ k) : y ∈ Ideal.span {(l : S) ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  haveI := Fact.mk hl
  obtain ⟨v, m, hlm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one
  have hv : v < k := by
    have h1 : v ≤ multiplicity l k.factorial :=
      (Nat.pow_dvd_iff_le_multiplicity hl.ne_one k.factorial_ne_zero).1 ⟨m, hm⟩
    exact lt_of_le_of_lt h1 (multiplicity_factorial_lt_of_ne_zero l hk)
  obtain ⟨t, ht⟩ : ∃ t, n * k = n + v + t := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨n * k' - v, ?_⟩
    have : v ≤ n * k' := by nlinarith [Nat.lt_succ_iff.1 hv]
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    omega
  have hfac : (k.factorial : S) = (l : S) ^ v * (m : S) := by rw [hm]; push_cast; rfl
  have e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k)) := by
    rw [← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]
    ring
  have hr : (l : S) ^ v ∈ nonZeroDivisors S := pow_mem (hS l hl.ne_zero) v
  have e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k) := by
    have h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))
  have hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → S) hab
  have hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n := by
    calc y = ((a : S) * (m : S) + (b : S) * (l : S) ^ n) * y := by rw [hab', one_mul]
      _ = (a : S) * ((m : S) * y) + (b : S) * (l : S) ^ n * y := by ring
      _ = _ := by rw [e3]; ring
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_dividedPowers_map_mkAcr {l : ℕ} [hl : Fact l.Prime] (A : PAlg l) (n : ℕ)
    (I : Ideal A.Acr0) (hI : R.PdI I) (K : Ideal (A.Acr n)) (hK : K = I.map (A.mkAcr n)) :
    ∃ δ : DividedPowers K, R.IsPd (A.mkAcr n) I δ := by
  subst hK
  exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I
    (Ideal.span {(l : A.Acr0) ^ n}) hI
    fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e

theorem exists_dividedPowers_fil_pfil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧
      ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  intro l _ A n
  obtain ⟨-, -, -, -, h1, h2, -⟩ := _root_.GlobalTheory.CompanionTheory.FilMul.main A
  obtain ⟨p1, p2, -⟩ := _root_.GlobalTheory.CompanionTheory.PerfFil.pdI_main A
  exact ⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1),
    exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TiltIdem

variable {B R : Type} [CommRing B] [CommRing R]

theorem idem_eq (i : B →* R)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {x y : B} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : ∀ p : PrimeSpectrum R, i x ∉ p.asIdeal ↔ i y ∉ p.asIdeal) : x = y := by
  have hix : IsIdempotentElem (i x) := by
    change i x * i x = i x
    rw [← map_mul, hx.eq]
  have hiy : IsIdempotentElem (i y) := by
    change i y * i y = i y
    rw [← map_mul, hy.eq]
  have hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y) := by
    ext p
    exact h p
  have e : i x = i y := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb
  exact (hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩

theorem exists_idem (i : B →* R) (h0 : i 0 = 0)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {ι : Type} [Fintype ι] (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧
      (∀ (a : ι) (p : PrimeSpectrum R), i (e a) ∉ p.asIdeal ↔ f p = a) ∧
      ∀ (e' : B) (a : ι), IsIdempotentElem e' →
        (∀ p : PrimeSpectrum R, i e' ∉ p.asIdeal → f p = a) → e' * e a = e' := by
  classical
  have hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a := by
    intro a
    have hc : IsClopen (f ⁻¹' {a}) := f.isLocallyConstant.isClopen_fiber a
    obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.1 hc
    obtain ⟨e₀, ⟨he₀, rfl⟩, -⟩ := hidem ε hε
    refine ⟨e₀, he₀, fun p => ?_⟩
    have : p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀) := by rw [hs]; rfl
    exact this.symm
  choose e he hp using hfib
  have hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal) := fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)
  have hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal := by
    intro x y p
    rw [map_mul, p.isPrime.mul_mem_iff_mem_or_mem]
    tauto
  have hort : OrthogonalIdempotents e := by
    refine ⟨he, fun a b hab => ?_⟩
    refine idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    obtain ⟨h1, h2⟩ := (hmul _ _ p).1 h
    exact hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))
  have hsum : IsIdempotentElem (∑ a, e a) := hort.isIdempotentElem_sum
  have hc : IsIdempotentElem (1 - ∑ a, e a) := hsum.one_sub
  have hce : ∀ a, (1 - ∑ b, e b) * e a = 0 := by
    intro a
    rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]
    · exact fun b _ hb => hort.ortho hb
    · exact fun h => absurd (Finset.mem_univ a) h
  have hone : 1 - ∑ a, e a = 0 := by
    refine idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    have h1 : i (e (f p)) ∉ p.asIdeal := (hp (f p) p).2 rfl
    have h2 := (hmul _ _ p).2 ⟨h, h1⟩
    rw [hce] at h2
    exact hnot0 p h2
  refine ⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩
  refine idem_eq i hidem (he'.mul (he a)) he' fun p => ?_
  rw [hmul]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩

theorem sharp_zero' {l : ℕ} [Fact l.Prime] (A : PAlg l) : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem lcIdem : CrystallineSemistableComparison.E.LcIdem := by
  intro l _ H A hA ι _ f
  let i : A.A →* A.Ug := (algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp
  have h0 : i 0 = 0 := by
    change algebraMap A.U A.Ug (A.sharp 0) = 0
    rw [sharp_zero', map_zero]
  let f' : LocallyConstant (PrimeSpectrum A.Ug) ι := ⟨f, f.isLocallyConstant⟩
  exact exists_idem i h0 (H.idem A hA) f'

end GlobalTheory.CompanionTheory.TiltIdem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap ContDiff
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

section Majorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_dilate_le (f : 𝓢(E, ℝ)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (a • y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a • x)‖ := by
  have hg : (fun y ↦ f (a • y)) = f ∘ (a • ContinuousLinearMap.id ℝ E) := rfl
  have hle : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg ha0]
    exact mul_le_one₀ ha1 (norm_nonneg _) ContinuousLinearMap.norm_id_le
  rw [hg, ContinuousLinearMap.iteratedFDeriv_comp_right _ (f.smooth ⊤) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hle

theorem exists_schwartz_majorant [FiniteDimensional ℝ E] (φ : 𝓢(E, ℂ)) :
    ∃ Φ : 𝓢(E, ℂ), ∃ r : E → ℝ, (∀ y, Φ y = (r y : ℂ)) ∧ ∀ y, ‖φ y‖ ≤ r y := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, by norm_num⟩
  let χ : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ b.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ b.le_one
  have hχb : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦
    b.one_of_mem_closedBall (by simpa [b] using hy)
  have hAex : ∀ m : ℕ, ∃ A : ℝ, ∀ y, (1 + ‖y‖) ^ m * ‖φ y‖ ≤ A := fun m ↦
    ⟨_, fun y ↦ by
      simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, 0)) le_rfl le_rfl
        φ y⟩
  choose A hA using hAex
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦
    (by positivity : 0 ≤ (1 + ‖(0 : E)‖) ^ m * ‖φ 0‖).trans (hA m 0)
  let c : ℕ → ℝ := fun k ↦ ⨅ m : ℕ, A m / ((2 : ℝ) ^ k) ^ m
  have hbdd : ∀ k : ℕ, BddBelow (Set.range fun m : ℕ ↦ A m / ((2 : ℝ) ^ k) ^ m) := fun k ↦
    ⟨0, by rintro _ ⟨m, rfl⟩; exact div_nonneg (hA0 m) (by positivity)⟩
  have hc0 : ∀ k, 0 ≤ c k := fun k ↦ le_ciInf fun m ↦ div_nonneg (hA0 m) (by positivity)
  have hcle : ∀ k m, c k ≤ A m / ((2 : ℝ) ^ k) ^ m := fun k m ↦ ciInf_le (hbdd k) m
  have hsum : ∀ m : ℕ, Summable fun k : ℕ ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m := by
    intro m
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hc0 k) (by positivity)) (fun k ↦ ?_)
      (summable_geometric_two.mul_left (A (m + 1) * 2 ^ m))
    have e1 : ((2 : ℝ) ^ (k + 1)) ^ m = ((2 : ℝ) ^ k) ^ m * 2 ^ m := by
      rw [pow_succ, mul_pow]
    have e2 : ((2 : ℝ) ^ k) ^ (m + 1) = ((2 : ℝ) ^ k) ^ m * 2 ^ k := by rw [pow_succ]
    calc c k * ((2 : ℝ) ^ (k + 1)) ^ m
        ≤ A (m + 1) / ((2 : ℝ) ^ k) ^ (m + 1) * ((2 : ℝ) ^ (k + 1)) ^ m := by
          gcongr
          exact hcle k (m + 1)
      _ = A (m + 1) * 2 ^ m * (1 / 2) ^ k := by
          rw [e1, e2, one_div, inv_pow]
          field_simp
  let a : ℕ → ℝ := fun k ↦ ((2 : ℝ) ^ (k + 1))⁻¹
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by positivity
  have ha1 : ∀ k, a k ≤ 1 := fun k ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  let f : ℕ → E → ℝ := fun k y ↦ c k * χ (a k • y)
  have hfsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k ↦
    contDiff_const.mul ((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id))
  choose D hD using fun (m n : ℕ) ↦ χ.decay' m n
  have hfd : ∀ (k m n : ℕ) (x : E),
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
    intro k m n x
    have e1 : iteratedFDeriv ℝ n (f k) x =
        c k • iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x :=
      iteratedFDeriv_const_smul_apply (a := c k) (f := fun y ↦ χ (a k • y))
        (((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id)).contDiffAt.of_le
          (by exact_mod_cast le_top))
    have e2 : ‖x‖ = (2 : ℝ) ^ (k + 1) * ‖a k • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), ← mul_assoc, mul_inv_cancel₀ (by positivity),
        one_mul]
    rw [e1, norm_smul, Real.norm_of_nonneg (hc0 k)]
    calc ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x‖)
        ≤ ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          have := norm_iteratedFDeriv_dilate_le χ (ha0 k) (ha1 k) n x
          have := hc0 k
          gcongr
      _ = c k * ((2 : ℝ) ^ (k + 1)) ^ m *
            (‖a k • x‖ ^ m * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          rw [e2, mul_pow]
          ring
      _ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
          exact mul_le_mul_of_nonneg_left (hD m n (a k • x))
            (mul_nonneg (hc0 k) (by positivity))
  have hfv : ∀ (n k : ℕ) (x : E), ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * D 0 n := by
    intro n k x
    simpa using hfd k 0 n x
  have hsv : ∀ n : ℕ, Summable fun k ↦ c k * D 0 n := fun n ↦ by
    simpa using (hsum 0).mul_right (D 0 n)
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ ∑' k, f k y :=
    contDiff_tsum (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n) fun n k x _ ↦ hfv n k x
  let Φr : 𝓢(E, ℝ) :=
    { toFun := fun y ↦ ∑' k, f k y
      smooth' := hsmooth
      decay' := by
        intro m n
        refine ⟨(∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n, fun x ↦ ?_⟩
        rw [iteratedFDeriv_tsum_apply (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n)
          (fun n k x _ ↦ hfv n k x) (by exact_mod_cast le_top) x]
        have hs1 : Summable fun k ↦ ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hfv n k x) (hsv n)
        have hs2 : Summable fun k ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
          (hsum m).mul_right _
        calc ‖x‖ ^ m * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ m * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hs1
          _ = ∑' k, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ ∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
              (hs1.mul_left _).tsum_le_tsum (fun k ↦ hfd k m n x) hs2
          _ = (∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n := tsum_mul_right }
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM Φr, Φr, fun y ↦ rfl, fun y ↦ ?_⟩
  have hf0 : ∀ k, 0 ≤ f k y := fun k ↦ mul_nonneg (hc0 k) (hχ0 _)
  have hfs : Summable fun k ↦ f k y := by
    refine Summable.of_nonneg_of_le hf0 (fun k ↦ ?_) (by simpa using hsum 0)
    exact mul_le_of_le_one_right (hc0 k) (hχ1 _)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 + ‖y‖) (y := (2 : ℝ))
    (by linarith [norm_nonneg y]) (by norm_num)
  have h1 : ‖φ y‖ ≤ c k := by
    refine le_ciInf fun m ↦ ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hA m y)
    gcongr
  have h2 : f k y = c k := by
    have : χ (a k • y) = 1 := by
      refine hχb _ ?_
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), inv_mul_le_iff₀ (by positivity), mul_one]
      linarith
    simp only [f, this, mul_one]
  calc ‖φ y‖ ≤ f k y := h2 ▸ h1
    _ ≤ ∑' k, f k y := hfs.le_tsum k fun j _ ↦ hf0 j

end Majorant

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

variable {K : Type _} [Field K] [NumberField K]

end GlobalTheory.CompanionTheory.EisRk1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogMulPf

def ratHom {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) : ℚ →+* S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom S) (fun y => by
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h := hu _ (Int.natAbs_ne_zero.2 hy)
    rcases Int.natAbs_eq (y : ℤ) with e | e
    · rw [e]; simpa using h
    · rw [e]; simpa using h)

theorem inv_smul_eq {S : Type} [CommRing S] [Algebra ℚ S] (m : ℕ) (hm : m ≠ 0) (x : S) :
    ((m : ℚ)⁻¹) • x = Ring.inverse (m : S) * x := by
  have h1 : (m : S) * algebraMap ℚ S (m : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ S), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]
  have h : IsUnit (m : S) := IsUnit.of_mul_eq_one _ h1
  apply h.mul_left_cancel
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, h1, Ring.mul_inverse_cancel _ h]

theorem core (hLA : LogAlg) {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) (T : Subring S) (x y : S)
    (hx : ∀ k : ℕ, Ring.inverse (k.factorial : S) * x ^ k ∈ T)
    (hy : ∀ k : ℕ, Ring.inverse (k.factorial : S) * y ^ k ∈ T) :
    (∀ k : ℕ, Ring.inverse (k.factorial : S) * (x + y + x * y) ^ k ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) *
          (Ring.inverse ((k + 1).factorial : S) * (x + y + x * y) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * x ^ (k + 1)) +
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * y ^ (k + 1)) +
          (N.factorial : S) * c := by
  letI : Algebra ℚ S := (ratHom hu).toAlgebra
  have e : ∀ (k : ℕ) (z : S), ((k.factorial : ℚ)⁻¹) • z ^ k = Ring.inverse (k.factorial : S) * z ^ k :=
    fun k z => inv_smul_eq _ k.factorial_ne_zero _
  have := hLA S T (fun k z => ((k.factorial : ℚ)⁻¹) • z ^ k) (fun _ _ => rfl) x y
    (fun k => by simp only [e]; exact hx k) (fun k => by simp only [e]; exact hy k)
  simpa only [e] using this

theorem sum_eq_of_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (T : Subalgebra R S) (f f' f'' : ℕ → T)
    (N : ℕ) (c : T)
    (e : ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f'' (k + 1) : S) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f (k + 1) : S) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f' (k + 1) : S) + (N.factorial : S) * (c : S)) :
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f'' (k + 1) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f (k + 1) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f' (k + 1) + (N.factorial : T) * c := by
  apply Subtype.ext
  push_cast
  exact e

variable {l : ℕ} [Fact l.Prime]

theorem factorial_acr (A : PAlg l) (n : ℕ) : (((l * n).factorial : ℕ) : A.Acr n) = 0 := by
  obtain ⟨d, hd⟩ := ACris.pow_dvd_factorial (p := l) (le_refl (l * n))
  rw [hd, Nat.cast_mul, Nat.cast_pow, A.pow_l_acr, zero_mul]

theorem isLog_mul (hLA : LogAlg) (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n)
    (hy : IsLog A n w y) (hy' : IsLog A n w' y') : IsLog A n (w * w') (y + y') := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have hab : algebraMap A.W (WL l A.A) (w * w' - 1) =
      algebraMap A.W (WL l A.A) (w - 1) + algebraMap A.W (WL l A.A) (w' - 1) +
        algebraMap A.W (WL l A.A) (w - 1) * algebraMap A.W (WL l A.A) (w' - 1) := by
    simp only [map_sub, map_mul, map_one]; ring
  obtain ⟨hT, hN⟩ := core hLA (fun m hm => A.isUnit_natCast hm) A.Acr0.toSubring
    (algebraMap A.W (WL l A.A) (w - 1)) (algebraMap A.W (WL l A.A) (w' - 1))
    (fun k => by have h := (g k).2; rw [hg k] at h; exact h)
    (fun k => by have h := (g' k).2; rw [hg' k] at h; exact h)
  have hmem : ∀ k, dpw k (w * w' - 1) ∈ A.Acr0 := fun k => by
    rw [dpw, hab]; exact hT k
  obtain ⟨c, hc, e⟩ := hN (l * n)
  refine ⟨fun k => ⟨dpw k (w * w' - 1), hmem k⟩, fun _ => rfl, ?_⟩
  have e0 := sum_eq_of_coe A.Acr0 g g' (fun k => ⟨dpw k (w * w' - 1), hmem k⟩) (l * n) ⟨c, hc⟩ (by
    simp only [hg, hg']
    simp only [dpw, hab]
    exact e)
  have e1 := congrArg (A.mkAcr n) e0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at e1
  rw [e1, factorial_acr, zero_mul, add_zero]

theorem logMul : CrystallineSemistableComparison.E.LogAlg → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul :=
  fun h _ _ _ A n w w' y y' _ _ hy hy' => isLog_mul h A n w w' y y' hy hy'

end GlobalTheory.CompanionTheory.LogMulPf
end
end

