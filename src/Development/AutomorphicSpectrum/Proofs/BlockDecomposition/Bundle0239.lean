module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0010
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParity
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame.SignWord

variable {n : ℕ}

def sg (b : Bool) : ℤ := cond b 1 (-1)

theorem step_sign (a b c e : Bool) (k : ℕ) (h : Xor (a = b) (c = e)) :
    sg c * sg a * (-1 : ℤ) ^ k = sg e * sg b * (-1 : ℤ) ^ (k + 1) := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor, sg, pow_succ]

theorem sign_left (b : Bool) (k : ℕ) (h : sg b * sg true * (-1 : ℤ) ^ k = 1) :
    b = true ↔ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sign_right (b : Bool) (k : ℕ) (h : sg b * sg false * (-1 : ℤ) ^ k = 1) :
    b = true ↔ ¬ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sum_neg_one_pow (n : ℕ) : ∑ p ∈ range (2 * n + 1), (-1 : ℤ) ^ p = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h : (-1 : ℤ) ^ (2 * k + 1) = -1 := (odd_two_mul_add_one k).neg_one_pow
    have h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h]; norm_num
    rw [h, h']; norm_num

theorem above_lt_of_lt (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) {r : ℝ}
    (x : Fin (n + 1) ⊕ Fin n) (h : r < Sum.elim d d' x) :
    above d d' (Sum.elim d d' x) < above d d' r := by
  unfold above
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · simpa using h
  · simp

theorem above_lt_card (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (x : Fin (n + 1) ⊕ Fin n) :
    above d d' (Sum.elim d d' x) < 2 * n + 1 := by
  have h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card := by
    unfold above
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩
  have h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1 := by
    simp [Finset.card_univ, Fintype.card_sum]; ring
  omega

theorem above_injective (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    Function.Injective fun x => above d d' (Sum.elim d d' x) := by
  intro x y hxy
  simp only at hxy
  rcases lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h
  · have := above_lt_of_lt d d' y h
    omega
  · exact hv h
  · have := above_lt_of_lt d d' x h
    omega

theorem above_image (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x)) =
      range (2 * n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (above_lt_card d d' x)
  · rw [Finset.card_image_of_injective _ (above_injective d d' hv)]
    simp [Finset.card_univ, Fintype.card_sum]
    omega

theorem sum_above (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    ∑ x : Fin (n + 1) ⊕ Fin n, (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = 1 := by
  have h := sum_neg_one_pow n
  rw [← above_image d d' hv,
    Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)] at h
  exact h

theorem sum_signs (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e) :
    ∑ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = 1 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1 := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have h0 : sg (ε (e (Sum.inr ()))) = 1 := by
      have : ε (e (Sum.inr ())) = true := hf.1
      simp [this, sg]
    simp [hf.2, h0]
  have hl : sg true = 1 := rfl
  have hr : sg false = -1 := rfl
  simp [hl, hr, h1]

theorem step_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') (x y : Fin (n + 1) ⊕ Fin n)
    (hxy : above d d' (Sum.elim d d' y) = above d d' (Sum.elim d d' x) + 1) :
    sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
      sg (Sum.elim ε ε' y) * sg y.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' y) := by
  have hlt : Sum.elim d d' y < Sum.elim d d' x := by
    rcases lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h
    · exact h
    · rw [h] at hxy; omega
    · have := above_lt_of_lt d d' y h
      omega
  have hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x) := by
    rintro z ⟨h1, h2⟩
    have a1 := above_lt_of_lt d d' z h1
    have a2 := above_lt_of_lt d d' x h2
    omega
  have hstep := hw x y hlt hno
  rw [hxy]
  exact step_sign _ _ _ _ _ hstep

theorem const_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    ∃ T : ℤ, ∀ x : Fin (n + 1) ⊕ Fin n,
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = T := by
  have him := above_image d d' hv
  have hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p := by
    intro p hp
    have : p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image
        (fun x => above d d' (Sum.elim d d' x)) := by
      rw [him]; exact mem_range.2 hp
    obtain ⟨x, -, hx⟩ := mem_image.1 this
    exact ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hsurj 0 (by omega)
  refine ⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩
  have key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p →
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
        sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0) := by
    intro p
    induction p with
    | zero =>
      intro x hx
      have : x = x0 := above_injective d d' hv (by simp only [hx, hx0])
      rw [this]
    | succ k ih =>
      intro x hx
      have hk : k < 2 * n + 1 := by
        have := above_lt_card d d' x
        omega
      obtain ⟨y, hy⟩ := hsurj k hk
      rw [← ih y hy]
      exact (step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm
  exact fun x => key _ x rfl

theorem heSign (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e)
    (hv : Function.Injective (Sum.elim d d')) (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧
      ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  obtain ⟨T, hT⟩ := const_letters ε d ε' d' hv hw
  have hsum : T = 1 := by
    have h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft =
        T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) := by
      intro x
      rw [← hT x]
      have hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) *
          ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1 := by
        rw [← mul_pow]; simp
      rw [mul_assoc, hp, mul_one]
    have h2 := sum_signs ε ε' e hf
    simp_rw [h1] at h2
    rw [← Finset.mul_sum, sum_above d d' hv] at h2
    simpa using h2
  subst hsum
  refine ⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)),
    fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩

end GlobalTheory.CompanionTheory.RgHeFrame.SignWord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrMod

theorem factor_factor {R : Type} [CommRing R] {I J K : Ideal R} (h1 : I ≤ J) (h2 : J ≤ K) (y : R ⧸ I) :
    Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem fil_extend {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : B →+* B') (hJ : J' = J.map φ)
    (h : IsDPMorphism δ δ' φ) (r : ℕ) : fil δ' r = (fil δ r).map φ := by
  subst hJ
  exact (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers δ φ δ' h).1 r

theorem pow_mem_span {R : Type} [CommRing R] {I : Ideal R} (δ : DividedPowers I) {p : ℕ} (hp : p ≠ 0)
    {x : R} (hx : x ∈ I) : x ^ p ∈ Ideal.span {(p : R)} := by
  rw [← δ.factorial_mul_dpow_eq_pow hx]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem l_mem_pfil : (l : A.Acr n) ∈ A.PFil n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

theorem sharp_zero : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem uToPQ_th (x : A.W) : A.uToPQ n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := by
  rw [uToPQ, RingHom.comp_apply, uToQ_th, Ideal.Quotient.factor_mk]

theorem exists_pi : ∃ π : A.A →+* A.Acr n ⧸ A.PFil n,
    (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧
      π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi}) := by
  let g : A.W →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.mk _).comp (A.toAcr n)
  let π : A.A →+* A.Acr n ⧸ A.PFil n :=
    (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective ⟨g, fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
      rw [RingHom.mem_ker, map_mul, RingHom.comp_apply (Ideal.Quotient.mk _) (A.toAcr n) (l : A.W), map_natCast,
        Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n), mul_zero]⟩
  have hπ : ∀ x : A.W, π (x.coeff 0) = g x := fun x => RingHom.liftOfSurjective_comp_apply _ _ _ x
  have ht : ∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a)) := fun a => by
    have := hπ (WittVector.teichmuller l a)
    rwa [WittVector.teichmuller_coeff_zero] at this
  have hs : ∀ a, π a = A.uToPQ n (A.sharp a) := fun a => by
    rw [ht]
    exact (uToPQ_th A n _).symm
  refine ⟨π, ht, fun y => ?_, ?_, fun hn => ?_⟩
  · obtain ⟨u, rfl⟩ := (RL.uToQ A n).2.2.1 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, (hπ x).trans (uToPQ_th A n x).symm⟩
  · rw [hs, sharp_pi, map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n)
  · ext a
    have h := (RL.sharp_cong A).2.1 a 0
    rw [sharp_zero, sub_zero, sub_zero] at h
    rw [RingHom.mem_ker, hs, ← RingHom.mem_ker, (RL.uToQ A n).2.2.2 hn, h]

theorem fil_eq_map (r : ℕ) : A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 (mapAcr_fil A.fromBase n r))
  rw [PAlg.Fil, Ideal.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [← mapAcr_dxi A.fromBase n k]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, hk, rfl⟩)

theorem pfil_eq_map : A.PFil n = ((base l).PFil n).map (mapAcr A.fromBase n) := by
  rw [PFil, PFil, Ideal.map_sup, ← fil_eq_map, Ideal.map_span, Set.image_singleton, map_natCast]

theorem jj_eq_map (k : Bool) : JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n) := by
  cases k
  · exact fil_eq_map A n 1
  · exact pfil_eq_map A n

theorem fil_mono {r s : ℕ} (h : r ≤ s) : A.Fil n s ≤ A.Fil n r := by
  refine Ideal.span_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h.trans hk, rfl⟩

theorem fil_pdFil (r : ℕ) : fil (A.pdFil n) r = A.Fil n r := by
  refine le_antisymm ?_ ?_
  · have hprod : ∀ L : List (ℕ × A.Acr n), (∀ p ∈ L, p.2 ∈ A.Fil n 1) →
        (L.map fun p => (A.pdFil n).dpow p.1 p.2).prod ∈ A.Fil n (L.map Prod.fst).sum := by
      intro L
      induction L with
      | nil =>
        intro _
        simp only [List.map_nil, List.prod_nil, List.sum_nil]
        rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1 n]
        trivial
      | cons p L ih =>
        intro hL
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact (RL.filtration_multiplicative A).2.2.2.2.2.2.2 n _ _ (Ideal.mul_mem_mul
          (A.dpow_mem_fil n p.1 (hL p (by simp))) (ih fun q hq => hL q (by simp [hq])))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact fil_mono A n h2 (hprod L h1)
  · rw [PAlg.Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [← A.dpow_dxi n k]
    have h1 : A.dxi n 1 ∈ A.Fil n 1 := Ideal.subset_span ⟨1, le_rfl, rfl⟩
    exact GlobalTheory.CompanionTheory.PDMap.fil_anti (A.pdFil n) hk (GlobalTheory.CompanionTheory.PDMap.dpow_mem_fil (A.pdFil n) h1 k)

theorem pfil_pow (x : A.Acr n) (hx : x ∈ A.PFil n) : IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)} := by
  have h := pow_mem_span (A.pdPFil n) (Fact.out : l.Prime).ne_zero hx
  refine ⟨?_, h⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨l * n, by rw [pow_mul, ← hc, mul_pow, A.pow_l_acr n, mul_zero]⟩

theorem uJ_facts (k : Bool) (hn : n ≠ 0) :
    Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, hu⟩ := (RL.uToQ A n).1 (Ideal.Quotient.mk _ z)
    refine ⟨u, ?_⟩
    rw [uJ, RingHom.comp_apply, hu, Ideal.Quotient.factor_mk]
  · have e : A.uToPQ n x = Ideal.Quotient.factor (le_pfil k A n) (uJ k A n x) := by
      rw [uJ, RingHom.comp_apply, factor_factor]
      rfl
    have h0 : x ∈ RingHom.ker (A.uToPQ n) := by
      rw [RingHom.mem_ker, e, RingHom.mem_ker.1 hx, map_zero]
    rw [(RL.uToQ A n).2.2.2 hn] at h0
    exact (Ideal.span_singleton_le_iff_mem _).2 (R.mem_jacobson_of_complete (l : A.U)) h0

theorem acr_modp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  intro l _ A n
  exact ⟨exists_pi A n, fil_eq_map A n, jj_eq_map A n, fil_pdFil A n,
    fun k r => fil_extend _ _ _ (jj_eq_map A n k) (dd_map k A.fromBase n) r,
    pfil_pow A n, fun k hn => uJ_facts A n k hn⟩

end GlobalTheory.CompanionTheory.AcrMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}

def secs {E : X.Modules} (S : Subobject E) (V : X.Opens) : Set Γ(E, V) :=
  Set.range (S.arrow.app V)

def Killed (J : X.IdealSheafData) {E : X.Modules} (S : Subobject E) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x : Γ(E, U), a • x ∈ secs S U

variable [X.Over (Spec (.of A))]

def powSub (E : X.Modules) (n : ℕ) : Subobject E := Subobject.mk (idealPowι I E n)

def PropSupp (A : Type) [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules}
    (S : Subobject E) : Prop :=
  ∃ T : X.IdealSheafData, IsProper (T.subschemeι ≫ (X ↘ Spec (.of A))) ∧
    Scheme.Modules.SupportedIn (cokernel S.arrow) (T.support : Set X)

structure ClosedSys (E : X.Modules) (S : ℕ → Subobject E) : Prop where
  qcoh : ∀ e, (S e : X.Modules).IsQuasicoherent
  pow_le : ∀ e, powSub I E (e + 1) ≤ S e
  succ : ∀ e, S e = S (e + 1) ⊔ powSub I E (e + 1)

def Alg (E : X.Modules) (S : ℕ → Subobject E) : Prop :=
  ∃ B : Subobject E, (B : X.Modules).IsQuasicoherent ∧ PropSupp A B ∧
    ∀ e, B ⊔ powSub I E (e + 1) = S e

def Statement (J : X.IdealSheafData) : Prop :=
  ∀ (E : X.Modules), IsCoherent E → ∀ S : ℕ → Subobject E, ClosedSys I E S →
    (∀ e, Killed J (S e)) → PropSupp A (S 0) → Alg I E S

def restrictSys {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (c e : ℕ) :
    Subobject (D : X.Modules) :=
  (Subobject.pullback D.arrow).obj (S (e + c)) ⊔ powSub I (D : X.Modules) (e + 1)

lemma powSub_succ_le (E : X.Modules) (n : ℕ) : powSub I E (n + 1) ≤ powSub I E n :=
  Subobject.mk_le_mk_of_comm (idealPowSucc I E n) (idealPowSucc_ι I E n)

theorem closedSys_pow (E : X.Modules) [E.IsQuasicoherent] :
    ClosedSys I E (fun e => powSub I E (e + 1)) := by
  refine { qcoh := ?_, pow_le := fun _ => le_rfl, succ := ?_ }
  · intro e
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (idealPowι I E (e + 1))).symm inferInstance
  · intro e
    exact (sup_eq_right.2 (powSub_succ_le I E (e + 1))).symm

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientFiltrationBijectiveOfCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.QuoK

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_bijective_of_bot (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, fun y => ?_⟩) j
  · funext s
    have h1 := congrArg Subtype.val (congrFun h s)
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb] at h2
    exact sub_eq_zero.1 h2
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a₀ b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

end Abstract

section Concrete
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem ks_le_of_le {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) : KS q u 𝒱 ≤ KS q s 𝒱 := by
  rintro T ⟨⟨h1, h2⟩, hV⟩
  exact ⟨⟨le_bot_iff.1 (h1 ▸ T.pdPow_anti hus), h2⟩, hV⟩

theorem quoK_comm {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) (r : ℤ) (j : ℕ) (x : HdR q j) :
    ((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ r)).pull j (quoK q (KS q s 𝒱) r j x) =
      quoK q (KS q u 𝒱) r j x := by
  obtain ⟨z, hz, hx⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF (thA (smFun X q)))) j).1 x
  subst hx
  rfl

theorem quoK_bij_self {u : ℕ} (𝒱 : Set X.Opens) (j : ℕ) (h : Function.Bijective (resK q (KS q u 𝒱) j)) :
    Function.Bijective (quoK q (KS q u 𝒱) (u : ℤ) j) := by
  have hB := toSq_bijective_of_bot (sFil (KS q u 𝒱) 0) (sFil (KS q u 𝒱) (u : ℤ)) (fun T => T.obj.pdPow_zero)
    (fun T => by
      have h := T.property.1.1
      change T.obj.pdPow ((u : ℤ).toNat) = ⊥
      rw [Int.toNat_natCast]
      exact h) j
  exact hB.comp h

end Concrete

theorem quoK_bijective : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  intro hK K _ _ X q U s u hd hus 𝒱 h𝒱 j
  have h1 := quoK_bij_self q 𝒱 j (hK q U u hd 𝒱 h𝒱 j).1
  have h2 := _root_.GlobalTheory.CompanionTheory.PDTrunc.pull_incl_bijective (TF 1 s) 1 u (Or.inr ⟨s, hus, rfl⟩) 𝒱 (ks_le_of_le q hus 𝒱) 0 (u : ℤ) le_rfl j
  refine (Function.Bijective.of_comp_iff' h2 _).1 ?_
  have e : (((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ (u : ℤ))).pull j) ∘ (quoK q (KS q s 𝒱) (u : ℤ) j) =
      quoK q (KS q u 𝒱) (u : ℤ) j := funext (quoK_comm q hus 𝒱 (u : ℤ) j)
  exact (congrArg Function.Bijective e).mpr h1

end GlobalTheory.CompanionTheory.QuoK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel

theorem isNoetherianRing_Wm_one :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l],
      IsNoetherianRing (Wc.Wm l k 1) := by
  intro l _ k _ _ _
  unfold Wc.Wm
  infer_instance

end GlobalTheory.CompanionTheory.WittLevel
end

