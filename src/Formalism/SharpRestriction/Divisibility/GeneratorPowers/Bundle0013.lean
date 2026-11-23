module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FoldPermutation
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

variable {k : Type} [CommRing k] {d : ℕ}

def embP {n' n : ℕ} (e : Fin n' → Fin n) : Fin n' → Pt k n d := fun b => pt k d (e b)

theorem cz_embP {n' n : ℕ} (e : Fin n' → Fin n) : LogPf.CZ (embP (k := k) (d := d) e) := by
  intro j i
  simp [embP, pt]

theorem cz_ptz {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem pderiv_embP {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv (R := k) (e b, j) (ev (embP e) g) =
      ev (embP e) (pderiv (R := k) (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp

theorem pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv (R := k) (c, j) (ev (embP e) g) = 0 := by
  classical
  refine LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_
  rw [show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]
  intro h
  exact hc b (congrArg Prod.fst h)

theorem ev_ptz {n' n : ℕ} (e : Fin n' → Fin n) (b : Fin n') (X : PS k 2 d) :
    ev ![pt k d (e b), 0] X = ev (embP e) (ev ![pt k d b, 0] X) := by
  rw [LogPf.ev_ev (cz_embP e) (cz_ptz b)]
  congr 1
  funext q i
  fin_cases q
  · simp [LogPf.ev_X (cz_embP e), embP, pt]
  · simp [LogPf.ev_zero' (cz_embP e)]

theorem dofN_embP (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]

section Comm

def cB (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) : Fin n × Fin d → PS k n d := fun t =>
  if t.1 = b then ev (embP (fun _ : Fin 1 => b)) (WickVanishing.Nab.co G u ((0 : Fin 1), t.2)) else 0

theorem inj1 {n : ℕ} (b : Fin n) : Function.Injective (fun _ : Fin 1 => b) := by
  intro x y _
  exact Subsingleton.elim x y

theorem dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp

theorem cB_one (G : FGLaw k d) (u : Fin d → k) : cB G (0 : Fin 1) u = WickVanishing.Nab.co G u := by
  funext t
  have h1 : t.1 = 0 := Subsingleton.elim _ _
  have hp : (embP (k := k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  simp only [cB, if_pos h1, hp, LogPf.ev_pt]
  rw [show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]

theorem dofN_cB_ne (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp

theorem dofN_comm (G : FGLaw k d) {n : ℕ} (b b' : Fin n) (u v : Fin d → k) (g : PS k n d) :
    DofN G.F b u (DofN G.F b' v g) = DofN G.F b' v (DofN G.F b u g) := by
  classical
  rw [dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]
  have hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) =
      fun _ => (0 : PS k n d) := by
    funext t
    rw [← dofN_vf G b, ← dofN_vf G b']
    by_cases hb : b = b'
    · rw [← hb]
      have hE : ∀ (w : Fin d → k) (X : PS k 1 d),
          DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X) :=
        fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X
      unfold cB
      by_cases ht : t.1 = b
      · rw [if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1),
          dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]
      · rw [if_neg ht, if_neg ht]
        unfold DofN
        simp
    · rw [dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]
  rw [hz, WickVanishing.Nab.vf_zeroc]

end Comm

section Fold

variable {n' n : ℕ} (F : Fin d → PS k 2 d)
  (hF : ∀ (b b' : Fin n) (v v' : Fin d → k) (G : PS k n d), DofN F b v (DofN F b' v' G) = DofN F b' v' (DofN F b v G))
  (e : Fin n' → Fin n) (he : Function.Injective e) {ι ι' : Type} [Fintype ι] [Fintype ι']
  (cp : ι → Fin n) (u : ι → Fin d → k) (cp' : ι' → Fin n') (u' : ι' → Fin d → k) (φ : ι' → ι)
  (hφ : Function.Injective φ) (hcp : ∀ l, cp (φ l) = e (cp' l)) (hu : ∀ l, u (φ l) = u' l)
include hF he hφ hcp hu

end Fold

section Val

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (K : Type) [CommRing K]
  [Algebra ℚ K] [Algebra R K]

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem split_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hIdef
  set p' : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hp'def
  have hmax : p'.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : p' ≠ ⊥ := by
    rw [hp'def, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p' = I := by
    rw [hp'def, Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := normalizedFactors I with hMdef

  have hmem : ∀ P : Ideal (𝓞 E), P ∈ M ↔ P.IsPrime ∧ I ≤ P := fun P => Ideal.mem_normalizedFactors_iff hI0
  have hne : ∀ P ∈ M, P ≠ ⊥ := fun P hP h0 => hI0 (eq_bot_iff.2 (h0 ▸ ((hmem P).1 hP).2))
  have hlies : ∀ P ∈ M, P.LiesOver p' := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
    have hle : p' ≤ P.under ℤ := by
      rw [hp'def, Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact hIP (Ideal.subset_span rfl)
    have hnt : P.under ℤ ≠ ⊤ := by
      intro ht
      apply hPp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [ht]; trivial
      change algebraMap ℤ (𝓞 E) 1 ∈ P at h1
      rwa [map_one] at h1
    exact ⟨hmax.eq_of_le hnt hle⟩
  have hcard1 : M.toFinset.card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    have himg : HeightOneSpectrum.asIdeal '' {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} =
        (M.toFinset : Set (Ideal (𝓞 E))) := by
      ext P
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine (hmem _).2 ⟨v.isPrime, ?_⟩
        rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]
        exact hv
      · intro hP
        obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
        exact ⟨⟨P, hPp, hne P hP⟩, hIP (Ideal.subset_span rfl), rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]
  haveI := hmax
  have hsum := Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0
  have hfs : IsDedekindDomain.primesOverFinset p' (𝓞 E) = M.toFinset := by
    rw [IsDedekindDomain.primesOverFinset, hmap, hMdef, factors_eq_normalizedFactors]
  have hle : ∑ P ∈ M.toFinset, M.count P ≤ Module.finrank ℚ E := by
    rw [← hsum, hfs]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPM : P ∈ M := Multiset.mem_toFinset.1 hP
    haveI := hlies P hPM
    haveI : P.IsPrime := ((hmem P).1 hPM).1
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rw [hmap]; exact hI0) ‹P.IsPrime› (hne P hPM), hmap]
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg'_pos p' P)
  have hcard : M.card = ∑ P ∈ M.toFinset, M.count P := (Multiset.toFinset_sum_count_eq M).symm
  have h1 : M.toFinset.card ≤ M.card := Multiset.toFinset_card_le M
  have hMc : M.card = Module.finrank ℚ E := le_antisymm (hcard ▸ hle) (hcard1 ▸ h1)
  exact ⟨hMc, Multiset.toFinset_card_eq_card_iff_nodup.1 (hcard1.trans hMc.symm)⟩


open Formalism.BasicNotions in
theorem g_splits (D : D7) (i : Fin 2) :
    (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧
      (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup :=
  split_of_ncard (D.host.g_prime i) (D.nd.g_split i)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

namespace GaugeR

variable {R ι : Type} [CommRing R]

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  unfold Finsupp.prod
  have hpow : orig R ι ^ e.degree = ∏ i ∈ e.support, orig R ι ^ e i := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial ι R) ∈ orig R ι from Ideal.subset_span (Set.mem_range_self i)) _)

theorem mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → AddMonoidAlgebra.coeff p e = 0) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ (fun e he => ?_)
  have hn : n ≤ e.degree := by
    by_contra hlt
    push_neg at hlt
    exact (mem_support_iff.mp he) (h e hlt)
  exact Ideal.pow_le_pow_right hn (monomial_mem_orig_pow e _)

variable [Fintype ι] [DecidableEq ι]

theorem psJet_eq_mk (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → AddMonoidAlgebra.coeff p e = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]

theorem psJet_mul (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g := by
  have key : psJet m (f * g) = Ideal.Quotient.mk _ (psTrunc m f * psTrunc m g) := by
    refine psJet_eq_mk m _ _ (fun e he => ?_)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hd : x.1.degree + x.2.degree ≤ m := by
      rw [← map_add Finsupp.degree, hx']
      exact he
    rw [GermFun.coeff_psTrunc m f x.1 (by omega), GermFun.coeff_psTrunc m g x.2 (by omega)]
  rw [key, map_mul]
  rfl

theorem psJet_one (m : ℕ) : psJet m (1 : MvPowerSeries ι R) = 1 := by
  rw [psJet_eq_mk m 1 1 (fun e _ => by rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]; exact if_congr eq_comm rfl rfl), map_one]

theorem psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, psJet_mul, ih]

theorem aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [map_mul, map_finsuppProd, MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i => C (s i) * X i) p) e = (e.prod fun i k => s i ^ k) * AddMonoidAlgebra.coeff p e := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetSubstP_scale (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    Formalism.L2.Pj.jetSubstP m (fun i => C (s i) * X i) (psJet m f) =
      psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]

theorem jetAug_psJet (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self_apply]
  show AddMonoidAlgebra.coeff (psTrunc m f) 0 = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl

theorem exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m := by
  classical
  choose P hP using fun m => Ideal.Quotient.mk_surjective (ρ m)
  have hstep : ∀ m, P (m + 1) - P m ∈ orig R ι ^ (m + 1) := by
    intro m
    rw [← Ideal.Quotient.eq]
    have h1 := h m
    rw [← hP (m + 1), ← hP m] at h1
    exact h1
  have hcoef : ∀ n k (e : ι →₀ ℕ), e.degree ≤ n → AddMonoidAlgebra.coeff (P (n + k)) e = AddMonoidAlgebra.coeff (P n) e := by
    intro n k e he
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← sub_eq_zero, ← coeff_sub]
      exact GermFun.coeff_eq_zero_of_mem (hstep (n + k)) (by omega)
  refine ⟨fun e => AddMonoidAlgebra.coeff (P e.degree) e, fun m => ?_⟩
  rw [← hP m]
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  have h2 := hcoef e.degree (m - e.degree) e le_rfl
  rw [show e.degree + (m - e.degree) = m by omega] at h2
  rw [h2]
  rfl

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R]

theorem coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0

theorem psJet_subst_congr {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (D : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f g : MvPowerSeries σ R}
    (h : psJet D f = psJet D g) : psJet D (MvPowerSeries.subst a f) = psJet D (MvPowerSeries.subst a g) := by
  rw [psJet_subst D a ha f, psJet_subst D a ha g, h]

def psJetM {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℕ) : MvPowerSeries ι R →* Jet R ι D where
  toFun := psJet D
  map_one' := psJet_one D
  map_mul' := psJet_mul D

theorem psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b

theorem subst_exp {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
end
end

