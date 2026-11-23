module

public import Formalism.LocalToGlobal.Columns.Bundle0016
public import Formalism.LocalToGlobal.Columns.Bundle0045
public import Formalism.LocalToGlobal.Columns.ChainTwMain
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainTwFin
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Approx

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem tfVal_mem {u : 𝓞 E} {N : ℕ} (hu : u ∈ P.asIdeal ^ N) : P.valuation E (algebraMap (𝓞 E) E u) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem P u N).mpr hu

theorem tfApprox (a : E) (ha : P.valuation E a ≤ 1) (N : ℕ) : ∃ r : 𝓞 E, P.valuation E (a - algebraMap (𝓞 E) E r) ≤ WithZero.exp (-(N : ℤ)) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := by
    first
      | exact pow_ne_zero _ P.ne_bot
  obtain ⟨t, htP, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPN
  have hc : algebraMap E (P.adicCompletion E) a ∈ P.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  obtain ⟨r, hr⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local P
    (algebraMap E (P.adicCompletion E) a) hc t ht0
  refine ⟨r, ?_⟩
  rw [← map_sub] at hr
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hr
  exact hr.trans ((HeightOneSpectrum.intValuation_le_pow_iff_mem P t N).mpr htP)

end Approx

section Idx

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ)

def tfRed (g : ↥(GLint E n P)) : Fin n → Fin n → 𝓞 E ⧸ P.asIdeal ^ N := fun i j =>
  Ideal.Quotient.mk _ (tfApprox P _ (qsp_entry_int P g i j) N).choose

theorem tfRed_eq {g g' : ↥(GLint E n P)} (h : tfRed P N g = tfRed P N g') : lqPrinc P N ((g⁻¹ * g' : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  classical
  have hmat : ∀ x : ↥(GLint E n P), ((toGLm E n x.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      LinearMap.toMatrix' ((x.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) := fun x => rfl
  have hclose : ∀ l k, P.valuation E (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l k
    have hr := (tfApprox P _ (qsp_entry_int P g l k) N).choose_spec
    have hr' := (tfApprox P _ (qsp_entry_int P g' l k) N).choose_spec
    have hmk := congrFun (congrFun h l) k
    simp only [tfRed] at hmk
    have hrr := tfVal_mem P (Ideal.Quotient.eq.mp hmk)
    rw [map_sub] at hrr
    have e : ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
        ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k =
        (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
          algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
        (-(algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
          -(((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose)) := by ring
    rw [e]
    refine Valuation.map_add_le _ hr' (Valuation.map_add_le _ ?_ ?_)
    · rw [Valuation.map_neg]
      exact hrr
    · rw [Valuation.map_neg]
      exact hr
  have hM1 : ((toGLm E n (g⁻¹ * g').1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  have hM2 : ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one,
      Units.val_one]
  intro i j
  rw [← hmat (g⁻¹ * g'), hM1, ← hM2, ← Matrix.mul_sub, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul, Matrix.sub_apply]
  exact le_trans (mul_le_of_le_one_left' (qsp_entry_int P g⁻¹ i l)) (hclose l j)

theorem tfFinite_quot (hN : 0 < N) : Finite (𝓞 E ⧸ P.asIdeal ^ N) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := pow_ne_zero _ P.ne_bot
  first
    | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hPN)
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ hPN

theorem tfFinite_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → g ∈ H) :
    Finite (↥(GLint E n P) ⧸ H) := by
  classical
  haveI := tfFinite_quot P N hN
  let q : Set.range (tfRed P N) → (↥(GLint E n P) ⧸ H) := fun v => QuotientGroup.mk v.2.choose
  refine Finite.of_surjective q ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨⟨tfRed P N g, g, rfl⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    apply hH
    exact tfRed_eq P N (⟨tfRed P N g, g, rfl⟩ : Set.range (tfRed P N)).2.choose_spec

theorem tfRoot_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) (x : ↥H) :
    ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
  classical
  haveI := tfFinite_quot P N hN
  have key : ∀ k1 k2 : ℕ, k1 < k2 →
      tfRed P N ((x : ↥(GLint E n P)) ^ k1) = tfRed P N ((x : ↥(GLint E n P)) ^ k2) →
      ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
    intro k1 k2 hlt heq
    have hp := tfRed_eq P N heq
    have hpow : ((x : ↥(GLint E n P)) ^ k1)⁻¹ * (x : ↥(GLint E n P)) ^ k2 =
        (x : ↥(GLint E n P)) ^ (k2 - k1) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hpow] at hp
    obtain ⟨hmem, hlam⟩ := hH _ hp
    refine ⟨k2 - k1, by omega, ?_⟩
    have hx : (⟨(x : ↥(GLint E n P)) ^ (k2 - k1), hmem⟩ : ↥H) = x ^ (k2 - k1) := by
      apply Subtype.ext
      simp
    rw [← map_pow, ← hx, hlam]
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => tfRed P N ((x : ↥(GLint E n P)) ^ k))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key k1 k2 hlt heq
  · exact key k2 k1 hlt heq.symm

end Idx

section Pi

theorem tfPiChar {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    piChar H lam x = ∏ i, lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ := by
  simp only [piChar, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
  rfl

end Pi

section Fam

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q)

theorem thetaOpen_finIdx (h : ThetaOpen Θ) (P : Q) : Finite (↥(GLint E n P.1) ⧸ (Θ P).H) := by
  obtain ⟨N, hN, hg⟩ := h P
  exact tfFinite_of_princ P.1 N hN (Θ P).H (fun g hgp => (hg g hgp).1)

theorem thetaOpen_root (h : ThetaOpen Θ) (c : ↥Θ.grp) : ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : Kˣ) : K) ^ m = 1 := by
  classical
  have hP : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ ^ m = 1 := by
    intro P
    obtain ⟨N, hN, hg⟩ := h P
    exact tfRoot_of_princ P.1 N hN (Θ P).H (Θ P).lam hg _
  choose m hm0 hm using hP
  have key : (Θ.chr c) ^ (∏ P, m P) = 1 := by
    have hc : Θ.chr c = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ :=
      tfPiChar (fun P => (Θ P).H) (fun P => (Θ P).lam) c
    rw [hc, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun P _ => ?_
    obtain ⟨d, hd⟩ : m P ∣ ∏ Q, m Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ P)
    rw [hd, pow_mul, hm P, one_pow]
  refine ⟨∏ P, m P, Finset.prod_pos fun P _ => hm0 P, ?_⟩
  rw [← Units.val_pow_eq_pow_val, key, Units.val_one]

end Fam

section Tw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

end Tw

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def toTwistedEisensteinRanks (R : Ranks) : PI.TwistedEisensteinNonvanishing.Ranks :=
  { ord := R.ord, k := R.k, m := R.m, t := R.t, k_even := R.k_even, m_even := R.m_even, t_odd := R.t_odd, two_le_m := R.two_le_m,
    m_add_three_le_k := R.m_add_three_le_k, rank_add_five_le := R.rank_add_five_le, three_m_lt_t := R.three_m_lt_t,
    m_le_f := R.m_le_f, f_le_k := R.f_le_k, m_sq_le_N := R.m_sq_le_N }

section Br

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem doubleCosetDatum_psi_ok (G : ChGlob X R.m) (P : rowSG Pr sel mu)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) :
    PI.TwistedEisensteinNonvanishing.PsiOk (2 * (toTwistedEisensteinRanks R).m) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) := by
  refine ⟨fun x y hx hy => hadd x y hx hy, fun x hx => hint x hx, fun x hx => ?_⟩
  unfold twPsiQ
  rw [dite_eq_right]
  rintro ⟨b, hb, -⟩
  exact hx hb

theorem twistedMultiplier_ne_zero (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : twMuq Ch sel mu G (i + 1) P ≠ 0 := by
  unfold twMuq
  rw [if_neg hP]
  split_ifs
  · exact Units.ne_zero _
  · exact one_ne_zero

theorem squareRoot_norm_ne_zero (P : rowSG Pr sel mu) (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K)) :
    twSqrt (X := X) P.1 ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero] at hsq
  have : (qOf P.1 : X.K) ≠ 0 := by exact_mod_cast hq.ne_zero
  exact this hsq.symm

theorem firstUnfolding_eq_doubleCosetDatum (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (A' B' : ℕ) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    E1at Ch sel mu { twCst Ch sel mu G with A := A', B := B' } i P hal h =
      PI.TwistedEisensteinNonvanishing.TwistedEisensteinCoefficient (toTwistedEisensteinRanks R) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
        (resChar (mu : Chr X.F X.E X.K) P.1) A' B' i hal h := by
  unfold E1at omPhi muAt PhiAt
  simp only [twCst, if_neg hP]
  rfl

theorem doubleCosetDatum_hypotheses (H : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing) (G : ChGlob X R.m) {i : ℕ} (hi : i + 3 ≤ R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hu : ((Ideal.absNorm P.1.asIdeal : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K))
    (hal : AutY X R i) (h h' : AutY X R (i + 1)) (hbal : TwBdd (Pr := Pr) i P.1 hal) (hb : TwBdd (Pr := Pr) (i + 1) P.1 h)
    (hb' : TwBdd (Pr := Pr) (i + 1) P.1 h') (hdc : SameDC (Pr := Pr) true (i + 1) P.1 h h')
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h' := by
  have hL : ∀ j, lamYat (Pr := Pr) (R := R) j P.1 = LocE.lamY P.1 (qOf P.1) (R.N j) (cOf R j) 0 := fun j => by
    unfold lamYat; rw [if_neg hP]
  have hJ : ∀ j, Jat (Pr := Pr) (R := R) true j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := fun j => by
    unfold Jat; rw [if_neg hP]
  have bdd : ∀ j (g : AutY X R j), TwBdd (Pr := Pr) j P.1 g → PI.TwistedEisensteinNonvanishing.BddL (toTwistedEisensteinRanks R) P.1 j g := fun j g hg x hx => by
    have := hg x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨A₀, B₀, hAB⟩ := hne
  have := H X.E X.K (toTwistedEisensteinRanks R) P.1 hq hu (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
    (resChar (mu : Chr X.F X.E X.K) P.1) (doubleCosetDatum_psi_ok G P hadd hint) (squareRoot_norm_ne_zero P hq hsq) (twistedMultiplier_ne_zero G i P hP) i hi hal h h'
    (bdd i hal hbal) (bdd (i + 1) h hb) (bdd (i + 1) h' hb')
    (by obtain ⟨r, hr, κ, hκ, e⟩ := hdc; exact ⟨r, hr, κ, by rw [hJ] at hκ; exact hκ, e⟩)
    ⟨A₀, B₀, fun A' B' hA hB => by rw [← firstUnfolding_eq_doubleCosetDatum G i P hP]; exact hAB A' B' hA hB⟩
  obtain ⟨A₁, B₁, h1⟩ := this
  exact ⟨A₁, B₁, fun A' B' hA hB => by rw [firstUnfolding_eq_doubleCosetDatum G i P hP]; exact h1 A' B' hA hB⟩

theorem unfoldingNonvanishingDoubleCoset_holds (G : ChGlob X R.m) {m2 : ℕ} (hm : R.m = m2 + 2) (hK : TwCstQ (Pr := Pr) sel mu G) :
    UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h h' hbal hb hb' hs hne
  exact doubleCosetDatum_hypotheses _root_.TwistedEisensteinNonvanishing G (by omega) P hP hd.1 hd.2 (hK.psi_add P hP) (hK.psi_int P hP) (hK.sq_sq P hP)
    hal h h' hbal hb hb' hs hne

theorem twIdx_ok_closed (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have hK := twCstQ_of hd hz hs hxi
  have hc := twCst_ok hPr hCh h4 hK
  exact twistedIndex_firstUnfolding_ok hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (unfoldingNonvanishingDoubleCoset_holds G hm hK) (characterNonvanishing_holds hm hc)

end Br

end Formalism.L2.Col
end
end

