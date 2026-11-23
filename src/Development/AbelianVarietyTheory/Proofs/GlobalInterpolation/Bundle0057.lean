module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_zpow_mul {P : HeightOneSpectrum (𝓞 E)} {e : ℤ} (he : 0 ≤ e) {a : E} (ha : IntAt P a) :
    IntAt P ((qOf P : E) ^ e * a) := by
  lift e to ℕ using he
  rw [zpow_natCast]
  exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul e ha

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) : IntV P (Loc.inX E n c z) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hz _
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  simp only [Loc.eN]
  split_ifs
  · exact intAt_one P
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_sum {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (h : ∀ i ∈ s, IntV P (f i)) : IntV P (∑ i ∈ s, f i) := by
  intro l
  rw [Finset.sum_apply]
  exact intAt_sum s _ (fun i hi => h i hi l)

theorem intV_glue {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) (i : Fin c) :
    IntV P (if i.1 = 0 then Loc.inX E n c z else 0) := by
  split_ifs
  · exact intV_inX hz
  · exact IntV.zero P

theorem decomp {n c : ℕ} (x : Fin (n + c) → E) :
    x = Loc.inX E n c (fun a => x (Fin.castAdd c a)) + ∑ i : Fin c, x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) := by
  funext l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) l
  · have h1 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
      intro i
      simp only [Loc.eN, Fin.val_castAdd]
      rw [if_neg]
      omega
    simp [inX_castAdd, Finset.sum_apply, h1]
  · have h2 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.natAdd n b) = if i = b then 1 else 0 := by
      intro i
      by_cases hib : i = b
      · subst hib
        simp [Loc.eN]
      · simp only [Loc.eN, Fin.val_natAdd, if_neg hib]
        rw [if_neg]
        intro h
        apply hib
        ext
        omega
    have h3 : Loc.inX E n c (fun a => x (Fin.castAdd c a)) (Fin.natAdd n b) = 0 := by
      rw [inX_apply, dite_eq_right (by simp)]
    simp [Finset.sum_apply, h2, h3]

theorem mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {e : Fin c → ℤ} (he : ∀ i, e i ≤ 0) {z : Sp E n}
    (hz : IntV P z) {x : Sp E (n + c)} (hx : IntV P x) : x ∈ nfLat P n c e z := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  set w : Sp E n := ∑ i : Fin c, x (Fin.natAdd n i) • (if i.1 = 0 then z else 0) with hw
  refine ⟨(fun a => x (Fin.castAdd c a)) - w, ?_, fun i => x (Fin.natAdd n i) * (qOf P : E) ^ (-e i), ?_, ?_⟩
  · rw [mem_stdAt_iff, sub_eq_add_neg]
    refine IntV.add (fun l => hx _) (IntV.neg ?_)
    refine intV_sum _ _ (fun i _ => IntV.smul (hx _) ?_)
    split_ifs
    · exact hz
    · exact IntV.zero P
  · intro i
    show IntAt P (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i))
    rw [mul_comm]
    exact intAt_zpow_mul (by linarith [he i]) (hx _)
  · have hs : ∀ i : Fin c, (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i)) • nfGen (qOf P) n c e z i =
        x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) +
          Loc.inX E n c (x (Fin.natAdd n i) • (if i.1 = 0 then z else 0)) := by
      intro i
      simp only [nfGen, smul_smul, mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one, smul_add]
      congr 1
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, ← map_sum, ← hw, map_sub]
    conv_lhs => rw [decomp x]
    abel

theorem smul_int_of_mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c j : ℕ} {e : Fin c → ℤ} (he : ∀ i, -(j : ℤ) ≤ e i)
    {z : Sp E n} (hz : IntV P z) {x : Sp E (n + c)} (hx : x ∈ nfLat P n c e z) : IntV P (((qOf P : E) ^ j) • x) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hx
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  rw [mem_stdAt_iff] at hl
  have key : ∀ i : Fin c, ((qOf P : E) ^ j) • (s i • nfGen (qOf P) n c e z i) =
      ((qOf P : E) ^ ((j : ℤ) + e i) * s i) •
        (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0) := by
    intro i
    simp only [nfGen, smul_smul]
    congr 1
    rw [zpow_add₀ hq, zpow_natCast]
    ring
  rw [smul_add, Finset.smul_sum, ← LinearMap.map_smul (Loc.inX E n c)]
  refine IntV.add (intV_inX (fun k => ?_)) (intV_sum _ _ (fun i _ => ?_))
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul j (hl k)
  · rw [key i]
    refine IntV.smul ?_ (IntV.add (intV_eN P _ _) (intV_glue hz i))
    exact intAt_zpow_mul (by linarith [he i]) (hs i)

end Lattice

theorem inclAt (X : Fields) (Pr : Primes X) (R : Ranks) : InclAt Pr R := by
  intro j P hP h k hNF hk
  obtain ⟨e, z, he, hz, himg⟩ := hNF
  have hk' : ∀ x, k x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ lamYat (Pr := Pr) (R := R) j P := hk
  rw [mem_stdAt_iff] at hz
  constructor
  · intro x hx
    have hxi : IntV P x := (mem_lamYat (R := R) hP x).1 hx
    have hmem : x ∈ nfLat P (R.N j) (cOf R j) e z := mem_nfLat (fun i => (he i).2) hz hxi
    rw [← himg] at hmem
    obtain ⟨y', hy', rfl⟩ := hmem
    refine ⟨k.symm y', ?_, ?_⟩
    · rw [← hk']
      simpa using hy'
    · simp [LinearEquiv.mul_apply]
  · intro x hx
    have h1 : h (k x) ∈ nfLat P (R.N j) (cOf R j) e z := by
      rw [← himg]
      exact ⟨k x, (hk' x).2 hx, rfl⟩
    have h2 := smul_int_of_mem_nfLat (fun i => (he i).1) hz h1
    rw [mem_lamYat hP]
    intro l
    have h3 := h2 l
    simpa [LinearEquiv.mul_apply] using h3

end GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartz
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz

variable {E : Type} [Field E] {n' c' n c : ℕ}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add (x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (x + y) = _root_.Formalism.L2.Col.Loc.chArg x + _root_.Formalism.L2.Col.Loc.chArg y := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.add_apply, _root_.GlobalTheory.QNormal.atN_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul (a : E) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (a • x) = a * _root_.Formalism.L2.Col.Loc.chArg x := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.smul_apply, _root_.GlobalTheory.QNormal.atN_smul, Finset.mul_sum]

def freeMap (u : Loc.FC n' c' n c → E) : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : Loc.IsFree n' n c l.1 s.1 then u ⟨(l, s), hf⟩ else 0)

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E) (a : E) :
    _root_.Formalism.L2.Col.Loc.xx1 xj (t + a • u) = _root_.Formalism.L2.Col.Loc.xx1 xj t + a • _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u := by
  unfold _root_.Formalism.L2.Col.Loc.xx1 _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap
  rw [← map_smul, ← map_add (f := _)]
  congr 1
  ext l s
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp

variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intAt_atN_of_intV {N : ℕ} {v : Fin N → E}
    (hv : _root_.GlobalTheory.QNormal.IntV P v) (i : ℕ) : _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.atN v i) := by
  unfold _root_.Formalism.L2.Col.Loc.atN
  split_ifs with h
  · exact hv ⟨i, h⟩
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intV_eN' (N s : ℕ) :
    _root_.GlobalTheory.QNormal.IntV P (_root_.Formalism.L2.Col.Loc.eN E N s) := by
  intro l
  dsimp only [_root_.Formalism.L2.Col.Loc.eN]
  split_ifs
  · exact _root_.GlobalTheory.QNormal.intAt_one P
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg
    {y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} (hy : _root_.GlobalTheory.QNormal.IntHom P y) :
    _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.chArg y) := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  exact _root_.GlobalTheory.QNormal.intAt_sum _ _ fun i _ =>
    intAt_atN_of_intV (hy _ (intV_eN' _ _)) _

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap {u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E}
    (hu : ∀ i, _root_.Formalism.L2.Col.IntAt P (u i)) : _root_.GlobalTheory.QNormal.IntHom P (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u) := by
  rw [_root_.GlobalTheory.QNormal.intHom_iff]
  intro s l
  simp only [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, Matrix.of_apply]
  split_ifs with hf
  · exact hu _
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type)
    [Field K] (P : HeightOneSpectrum (𝓞 E))
    (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : _root_.Formalism.L2.Col.Loc.SF E K (n' + c') (n + c)), N ≤ D →
    _root_.GlobalTheory.QNormal.CharTo P D psi → _root_.GlobalTheory.QNormal.HomBdd P N Psi →
    ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
      _root_.GlobalTheory.QNormal.FunBdd P N (_root_.GlobalTheory.QNormal.integrand psi Psi xj) ∧
      ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
        _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
  intro E _ _ K _ P n' c' n c psi D N Psi hND hpsi hPsi xj
  obtain ⟨hPsi1, hPsi2⟩ := hPsi
  obtain ⟨hpsi1, hpsi2⟩ := hpsi
  have hchar : ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
      _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := fun t ht => by
    rw [← _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul]
    exact _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg (hPsi1 _ ht)
  refine ⟨?_, hchar⟩
  unfold _root_.GlobalTheory.QNormal.FunBdd
  refine ⟨fun t ht i => ?_, fun t u hu => ?_⟩
  · have hne : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 := fun h => ht (by simp [_root_.GlobalTheory.QNormal.integrand, h])
    have hint := (_root_.GlobalTheory.QNormal.intHom_iff _).1 (hPsi1 _ hne)
    obtain ⟨⟨l, s⟩, hf⟩ := i
    have hentry := hint s l
    simpa only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      _root_.GlobalTheory.QNormal.linearMap_unfolding_apply_single, dif_pos hf] using hentry
  · have hfree := _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap (P := P) hu
    have hPsi_eq : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj (t + (_root_.Formalism.L2.Col.qOf P : E) ^ N • u)) = Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) := by
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul]
      exact hPsi2 _ _ hfree
    simp only [_root_.GlobalTheory.QNormal.integrand, hPsi_eq]
    by_cases h0 : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) = 0
    · simp [h0]
    · congr 1
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul, _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add,
        _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul, neg_add]
      have hx : _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ D * -_root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
        rw [mul_neg]
        exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono hND (hchar t h0))
      have hy : _root_.Formalism.L2.Col.IntAt P (-((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u))) :=
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul N
          (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg hfree))
      rw [hpsi1 _ _ hx (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul D hy), hpsi2 _ hy, mul_one]

end GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormThetaCharTermLe
section
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.EvenThetaBound

open Complex

theorem norm_thetaChar_term_le (a b : Fin 2) (τ : ℂ) (hτ : 1 / 2 ≤ τ.im) (n : ℤ) :
    ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ ≤
      Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) := by
  set r : ℝ := (n : ℝ) + ((a : ℕ) : ℝ) / 2 with hr
  have hw : (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2) =
      ((Real.pi * r ^ 2 : ℝ) : ℂ) * τ * I + ((Real.pi * r * ((b : ℕ) : ℝ) : ℝ) : ℂ) * I := by
    rw [hr]; push_cast; ring
  rw [hw, Complex.norm_exp, Real.exp_le_exp, add_re, mul_I_re, mul_I_re, im_ofReal_mul,
    ofReal_im, neg_zero, add_zero]
  have ha : ((a : ℕ) : ℝ) = 0 ∨ ((a : ℕ) : ℝ) = 1 := by
    rcases a with ⟨_ | _ | k, hk⟩
    · left; simp
    · right; simp
    · omega
  have hpi := Real.pi_pos
  have hr2 : (n : ℝ) ^ 2 / 2 - |(n : ℝ)| ≤ r ^ 2 / 2 := by
    have h1 : -|(n : ℝ)| ≤ (n : ℝ) := neg_abs_le _
    have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    rcases ha with h | h <;> rw [hr, h] <;> nlinarith
  have hr3 : r ^ 2 / 2 ≤ r ^ 2 * τ.im := by nlinarith [sq_nonneg r]
  have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (hr2.trans hr3) hpi.le]

theorem evenThetaConst_bounded :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀ := by
  have hs := summable_pow_mul_jacobiTheta₂_term_bound 1 (by norm_num : (0 : ℝ) < 1 / 2) 0
  simp only [pow_zero, one_mul] at hs
  have hs' : Summable (fun n : ℤ => Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|))) := by
    simpa [Int.cast_abs] using hs
  refine ⟨1 + ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)), ?_, ?_⟩
  · have : 0 ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
      tsum_nonneg fun n => (Real.exp_pos _).le
    linarith
  · intro a b τ hτ
    rw [JacobiThetaHalfCharacteristic.thetaChar_eq_tsum]
    have hb : Summable (fun n : ℤ => ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
        2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖) :=
      hs'.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaChar_term_le a b τ hτ)
    calc _ ≤ ∑' n : ℤ, ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
          2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ :=
          norm_tsum_le_tsum_norm hb
      _ ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
          hb.tsum_le_tsum (norm_thetaChar_term_le a b τ hτ) hs'
      _ ≤ _ := le_add_of_nonneg_left zero_le_one

end GlobalTheory.Glob.EvenThetaBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfolding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dite_eq_right (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dite_eq_left (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

end GlobalTheory.Proof.normal_form_bounds_unfolding
end
end

