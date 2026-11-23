module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PrincipalCompletion

variable {R : Type} [CommRing R] (a : R)

theorem fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton a

theorem eval_eq_zero_iff (n : ℕ) (x : AdicCompletion (Ideal.span {a}) R) :
    AdicCompletion.eval (Ideal.span {a}) R n x = 0 ↔
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ n ∣ x := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (fg a),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
      (AdicCompletion (Ideal.span {a}) R) := by
  have h := AdicCompletion.isAdicComplete (M := R) (fg a)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {a}) R),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (x : AdicCompletion (Ideal.span {a}) R) (r : ℕ) :
    ∃ (s : R) (z : AdicCompletion (Ideal.span {a}) R),
      x = algebraMap R _ s + (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {a}) R r x)
  have : AdicCompletion.eval (Ideal.span {a}) R r (x - algebraMap R _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff a r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : R) (r : ℕ) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ r ∣ algebraMap R _ s ↔ a ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {a}) R r (algebraMap R _ s) = Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem torsionFree (ha : ∀ s : R, a * s = 0 → s = 0) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : algebraMap R (AdicCompletion (Ideal.span {a}) R) a * x = 0) : x = 0 := by
  refine AdicCompletion.ext fun n => ?_
  change AdicCompletion.eval (Ideal.span {a}) R n x = 0
  rw [eval_eq_zero_iff]
  obtain ⟨s, z, rfl⟩ := dense a x n
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [dvd_iff]
  have h1 : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ (n + 1) ∣
      algebraMap R _ (a * s) := ⟨-z, by rw [map_mul]; linear_combination hx⟩
  obtain ⟨t, ht⟩ := (dvd_iff a _ _).1 h1
  exact ⟨t, sub_eq_zero.1 (ha _ (by linear_combination ht))⟩

theorem basic_of_equiv_pt (p : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (hp : ∀ s : R, (p : R) * s = 0 → s = 0)
    (e : A ≃+* AdicCompletion (Ideal.span {(p : R)}) R)
    (he : ∀ s, e (algebraMap R A s) = algebraMap R _ s) :
    IsAdicComplete (Ideal.span {(p : A)}) A ∧
    (∀ x : A, (p : A) * x = 0 → x = 0) ∧
    (∀ (x : A) (r : ℕ), ∃ (s : R) (z : A), x = algebraMap R A s + (p : A) ^ r * z) ∧
    ∀ (s : R) (r : ℕ), (p : A) ^ r ∣ algebraMap R A s ↔ (p : R) ^ r ∣ s := by
  have hpe : e (p : A) = algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) (p : R) := by
    rw [map_natCast, map_natCast]
  refine ⟨?_, fun x hx => ?_, fun x r => ?_, fun s r => ?_⟩
  · have h := complete (p : R)
    rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton, hpe]
    exact h
  · apply e.injective
    rw [map_zero]
    apply torsionFree _ hp
    rw [← hpe, ← map_mul, hx, map_zero]
  · obtain ⟨s, z, hz⟩ := dense (p : R) (e x) r
    refine ⟨s, e.symm z, e.injective ?_⟩
    rw [map_add (f := _), map_mul, map_pow, he, hpe, RingEquiv.apply_symm_apply]
    exact hz
  · rw [← dvd_iff (p : R) s r, ← hpe, ← he, ← map_pow, map_dvd_iff]

end GlobalTheory.PrincipalCompletion

namespace GlobalTheory.MemLoc

theorem acris0_torsionFree (l : ℕ) [Fact l.Prime] (s : Per.Acris0 l)
    (hs : (l : Per.Acris0 l) * s = 0) : s = 0 := by
  have hu : IsUnit (l : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) (l : Per.Ainf l)
    rwa [map_natCast] at this
  have h : (l : Per.AinfP l) * (s : Per.AinfP l) = 0 := by
    simpa using congrArg Subtype.val hs
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h)

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ (∀ (x : Per.Acris l) (r : ℕ), ∃ (s : Per.Acris0 l) (z : Per.Acris l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z) ∧ ∀ (s : Per.Acris0 l) (r : ℕ), (l : Per.Acris l) ^ r ∣ algebraMap (Per.Acris0 l) (Per.Acris l) s ↔ (l : Per.Acris0 l) ^ r ∣ s :=
  fun l _ => by
    obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
    exact GlobalTheory.PrincipalCompletion.basic_of_equiv_pt l (Per.Acris0 l) (Per.Acris l)
      (acris0_torsionFree l) e he

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ainf_isDomain_and_injective : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧
    Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  intro l _
  have : IsDomain (Per.Fl l) := inferInstance
  have h : IsDomain (Per.Ainf l) := inferInstance
  have hp : (l : Per.Ainf l) ≠ 0 := WittVector.p_nonzero l _
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hp
  exact ⟨h, IsLocalization.isDomain_of_le_nonZeroDivisors (Per.AinfP l) hle, IsLocalization.injective _ hle⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutant
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_tau_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  intro L _ _ _ n a ι _ _ b P hA τ v hv w
  classical
  have hS := _root_.GlobalTheory.AlgWtHW.span_ratPt_orbit L n a ι b P hA v hv w
  refine Submodule.span_mono ?_ hS
  rintro x ⟨γ₀, hγ, rfl⟩
  obtain ⟨_, hmul⟩ := _root_.GlobalTheory.AlgWtMul.evM_mul L n a ι b P hA
  set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef
  have hBv : B.val = γ₀.val.map τ := rfl
  set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
    if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef
  have hU := isUPt_ratPt γ₀ hγ
  have hR : IsUPt R := by
    intro σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, conj_conj]
      simp only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]
    · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', conj_conj]))
        · exact h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))
      simp only [R, if_neg h, if_neg h']
      exact hU σ
  have hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    exact hU τ
  have hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ := by
    funext σ
    have hne := conjugate_ne_self τ
    by_cases h1 : σ = τ
    · subst h1
      simp [tauPt, R, hBv, ratPt]
    · by_cases h2 : σ = ComplexEmbedding.conjugate τ
      · subst h2
        simp only [tauPt, if_neg h1, if_true, R, or_true, mul_one]
        rw [hinv, Matrix.transpose_transpose]
      · simp [tauPt, R, h1, h2]
  have hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ) := by
    intro A
    funext σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · simp [R, h]
    · have h1 : σ ≠ τ := fun e => h (Or.inl e)
      have h2 : σ ≠ ComplexEmbedding.conjugate τ := fun e => h (Or.inr e)
      simp [tauPt, h1, h2]
  refine ⟨B, evM P (upt R), ?_, ?_⟩
  · intro A
    rw [evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]
  · rw [hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
open Polynomial

namespace GlobalTheory.AxLemma

section General
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_taylor_coeff_le (T : Finset K) (x : K) (r : ℝ) (hr : 0 ≤ r) (h : ∀ z ∈ T, ‖z - x‖ ≤ r)
    (q : ℕ) (hq : q ≤ T.card) :
    ‖(hasseDeriv q (∏ z ∈ T, (X - C z))).eval x‖ ≤ r ^ (T.card - q) := by
  rw [← taylor_coeff]
  have h1 : taylor x (∏ z ∈ T, (X - C z)) = ∏ z ∈ T, (X + C (x - z)) := by
    rw [taylor_apply, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun z _ => ?_
    simp only [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [h1, Finset.prod_X_add_C_coeff T _ hq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  rw [norm_prod, ← ht.2, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun z hz => ?_
  rw [norm_sub_rev]
  exact h z (ht.1 hz)

omit [IsUltrametricDist K] in
theorem exists_root_near [IsAlgClosed K] (p : K[X]) (hp : 0 < p.natDegree) (x : K) :
    ∃ b ∈ p.roots, ‖p.leadingCoeff‖ * ‖b - x‖ ^ p.natDegree ≤ ‖p.eval x‖ := by
  first
  | exact @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | (apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le ..)

end General

variable {l : ℕ} [Fact l.Prime]

theorem norm_gal' (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := (spectralNorm_eq_of_equiv g x).symm

theorem one_le_mul_norm_choose (n q : ℕ) (hn : 0 < n) (hq : q ≤ n) :
    1 ≤ (n : ℝ) * ‖((n.choose q : ℕ) : Om l)‖ := by
  have hl : l.Prime := Fact.out
  have h0 : n.choose q ≠ 0 := (Nat.choose_pos hq).ne'
  have h1 : ((n.choose q : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) ((n.choose q : ℕ) : ℚ_[l]) := by
    rw [map_natCast]
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0),
    Padic.valuation_natCast, zpow_neg, zpow_natCast]
  have h2 := Nat.pow_factorization_choose_le (p := l) (k := q) hn
  rw [Nat.factorization_def _ hl] at h2
  have h3 : (0 : ℝ) < (l : ℝ) ^ multiplicity l (n.choose q) := by
    have := hl.pos
    positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h3, one_mul]
  exact_mod_cast h2

noncomputable def cst (k : ℕ) : ℝ := (2 : ℝ) ^ ((4 : ℝ) - (2 * k + 4) / 2 ^ k)

noncomputable def loss (k : ℕ) : ℝ := (2 : ℝ) ^ (((k : ℝ) + 1) / 2 ^ k)

theorem cst_succ (k : ℕ) : cst (k + 1) = cst k * loss k := by
  unfold cst loss
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  field_simp
  ring

theorem one_le_loss (k : ℕ) : 1 ≤ loss k :=
  Real.one_le_rpow (by norm_num) (by positivity)

theorem loss_pow (k : ℕ) : loss k ^ (2 ^ k) = 2 ^ (k + 1) := by
  unfold loss
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast (2 : ℝ) (k + 1)]
  congr 1
  push_cast
  field_simp

theorem one_le_cst (k : ℕ) : 1 ≤ cst k := by
  induction k with
  | zero => simp [cst]
  | succ k ih => rw [cst_succ]; exact one_le_mul_of_one_le_of_one_le ih (one_le_loss k)

theorem cst_le (k : ℕ) : cst k ≤ 16 := by
  unfold cst
  have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
  rw [this]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (2 * k + 4) / 2 ^ k := by positivity
  linarith

theorem ax_step (H : Subgroup (GQ l)) (k : ℕ) : ∀ (x : Om l) (r : ℝ) (S : Finset (Om l)),
    (∀ g ∈ H, g x ∈ S) → S.card ≤ 2 ^ k → (∀ g ∈ H, ‖g x - x‖ ≤ r) →
    ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ cst k * r := by
  classical
  induction k with
  | zero =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    refine ⟨x, fun g hg => ?_, ?_⟩
    · have hx : x ∈ S := by simpa using hS 1 H.one_mem
      exact Finset.card_le_one.1 (by simpa using hc) _ (hS g hg) _ hx
    · have := one_le_cst 0
      rw [sub_self, norm_zero]; positivity
  | succ k ih =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    have hc1 := one_le_cst k
    have hl1 := one_le_loss k
    set T := S.filter (fun z => ∃ g ∈ H, g x = z) with hT
    have hTm : ∀ z, z ∈ T ↔ ∃ g ∈ H, g x = z := by
      intro z
      rw [hT, Finset.mem_filter]
      exact ⟨fun h => h.2, fun ⟨g, hg, h⟩ => ⟨h ▸ hS g hg, g, hg, h⟩⟩
    have hTc : T.card ≤ 2 ^ (k + 1) := (Finset.card_filter_le _ _).trans hc
    by_cases hk : T.card ≤ 2 ^ k
    · obtain ⟨y, hy, hxy⟩ := ih x r T (fun g hg => (hTm _).2 ⟨g, hg, rfl⟩) hk hr
      refine ⟨y, hy, hxy.trans ?_⟩
      rw [cst_succ]
      refine mul_le_mul_of_nonneg_right ?_ hr0
      nlinarith
    push Not at hk
    set f : (Om l)[X] := ∏ z ∈ T, (X - C z) with hf
    set q := T.card - 2 ^ k with hq
    have hq1 : T.card - q = 2 ^ k := by omega
    have hfm : f.Monic := monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z
    have hfd : f.natDegree = T.card := by
      rw [hf, natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]; simp
    have hfg : ∀ g ∈ H, f.map (g : Om l →+* Om l) = f := by
      intro g hg
      rw [hf, Polynomial.map_prod]
      refine Finset.prod_bij (fun z _ => g z) ?_ ?_ ?_ ?_
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        exact (hTm _).2 ⟨g * g', H.mul_mem hg hg', rfl⟩
      · intro a _ b _ h
        exact g.injective h
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        refine ⟨(g⁻¹ * g') x, (hTm _).2 ⟨_, H.mul_mem (H.inv_mem hg) hg', rfl⟩, ?_⟩
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
      · intro z _
        simp
    set p := hasseDeriv q f with hp
    have hpd : p.natDegree = 2 ^ k := by rw [hp, natDegree_hasseDeriv, hfd, hq1]
    have hpl : p.leadingCoeff = ((T.card.choose q : ℕ) : Om l) := by
      have h2 : 2 ^ k + q = T.card := by omega
      rw [leadingCoeff, hpd, hp, hasseDeriv_coeff, h2]
      conv_lhs => rw [← hfd, hfm.coeff_natDegree, hfd]
      rw [mul_one]
    have hpg : ∀ g ∈ H, p.map (g : Om l →+* Om l) = p := by
      intro g hg
      ext n
      have := congrArg (fun u : (Om l)[X] => u.coeff (n + q)) (hfg g hg)
      simp only [coeff_map] at this
      rw [coeff_map, hp, hasseDeriv_coeff, map_mul, map_natCast, this]
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hpd
      exact (pow_pos two_pos k).ne hpd
    obtain ⟨b, hb, hbx⟩ := exists_root_near p (by rw [hpd]; positivity) x
    have hev := norm_taylor_coeff_le T x r hr0 (fun z hz => by
      obtain ⟨g, hg, rfl⟩ := (hTm z).1 hz
      exact hr g hg) q (by omega)
    rw [← hf, ← hp, hq1] at hev
    rw [hpd, hpl] at hbx
    have hch := one_le_mul_norm_choose (l := l) T.card q (by omega) (by omega)
    have hbr : ‖b - x‖ ≤ loss k * r := by
      refine le_of_pow_le_pow_left₀ (pow_pos two_pos k).ne' (by positivity) ?_
      rw [mul_pow, loss_pow]
      have h1 : (T.card : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hTc
      have h2 : 0 ≤ ‖b - x‖ ^ 2 ^ k := by positivity
      have h3 : (0 : ℝ) ≤ T.card := by positivity
      calc ‖b - x‖ ^ 2 ^ k ≤ (T.card * ‖((T.card.choose q : ℕ) : Om l)‖) * ‖b - x‖ ^ 2 ^ k :=
            le_mul_of_one_le_left h2 hch
        _ ≤ T.card * r ^ 2 ^ k := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbx.trans hev) h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hrr : r ≤ loss k * r := le_mul_of_one_le_left hr0 hl1
    have hgb : ∀ g ∈ H, ‖g b - b‖ ≤ loss k * r := by
      intro g hg
      have e : g b - b = g (b - x) + ((g x - x) + (x - b)) := by rw [map_sub]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · rw [norm_gal']; exact hbr
      · exact (hr g hg).trans hrr
      · rw [norm_sub_rev]; exact hbr
    obtain ⟨y, hy, hby⟩ := ih b (loss k * r) p.roots.toFinset (fun g hg => by
      rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
      have h0 : p.eval b = 0 := (mem_roots hp0).1 hb
      have h1 := eval_map_apply (g : Om l →+* Om l) (p := p) b
      rw [hpg g hg, h0, map_zero] at h1
      exact h1)
      ((Multiset.toFinset_card_le _).trans ((card_roots' p).trans hpd.le)) hgb
    refine ⟨y, hy, ?_⟩
    have e : x - y = (x - b) + (b - y) := by ring
    rw [e, cst_succ, mul_assoc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hby)
    rw [norm_sub_rev]
    exact hbr.trans (le_mul_of_one_le_left (by positivity) hc1)

theorem ax_lemma : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ),
    (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  classical
  intro l _
  refine ⟨16, by norm_num, fun H x r hr => ?_⟩
  have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set S := ((minpoly ℚ_[l] x).aroots (Om l)).toFinset with hS
  obtain ⟨y, hy, hxy⟩ := ax_step H S.card x r S (fun g _ => by
    rw [hS, Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]) Nat.lt_two_pow_self.le hr
  exact ⟨y, hy, hxy.trans (mul_le_mul_of_nonneg_right (cst_le _) hr0)⟩

end GlobalTheory.AxLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_eq_mk_rootT {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (n : ℕ) :
    PreTilt.coeff n e = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) := by
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e
  rw [zero_add] at h3
  rw [← h3, ← h2]
  rfl

theorem eps_coeff : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (n : ℕ),
    PreTilt.coeff n C.ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT C.ε n) :=
  fun _ _ C n => coeff_eq_mk_rootT C.ε n

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffGaloisTilt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_galois_tilt (l : ℕ) [Fact l.Prime] (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : PadicComplex l) = Per.σC g (y : PadicComplex l) ∧
      PreTilt.coeff n (Per.σF g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' :=
  ⟨Per.σO g y, GlobalTheory.RingIface.sigO_coe (l := l) g y,
    GlobalTheory.AdicMaps.coeff_galois l g x n y h⟩

end GlobalTheory.MemLoc
end

