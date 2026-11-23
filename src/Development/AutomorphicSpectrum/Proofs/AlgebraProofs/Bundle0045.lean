module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullFlagpair
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0044
public import ReciprocityTheory.DualLattices.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SmulMemSpan

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaEquivariantFrobenius
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem alpha_comm_act : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) :=
  @PositivityTheory.HtPt.Cb.alpha_act

end GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPairBaseExtension
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) :=
  PositivityTheory.Xgn.t_pull_flagpair

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProduct
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.ROm

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) r =
      fun a => algebraMap R C (r * χ a) := by
    funext a; simp [Algebra.smul_def]
  rw [xIdeal, Submodule.mem_comap, this]

theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_left' (hv.map_le_one s)

theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self a))
    (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self b))

theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  let T : Submodule R C :=
    { carrier := {x | v x ≤ b}
      add_mem' := fun hx hy => v.map_add_le hx hy
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        change v (r • x) ≤ b
        rw [Algebra.smul_def, map_mul]
        exact (mul_le_of_le_one_left' (hv.map_le_one r)).trans hx }
  have : sqIdeal (Submodule.span R s) ≤ T.comap l := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, g', hg', rfl⟩
    have h1 : Submodule.span R s * Submodule.span R s ≤ T.comap l := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, a', ha', rfl⟩
      exact h a ha a' ha'
    exact h1 (Submodule.mul_mem_mul hg hg')
  exact fun g hg => this hg

variable [Fintype F] [DecidableEq F]

theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ]
    refine (mem_aug _ _).2 ⟨AA.mul_mem _ _ ih.1 hg.1, ?_⟩
    rw [Pi.mul_apply, ((mem_aug _ _).1 hg).2, mul_zero]

theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier :=
    (mem_aug _ _).2 ⟨(mem_x_ideal_iff _ _ _).1 hc, by simp [MulChar.map_zero]⟩
  refine Submodule.subset_span ⟨_, pow_mem_aug AA hg j, _, hg, ?_⟩
  funext a
  rw [← pow_succ, Pi.pow_apply, MulChar.pow_apply' _ (by omega), ← mul_pow, map_pow]

theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, g', hg', rfl⟩
  exact AA.mul_mem _ _ hg.1 hg'.1

omit [Fintype F] [DecidableEq F] in
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  refine ⟨finFunctionFinEquiv.symm ⟨m, h2⟩, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := finFunctionFinEquiv_apply (finFunctionFinEquiv.symm ⟨m, h2⟩)
    rw [Equiv.apply_symm_apply] at this
    simp [h] at this
    omega
  · rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]

theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end GlobalTheory.CompanionTheory.Ar.GR.ROm

open GlobalTheory.CompanionTheory.Ar.GR.ROm PositivityTheory.HtPt.Rb in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hf AA hst σ hσ c hc n
  haveI : IsDomain R := hv.hom_inj.isDomain
  have hp2 : 2 ≤ p := hpp.out.two_le
  have hf0 : 0 < f := Nat.pos_of_ne_zero (f_ne_zero hf)
  have hord : orderOf σ = p ^ f - 1 := (FundGen.main p C v R hv hp F f hf σ hσ).1
  obtain ⟨h0, -⟩ := exists_inv_card hv hp hf
  have hprin := eig_rank_one p C v R hv hp F f hf AA hst
  have hmono := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hf AA hst σ hσ c hc).2
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
  have hsq : ∀ n, (fun a => algebraMap R C (c n ^ p * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) := fun n => by
    have := pow_mem_sq AA (σ ^ p ^ n) (hc n ▸ Ideal.mem_span_singleton_self (c n)) hp2
    rwa [← pow_mul, ← pow_succ] at this
  have hdvd : ∀ n, c n ^ p ∈ Ideal.span {c (n + 1)} := fun n => by
    rw [← hc, mem_x_ideal_iff]
    exact sq_le AA (hsq n)
  have hper : ∀ n, σ ^ p ^ (n + f) = σ ^ p ^ n := fun n => by
    rw [pow_eq_pow_iff_modEq, hord, pow_add]
    have : p ^ f ≡ 1 [MOD (p ^ f - 1)] := ((Nat.modEq_iff_dvd' hq).2 dvd_rfl).symm
    simpa using this.mul_left (p ^ n)
  have hcarry := frobeniusChain_carry p f hp2 hf0 (fun n => v (algebraMap R C (c n)))
    (fun n => v_eq_of_span hv (by rw [← hc, ← hc, hper])) (fun n => hv.map_le_one _)
    (fun n => by simpa only [map_pow] using v_le_of_mem hv (hdvd n))
  choose c' hc'0 hc' using fun m : ℕ => (hprin (σ ^ m)).1
  have hdec := (r_decomp_relay p C v R hv hp F f hf AA hst σ hσ c' hc').1
  have hiff : ∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p} := by
    intro r
    constructor
    · intro hr
      rw [hdec] at hr
      have := sq_bound hv _ ((LinearMap.proj (R := R) (φ := fun _ : F => C) 1).comp
        (projL (σ ^ p ^ (n + 1)))) (v (algebraMap R C (c n)) ^ p) ?_ _ hr
      · rw [LinearMap.comp_apply, projL_apply, proj_eigen_self h0 _ _ (eig_fun _ r)] at this
        simp only [LinearMap.proj_apply, map_one, mul_one] at this
        rw [Ideal.mem_span_singleton]
        refine hv.dvd_of_le ?_
        simpa only [map_pow] using this
      · rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
        simp only [Finset.coe_Icc, Set.mem_Icc] at hm hm'
        have e : ((fun a : F => algebraMap R C (c' m * (σ ^ m) a)) *
            fun a : F => algebraMap R C (c' m' * (σ ^ m') a)) =
            fun a : F => algebraMap R C ((c' m * c' m') * (σ ^ (m + m')) a) := by
          funext a
          simp only [Pi.mul_apply, pow_add, MulChar.mul_apply, map_mul]; ring
        rw [LinearMap.comp_apply, projL_apply]
        simp only []
        rw [e]
        by_cases hχ : σ ^ p ^ (n + 1) = σ ^ (m + m')
        · rw [hχ, proj_eigen_self h0 _ _ (eig_fun _ _)]
          simp only [LinearMap.proj_apply, map_one, mul_one]
          obtain ⟨d, ⟨i, hi⟩, hd⟩ := digits (p := p) (f := f) hm.1 (by omega)
          obtain ⟨d', ⟨i', hi'⟩, hd'⟩ := digits (p := p) (f := f) hm'.1 (by omega)
          have e1 := hmono d ⟨i, hi⟩
          have e2 := hmono d' ⟨i', hi'⟩
          rw [hd, hc'] at e1
          rw [hd', hc'] at e2
          rw [map_mul, map_mul, v_eq_of_span hv e1, v_eq_of_span hv e2]
          have := hcarry (fun k => (d k : ℕ) + d' k) n ?_ ?_
          · simpa only [pow_add, Finset.prod_mul_distrib, map_prod, map_pow] using this
          · rw [Finset.sum_add_distrib]
            have a1 := Finset.single_le_sum (f := fun k => (d k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i)
            have a2 := Finset.single_le_sum (f := fun k => (d' k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i')
            omega
          · simp only [add_mul, Finset.sum_add_distrib, hd, hd']
            rw [← hord, ← pow_eq_pow_iff_modEq, hχ]
        · rw [proj_eigen_ne hχ _ (eig_fun _ _)]
          simp
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      convert Submodule.smul_mem _ s (hsq n) using 1
      funext a
      simp [Algebra.smul_def, map_mul, mul_assoc]
  refine ⟨hiff, ?_, fun δ hδ => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hdvd n)
    exact ⟨s, hs.symm⟩
  · have hne : c (n + 1) ≠ 0 := by
      intro h
      have := hc (n + 1)
      rw [hc', h, Ideal.span_singleton_zero, Ideal.span_singleton_eq_bot] at this
      exact hc'0 _ this
    have hg : (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈
        eig AA.carrier (σ ^ p ^ (n + 1)) :=
      ((hprin _).2 _).2 ⟨_, hc (n + 1) ▸ Ideal.mem_span_singleton_self _, rfl⟩
    have hsm : ∀ r : R, r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) =
        fun a => algebraMap R C (r * c (n + 1) * (σ ^ p ^ (n + 1)) a) := fun r => by
      funext a
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
    refine hasLen_quot v ((Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ ⟨_, hg⟩)) ?_ δ ?_
    · refine (Submodule.mkQ_surjective _).comp ?_
      rintro ⟨g, hg'⟩
      obtain ⟨r, hr, rfl⟩ := ((hprin _).2 _).1 hg'
      rw [hc] at hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      exact ⟨s, Subtype.ext (hsm s)⟩
    · ext r
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈ _ ↔ _
      rw [hsm, hiff, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        mul_dvd_mul_iff_right hne]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuation
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

lemma two_mul_sum_digit (p f : ℕ) (j : Fin f) :
    (∑ d : Fin f → Fin p, (d j : ℕ)) * 2 = p ^ f * (p - 1) := by
  let e : (Fin f → Fin p) ≃ (Fin f → Fin p) := Equiv.arrowCongr (Equiv.refl _) Fin.revPerm
  have h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ) :=
    e.sum_comp (fun d => (d j : ℕ))
  have h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1) := by
    intro d
    simp [e, Equiv.arrowCongr_apply, Fin.val_rev]
  simp only [h2] at h1
  rw [mul_two]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  have h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1 := by
    intro d; have := (d j).2; omega
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

lemma prod_digit_sq (p f : ℕ) (x : Fin f → NNReal) :
    (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2 = (∏ j, x j) ^ (p ^ f * (p - 1)) := by
  have key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1)) := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]
  calc (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2
      = (∏ j, ∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := by rw [Finset.prod_comm]
    _ = ∏ j, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := (Finset.prod_pow _ _ _).symm
    _ = ∏ j, x j ^ (p ^ f * (p - 1)) := Finset.prod_congr rfl (fun j _ => key j)
    _ = (∏ j, x j) ^ (p ^ f * (p - 1)) := Finset.prod_pow _ _ _

def num {p f : ℕ} (d : Fin f → Fin p) : ℕ := ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)

lemma num_eq {p f : ℕ} (d : Fin f → Fin p) : num d = (finFunctionFinEquiv d : ℕ) := by
  rw [num, finFunctionFinEquiv_apply]

lemma num_lt {p f : ℕ} (d : Fin f → Fin p) : num d < p ^ f := by
  rw [num_eq]; exact Fin.isLt _

lemma num_inj {p f : ℕ} {d e : Fin f → Fin p} (h : num d = num e) : d = e := by
  rw [num_eq, num_eq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h)

lemma num_surj {p f m : ℕ} (h : m < p ^ f) : ∃ d : Fin f → Fin p, num d = m :=
  ⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩

lemma num_ne_zero_iff {p f : ℕ} (hp : 0 < p) (d : Fin f → Fin p) :
    num d ≠ 0 ↔ ∃ n, (d n : ℕ) ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ n, (d n : ℕ) = 0 := fun n => by_contra (fun hn => hc ⟨n, hn⟩)
    apply h
    simp [num, hc']
  · rintro ⟨n, hn⟩ h
    apply hn
    rw [num] at h
    have h' := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (pow_ne_zero _ hp.ne')

lemma prod_Icc_num {M : Type} [CommMonoid M] {p f : ℕ} (hp : 0 < p) (g : ℕ → M)
    (G : (Fin f → Fin p) → M) (h0 : ∀ d, num d = 0 → G d = 1)
    (h1 : ∀ d, num d ≠ 0 → g (num d) = G d) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), g m = ∏ d, G d := by
  classical
  have hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d :=
    Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))
  rw [← hfilt]
  symm
  refine Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have := num_lt d
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    exact num_inj h
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨d, hd⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact (h1 d hd).symm

lemma mono_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F] {p f : ℕ}
    (hp : 0 < p) (σ : MulChar F R) (c : ℕ → R) (d : Fin f → Fin p) (hd : num d ≠ 0) (a : F) :
    ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) =
      algebraMap R C ((∏ n : Fin f, c n ^ (d n : ℕ)) * (σ ^ num d) a) := by
  have hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n :=
    fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a
  rw [MulChar.pow_apply' σ hd a]
  simp only [hpow']
  simp only [map_mul, map_pow, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]
  congr 2
  exact Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)

lemma digits_zero {p f : ℕ} (hp : 0 < p) {d : Fin f → Fin p} (hd : num d = 0) (n : Fin f) :
    (d n : ℕ) = 0 := by
  by_contra h
  exact (num_ne_zero_iff hp d).2 ⟨n, h⟩ hd

end GlobalTheory.CompanionTheory.Ar.GR.RankOneColen


open GlobalTheory.CompanionTheory.Ar.GR.RankOneColen in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hT := GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc
  obtain ⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧
      ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by
    refine ⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then
        ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ)
      else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩
    · intro m
      dsimp only
      by_cases h : m ≠ 0 ∧ m < p ^ f
      · rw [dite_eq_left h]
        have hd := Classical.choose_spec (num_surj h.2)
        have hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0 :=
          (num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)
        have e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2)) := by rw [hd]
        rw [e]
        exact hT.2 _ hne
      · rw [dite_eq_right h]
        exact (Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2
    · intro d hd
      dsimp only
      have h : num d ≠ 0 ∧ num d < p ^ f := ⟨hd, num_lt d⟩
      rw [dite_eq_left h]
      have := num_inj (Classical.choose_spec (num_surj h.2))
      rw [this]
  obtain ⟨hAug, hCar, hCol⟩ := r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'
  refine ⟨?_, ?_⟩
  · have hset : Set.range (fun (d : Fin f → Fin p) (a : F) =>
          ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) =
        insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1))) := by
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨d, rfl⟩
        by_cases h0 : num d = 0
        · left
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])
        · right
          refine ⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
      · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
        · refine ⟨fun _ => ⟨0, hp⟩, ?_⟩
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => pow_zero _)
        · obtain ⟨d, rfl⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
          have h0 : num d ≠ 0 := by omega
          refine ⟨d, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
    rw [hset, Submodule.span_insert, ← hAug, ← hCar]
  · intro cN hcN
    have huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m)) := by
      obtain ⟨B, hB, hBd⟩ := hcN
      obtain ⟨B', hB', hB'd⟩ := hCol
      obtain ⟨P, hPu, hP⟩ := AA.lat
      rw [← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB),
        valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]
    rw [huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m)))
      (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]
    · exact prod_digit_sq p f (fun n => v (algebraMap R C (c n)))
    · intro d hd
      exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])
    · intro d hd
      simp only [hc'd d hd, map_prod, map_pow]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelComparison
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamGood2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  exact @PositivityTheory.Xgn.t_fam_good2

end GlobalTheory.CompanionTheory.Ar.FamGood2
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormulaStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_one_series_p_formula : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p <;> assumption)
end

