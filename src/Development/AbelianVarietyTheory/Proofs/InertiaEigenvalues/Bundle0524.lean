module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

theorem psi_alg_pt (a : Per.Ainf l) : psi bk (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

theorem gamma_acris0 (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (s : Per.Acris0 l) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      psi bk (s : Per.AinfP l) := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (a : Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a))
    (hy : C.j (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) ∈ Per.FilP l m) :
    ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) =
      ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) +
      ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add (f := _), map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add (f := _), map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

theorem acris_dense {l : ℕ} [Fact l.Prime] (y : Per.Acris l) (r : ℕ) :
    ∃ (s : Per.Acris0 l) (z : Per.Acris l),
      y = algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]
  exact h

theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l) (w : Per.AinfP l)
    (hw : ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a =
        algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add (f := _), gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApproxStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O), (∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) → toOB l O x ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | exact GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | (intros; apply GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.Adm4Tab

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty :=
  by apply _root_.UpperTheory.Reformulated.B.Qk8.exists_place <;> assumption

theorem sumOver_const (D : D7) (l : ℕ) (hl : l ≠ 0) (k : ℝ) :
    TwistedPlaces.sumOver D l (fun _ => k) = ((placesOver D.host.E l).ncard : ℝ) * k := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.sum_const, Set.ncard_eq_toFinset_card _ hf,
    nsmul_eq_mul]

theorem sumOver_mono (D : D7) (l : ℕ) (hl : l ≠ 0) {f g : HeightOneSpectrum (𝓞 D.host.E) → ℝ}
    (h : ∀ lam, f lam ≤ g lam) : TwistedPlaces.sumOver D l f ≤ TwistedPlaces.sumOver D l g := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  exact Finset.sum_le_sum fun lam _ => h lam

theorem le_supZ {D : D7} (i : D.nd.Loc) (f : D.nd.X i → ℝ) {π : D.nd.X i} (hπ : π ∈ D.nd.Zgood i) :
    f π ≤ KillingConditions.supZ i f := by
  unfold KillingConditions.supZ
  rw [dite_eq_left ⟨π, hπ⟩]
  exact Finset.le_sup' f hπ

end GlobalTheory.NLink.Adm4Tab


open GlobalTheory.NLink.Adm4Tab in
theorem GlobalTheory.NLink.admissible_table_of_conclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i,
      Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  intro D L P X C tf hC h23 i hi hg π hπ
  have key : ∀ b, Bd X.ρ i π b → b ≤ TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i →
      (D.nd.vcc i π : ℝ) ≤ (tab L X tf C).s i π + TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + (tab L X tf C).BB i + TwistedPlaces.epsL (D.nd.l i) := by
    intro b hb hle
    unfold Bd at hb
    have hs : (tab L X tf C).s i π = (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) := rfl
    rw [hs]
    linarith
  have hl0 : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hq3 : D.host.q ≠ 3 := D.host.q_ne_three
  have hd3 : D.host.d ≠ 3 := by have := D.host.hyp.2.2.2.1; omega
  have hzero : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
    rw [sumOver_const D _ hl0, mul_zero]
  by_cases h2 : D.nd.l i ∈ D.host.small
  · apply key _ (h23 i hi (Or.inl h2) π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    rw [hlen, hzero, hBB, zero_add]
  by_cases h3 : D.nd.l i = 3
  · apply key _ (h23 i hi (Or.inr h3) π hπ)
    have hBB : (tab L X tf C).BB i = 0 := by
      have hq : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by
        rw [h3]; rintro (h | h) <;> [exact hq3 h.symm; exact hd3 h.symm]
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg hq, if_neg hR]
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    rw [hBB, hlen, h3, sumOver_const D 3 (by norm_num)]
    have hf3 := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
    have hpos : 0 < (placesOver D.host.E 3).ncard :=
      (Set.ncard_pos hf3).2 (placesOver_nonempty D.host.E 3 Nat.prime_three)
    have hpos' : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel₀ _ hpos', add_zero]
  by_cases hqd : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d
  · apply key _ (hC.ram i hi hqd π hπ)
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hqd
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, if_neg h2, if_pos hqd]
    rw [hlen, hzero, hBB, zero_add]
  by_cases hR : KillingConditions.RangeAD L X.exc (D.nd.l i)
  · have hm := hC.mid i hi hg hR π hπ
    have hb : Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) + X.errorBoundHub i π) := by
      unfold Bd
      linarith
    apply key _ hb
    have hlen : (tab L X tf C).len i = KillingConditions.lenR X.len0 i := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_pos hR]
    have hBB : (tab L X tf C).BB i = KillingConditions.supZ i (X.errorBoundHub i) := by
      simp only [tab, if_neg h2, if_neg hqd, if_pos hR]
    rw [hlen, hBB]
    have h1 : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) ≤ TwistedPlaces.sumOver D (D.nd.l i) (KillingConditions.lenR X.len0 i) :=
      sumOver_mono D _ hl0 fun lam => le_supZ i (fun π => X.len0 i π lam) hπ
    have h2' : X.errorBoundHub i π ≤ KillingConditions.supZ i (X.errorBoundHub i) := le_supZ i (X.errorBoundHub i) hπ
    linarith
  · have hlt : TwistedPlaces.lStar L < (D.nd.l i : ℝ) ∧ D.nd.l i ∉ X.exc := by
      by_contra hc
      exact hR ⟨fun h => h.elim h2 h3, hqd, hc⟩
    apply key _ (hC.large i hi hlt.1 hg hlt.2 π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = 0 := by
      simp only [tab, if_neg h2, if_neg hqd, if_neg hR]
    rw [hlen, hzero, hBB, add_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeriesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) sA j → ∀ (x y : A) (f g : bk.DS bk.ρ₀), g ≠ 0 → y ≠ 0 → toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f → ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  first | exact @GlobalTheory.BSP.linDisjoint_disc | exact GlobalTheory.BSP.linDisjoint_disc | (intros; apply GlobalTheory.BSP.linDisjoint_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  first | exact @GlobalTheory.AmbBlockDecomp.main | exact GlobalTheory.AmbBlockDecomp.main | (intros; apply GlobalTheory.AmbBlockDecomp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisCoboundaryEventuallyMemPrimePowLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  first | exact @GlobalTheory.CocycleCont.cont_at_one | exact GlobalTheory.CocycleCont.cont_at_one | (intros; apply GlobalTheory.CocycleCont.cont_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvPush

theorem c_mem_of_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (L : Ideal S) (i : ι) {x : A} (hx : x ∈ L.map s) : TB.c i x ∈ L := by
  have key : ∀ a : A, TB.c i (a * x) ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      rw [mul_comm, TB.c_mul]
      exact L.mul_mem_right _ hj
    | zero => intro a; rw [mul_zero, map_zero]; exact L.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem coeff_map {S A S' A' ι : Type} [CommRing S] [CommRing A] [CommRing S'] [CommRing A'] {s : S →+* A}
    {s' : S' →+* A'} {I : Ideal S} {I' : Ideal S'} (TB : TopBasis s I ι) (TB' : TopBasis s' I' ι) (g : S →+* S')
    (qf : A →+* A') (hq : ∀ y, qf (s y) = s' (g y)) (hb : ∀ i, qf (TB.b i) = TB'.b i) (hI : I.map g ≤ I')
    (hH : IsHausdorff I' S') (x : A) (α : ι) : TB'.c α (qf x) = g (TB.c α x) := by
  classical
  refine sub_eq_zero.1 (hH.haus _ fun n => SModEq.zero.2 ((Ideal.mul_top _).ge ?_))
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset ∪ {α} → TB.c i x ∈ I ^ n := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 h))
  have hm : qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i) ∈ (I' ^ n).map s' := by
    have h1 := Ideal.mem_map_of_mem qf (TB.approx x n _ hF)
    rw [Ideal.map_map, show qf.comp s = s'.comp g from RingHom.ext hq, ← Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.map_mono (Ideal.pow_right_mono hI n) h1
  have hc := c_mem_of_mem_map TB' _ α hm
  have e : TB'.c α (qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i)) =
      TB'.c α (qf x) - g (TB.c α x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, Finset.sum_eq_single α]
    · rw [map_mul, hq, hb, TB'.c_mul, TB'.c_self, mul_one]
    · intro i _ hi
      rw [map_mul, hq, hb, TB'.c_mul, TB'.c_ne α i (Ne.symm hi), mul_zero]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self α)) h
  rwa [e] at hc

end GlobalTheory.BSP.EnvPush


open GlobalTheory.BSP.EnvPush in
theorem GlobalTheory.BSP.envPush_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En An q hl hr x hx
  have hql : ∀ y : bk.prism.A, q.f (En.inl.f y) = An.inl.f (bk.ι.f y) := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hl
  have hqr : ∀ y : bk.prism.A, q.f (En.inr.f y) = An.inr.f y := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hr

  have hw : q.f En.w = An.w := by
    have e1 : q.f (En.inr.f (bk.toP X)) = An.inr.f (bk.toP X) := hqr _
    have e2 : En.inr.f (bk.toP X) = En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w := En.w_eq
    have e3 : An.inr.f (bk.toP X) = An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * An.w :=
      An.w_eq
    have e4 : q.f (En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w) =
        An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * q.f En.w :=
      (q.f.map_add _ _).trans (congrArg₂ (· + ·) (hql _) ((q.f.map_mul _ _).trans (congrArg (· * q.f En.w) (hql _))))
    have e5 := add_left_cancel (e4.symm.trans ((congrArg q.f e2).symm.trans (e1.trans e3)))
    have key : ∀ (b u v : An.Q.A), b ∈ nonZeroDivisors An.Q.A → b * u = b * v → u = v := fun b u v hb h =>
      sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).1 (by rw [mul_sub, h, sub_self]))
    have hnz : An.inl.f (bk.ι.f (bk.toP bk.E)) ∈ nonZeroDivisors An.Q.A :=
      (_root_.GlobalTheory.BSP.hf_E_pair l K bk An.Q (An.inl.comp bk.ι) (An.inl.comp bk.ι)).1
    exact key _ _ _ hnz e5

  have hδ : ∀ (n : ℕ) (y : En.Q.A), q.f (En.Q.D.δ^[n] y) = An.Q.D.δ^[n] (q.f y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      exact (congrArg q.f (Function.iterate_succ_apply' _ n y)).trans ((q.f_δ _).trans
        ((congrArg An.Q.D.δ (ih y)).trans (Function.iterate_succ_apply' _ n _).symm))
  have hb : ∀ α, q.f (En.tb.b α) = An.tb.b α := by
    intro α
    refine (congrArg q.f (En.tb_b α)).trans ((map_finsuppProd q.f _ _).trans (Eq.trans ?_ (An.tb_b α).symm))
    exact Finsupp.prod_congr fun i _ =>
      (map_pow q.f _ _).trans (congrArg (· ^ α.1 i) ((hδ i En.w).trans (congrArg _ hw)))

  have hJ : (Ideal.span {((l : ℕ) : bk.prism.A)} ⊔ bk.prism.I).map bk.ι.f ≤
      Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I := by
    refine Ideal.map_le_iff_le_comap.2 (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
      fun y hy => Ideal.mem_sup_right (bk.ι.f_I y hy))
    show bk.ι.f ((l : ℕ) : bk.prism.A) ∈ Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I
    rw [map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I) (ainfObj K).A :=
    (ainfObj K).complete.toIsHausdorff

  have key : ∀ α, An.tb.c α (q.f x) = bk.ι.f (En.tb.c α x) := fun α =>
    coeff_map En.tb An.tb bk.ι.f q.f hql hb hJ hH x α

  obtain ⟨y, hy⟩ := hx
  have hl' : ∀ α, ((l : ℕ) : bk.S) ∣ En.tb.c α x := fun α => by
    apply (_root_.GlobalTheory.BSP.BK.evW_isUnit_injective_dvd l K bk).2.2
    refine ⟨An.tb.c α y, ?_⟩
    calc bk.ι.f (En.tb.c α x) = An.tb.c α (q.f x) := (key α).symm
      _ = An.tb.c α (An.inl.f ((l : ℕ) : (ainfObj K).A) * y) := by rw [hy, map_natCast]
      _ = ((l : ℕ) : (ainfObj K).A) * An.tb.c α y := An.tb.c_mul α _ y
  have h := (_root_.GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c l K bk En.Q.A (En.inl.f : bk.S →+* En.Q.A) (Digits l) En.tb ((l : ℕ) : bk.S) x).2 hl'
  have hg : ∀ {R A : Type} [CommRing R] [CommRing A] (s : R →+* A) (y : A) (n : ℕ), s n ∣ y → (n : A) ∣ y :=
    fun s y n h => (map_natCast s n) ▸ h
  exact hg _ _ _ h
end

