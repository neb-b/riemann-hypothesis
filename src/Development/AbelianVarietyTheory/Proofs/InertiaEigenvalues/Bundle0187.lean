module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

open Filter Topology

namespace GlobalTheory.GaussSlope

theorem eventually_iSup_eq_monomial (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≥] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push Not at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  have hσ0 : 0 < σ := hρ.trans hσ
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hρ j)) hσ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, n)) ⟨j, Finset.mem_insert_self _ _⟩
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≥] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : ρ ≤ r := hr
      simp only at h h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_div hρ).2 hr) h')
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[≥] ρ, r < σ := (gt_mem_nhds hσ).filter_mono nhdsWithin_le_nhds
  filter_upwards [(eventually_all_finset _).2 key, hlt, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : ρ ≤ r := hr
  have hr0 : 0 ≤ r := hρ.le.trans hr
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * σ ^ n := by gcongr; exact h1 n
        _ ≤ σ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hσ0.le hσ1.le (not_lt.1 hn)
        _ ≤ c j * ρ ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem add_eq_of_lt {R : Type} [CommRing R] (N : R → ℝ) (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hneg : ∀ x, N (-x) = N x) {x y : R} (h : N y < N x) : N (x + y) = N x := by
  refine le_antisymm ((hadd x y).trans (max_le le_rfl h.le)) ?_
  have := hadd (x + y) (-y)
  rw [add_neg_cancel_right, hneg] at this
  rcases le_max_iff.1 this with h' | h'
  · exact h'
  · exact absurd h' (not_le.2 h)

theorem map_pow_mul {R : Type} [CommRing R] (N : R → ℝ) (hmul : ∀ x y, N (x * y) = N x * N y)
    (p x : R) (k : ℕ) : N (p ^ k * x) = N p ^ k * N x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, hmul, ih]; ring

theorem slope_abstract {R : Type} [CommRing R] (p : R) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (N : ℝ → R → ℝ)
    (hN : ∀ r, ρ ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, ρ ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n) :
    ∃ (r₁ c : ℝ) (k : ℤ), ρ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, ρ < r → r < r₁ → N r b = c * r ^ k := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, ρ ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hρ.le.trans hr) _) (e1 z)
  have hbb : ∀ r, ρ ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN ρ le_rfl hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ le_rfl hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ le_rfl hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ le_rfl hρ1] at ha
  obtain ⟨i, hi⟩ := eventually_iSup_eq_monomial c h0 h1 hρ hρ1 ((pow_pos hρ _).trans ha).ne'
  rw [hi.self_of_nhdsWithin Set.self_mem_Ici] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  have h5 : ∀ᶠ r in 𝓝[≥] ρ, r < 1 → N r b = c i * r ^ ((i : ℤ) - k) := by
    filter_upwards [hi, h4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr1 hr2 hr hr3
    have hr : ρ ≤ r := hr
    have hr0 : 0 < r := hρ.trans_le hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr3
    have h6 := hbb r hr hr3
    have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
    rw [hab, add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
    rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h5
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  refine ⟨min u σ, c i, (i : ℤ) - k, lt_min hu hσ, (min_le_right _ _).trans_lt hσ1, hci, fun r hr hr' => ?_⟩
  exact hsub ⟨hr.le, hr'.trans_le (min_le_left _ _)⟩ ((hr'.trans_le (min_le_right _ _)).trans hσ1)

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem exists_pow_mul_eq (s : Per.Acris0 l) : ∃ (k : ℕ) (a : Per.Ainf l),
    (l : Per.Acris l) ^ k * algebraMap (Per.Acris0 l) (Per.Acris l) s = algebraMap (Per.Ainf l) (Per.Acris l) a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (l : Per.Ainf l) (s : Per.AinfP l)
  refine ⟨k, a, ?_⟩
  have h1 : (l : Per.Acris0 l) ^ k * s = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    rw [map_natCast, mul_comm] at h
    simpa using h
  have h2 : algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
    GlobalTheory.RingIface.tower (l := l) a
  rw [h2, ← h1, map_mul, map_pow, map_natCast]

theorem gauss_l {r : ℝ} (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
      = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · subst h
      simp
    · rw [untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 1 then r else 0) ⟨_, Set.forall_mem_range.2 hall⟩ 1 (by simp))

end GlobalTheory.GaussSlope

namespace GlobalTheory.MemLoc
open GlobalTheory.GaussSlope

theorem gauss_slope : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  intro l _ N hN b hb
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine slope_abstract (l : Per.Acris l) hρ hρ1 N (fun r hr hr1 => ?_) b
    (lt_of_le_of_ne ((hN _ le_rfl hρ1).1 b).1 hb.symm) fun n => ?_
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr1
    refine ⟨fun x => (e1 x).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, e5, gauss_l l (hρ.le.trans hr)]
  · obtain ⟨s, z, h⟩ := (acris_basic l).2.2.1 b n
    obtain ⟨k, a, ha⟩ := exists_pow_mul_eq l s
    refine ⟨k, _, z, fun n => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (hN r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicallyCompleteLatticeReductionAction
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.CocycleLift

variable {O G T M : Type} [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G]
  [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M]

theorem pow_smul_eq_zero (lam : O) (htf : ∀ t : T, lam • t = 0 → t = 0) (n : ℕ) (t : T)
    (h : lam ^ n • t = 0) : t = 0 := by
  induction n generalizing t with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact htf _ (ih _ h)

theorem smodeq_iff (lam : O) (n : ℕ) (x y : T) :
    x ≡ y [SMOD ((Ideal.span {lam}) ^ n • ⊤ : Submodule O T)] ↔ ∃ t, x - y = lam ^ n • t := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩; exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩; exact ⟨b, trivial, hb.symm⟩

theorem step (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M)
    (htf : ∀ t : T, lam • t = 0 → t = 0) (hq : Function.Surjective q)
    (hker : ∀ t, q t = 0 ↔ ∃ y, t = lam • y) (heq : ∀ g t, q (π g t) = π' g (q t))
    (hcont : ∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y)
    (hH : Subsingleton (ReciprocityTheory.Def.H2 π' ⊤)) (a : ℕ) (c : G → T) (hc : IsLocallyConstant c)
    (hd : ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y) :
    ∃ c' : G → T, (IsLocallyConstant c' ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c' x = lam ^ (a + 1 + 1) • y) ∧
      ∀ g, ∃ y, c' g - c g = lam ^ (a + 1) • y := by
  choose w hw using hd
  have hw' : ∀ g h, π g (c h) - c (g * h) + c g = lam ^ (a + 1) • w (g, h) := fun g h => hw (g, h)
  have hlc : IsLocallyConstant (fun x => q (w x)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨g₀, h₀⟩
    have e1 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.1 = c g₀ :=
      (hc.comp_continuous continuous_fst).eventually_eq (g₀, h₀)
    have e2 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.2 = c h₀ :=
      (hc.comp_continuous continuous_snd).eventually_eq (g₀, h₀)
    have e3 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c (x.1 * x.2) = c (g₀ * h₀) :=
      (hc.comp_continuous continuous_mul).eventually_eq (g₀, h₀)
    have e4 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀),
        ∃ y, π x.1 (c h₀) - π g₀ (c h₀) = lam ^ (a + 1 + 1) • y :=
      (continuous_fst.tendsto (g₀, h₀)).eventually (hcont (a + 1 + 1) (c h₀) g₀)
    filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 ⟨y, h4⟩
    obtain ⟨g, h⟩ := x
    simp only at h1 h2 h3 h4
    rw [← sub_eq_zero, ← map_sub, hker]
    refine ⟨y, ?_⟩
    rw [← sub_eq_zero]
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_sub, ← hw', ← hw', h1, h2, h3, ← mul_smul, ← pow_succ, ← h4]
    abel
  have hcoc : ∀ g h l, π g (w (h, l)) - w (g * h, l) + w (g, h * l) - w (g, h) = 0 := by
    intro g h l
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_add, smul_sub, ← map_smul, ← hw', ← hw', ← hw', ← hw']
    simp only [map_add (f := _), map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  have hZ : (fun x => q (w x)) ∈ ReciprocityTheory.Def.Z2 π' ⊤ := by
    refine ⟨⟨hlc, fun _ => trivial⟩, ?_⟩
    show ReciprocityTheory.Def.d2 π' _ = 0
    funext ⟨g, h, l⟩
    have := congrArg q (hcoc g h l)
    simp only [map_add (f := _), map_sub, heq, map_zero] at this
    exact this
  have h0 : (Submodule.Quotient.mk ⟨_, hZ⟩ : ReciprocityTheory.Def.H2 π' ⊤) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨b, ⟨hb, -⟩, hbd⟩ := h0
  have hbd' : ∀ g h, π' g (b h) - b (g * h) + b g = q (w (g, h)) := fun g h => congrFun hbd (g, h)
  choose s hs using hq
  refine ⟨fun g => c g - lam ^ (a + 1) • s (b g), ⟨?_, ?_⟩, fun g => ⟨- s (b g), by simp⟩⟩
  · exact hc.sub (hb.comp (fun m => lam ^ (a + 1) • s m))
  · rintro ⟨g, h⟩
    obtain ⟨y, hy⟩ := (hker (w (g, h) - (π g (s (b h)) - s (b (g * h)) + s (b g)))).1 (by
      simp only [map_add (f := _), map_sub, heq, hs, hbd', sub_self])
    refine ⟨y, ?_⟩
    show π g (c h - lam ^ (a + 1) • s (b h)) - (c (g * h) - lam ^ (a + 1) • s (b (g * h)))
      + (c g - lam ^ (a + 1) • s (b g)) = _
    rw [pow_succ lam (a + 1), mul_smul, ← hy, smul_sub, ← hw', map_sub, map_smul, smul_add, smul_sub]
    abel

theorem exists_lift : ∀ (O G T M : Type) [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M] (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M), IsAdicComplete (Ideal.span {lam}) T → (∀ t : T, lam • t = 0 → t = 0) → Function.Surjective q → (∀ t, q t = 0 ↔ ∃ y, t = lam • y) → (∀ g t, q (π g t) = π' g (q t)) → (∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y) → Subsingleton (ReciprocityTheory.Def.H2 π' ⊤) → ∀ z ∈ ReciprocityTheory.Def.Z1 π' ⊤, ∃ c : G → T, (∀ g h, c (g * h) = c g + π g (c h)) ∧ (∀ g, q (c g) = z g) ∧ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, c g - c g₀ = lam ^ a • y := by
  intro O G T M _ _ _ _ _ _ _ _ lam π π' q hcomp htf hq hker heq hcont hH z hz
  have hst := step lam π π' q htf hq hker heq hcont hH
  obtain ⟨⟨hz1, -⟩, hz2⟩ := hz
  have hz3 : ∀ g h, π' g (z h) - z (g * h) + z g = 0 := fun g h => congrFun hz2 (g, h)
  choose s hs using hq
  let P : ℕ → (G → T) → Prop := fun a c =>
    IsLocallyConstant c ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y
  have P0 : P 0 (fun g => s (z g)) := by
    refine ⟨hz1.comp s, ?_⟩
    rintro ⟨g, h⟩
    rw [zero_add, pow_one, ← hker]
    show q (π g (s (z h)) - s (z (g * h)) + s (z g)) = 0
    simp only [map_add (f := _), map_sub, heq, hs, hz3]
  have hst' : ∀ a (c : {c // P a c}), ∃ c' : {c // P (a + 1) c},
      ∀ g, ∃ y, c'.1 g - c.1 g = lam ^ (a + 1) • y := by
    intro a c
    obtain ⟨c', h1, h2⟩ := hst a c.1 c.2.1 c.2.2
    exact ⟨⟨c', h1⟩, h2⟩
  choose F hF using hst'
  let u : ∀ a, {c // P a c} := fun a => Nat.rec ⟨_, P0⟩ F a
  have hu : ∀ a g, ∃ y, (u (a + 1)).1 g - (u a).1 g = lam ^ (a + 1) • y := fun a => hF a (u a)
  have hcau : ∀ g m n, m ≤ n → ∃ y, (u n).1 g - (u m).1 g = lam ^ (m + 1) • y := by
    intro g m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨y', hy'⟩ := hu n g
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨y + lam ^ k • y', ?_⟩
      rw [smul_add, ← mul_smul, ← pow_add, show m + 1 + k = m + k + 1 by ring, ← hy, ← hy']
      abel
  have hlim : ∀ g, ∃ L, ∀ n, ∃ y, (u n).1 g - L = lam ^ n • y := by
    intro g
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomp.toIsPrecomplete (f := fun n => (u n).1 g) (by
      intro m n hmn
      apply SModEq.symm
      rw [smodeq_iff]
      obtain ⟨y, hy⟩ := hcau g m n hmn
      exact ⟨lam • y, by rw [hy, pow_succ, mul_smul]⟩)
    exact ⟨L, fun n => (smodeq_iff lam n _ _).1 (hL n)⟩
  choose c hc using hlim
  refine ⟨c, fun g h => ?_, fun g => ?_, fun a g₀ => ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus hcomp.toIsHausdorff
    intro n
    rw [smodeq_iff]
    obtain ⟨y1, h1⟩ := hc g n
    obtain ⟨y2, h2⟩ := hc h n
    obtain ⟨y3, h3⟩ := hc (g * h) n
    obtain ⟨y4, h4⟩ := (u n).2.2 (g, h)
    have h4' : π g ((u n).1 h) - (u n).1 (g * h) + (u n).1 g = lam ^ n • lam • y4 := by
      rw [← mul_smul, ← pow_succ]; exact h4
    refine ⟨y1 + π g y2 - y3 - lam • y4, ?_⟩
    rw [smul_sub, smul_sub, smul_add, ← map_smul, ← h1, ← h2, ← h3, ← h4', map_sub]
    abel
  · obtain ⟨y1, h1⟩ := hc g 1
    obtain ⟨y2, h2⟩ := hcau g 0 1 (by norm_num)
    have h0 : q ((u 0).1 g) = z g := hs _
    rw [← h0, ← sub_eq_zero, ← map_sub, hker]
    refine ⟨y2 - y1, ?_⟩
    rw [zero_add, pow_one] at h2
    rw [pow_one] at h1
    rw [smul_sub, ← h1, ← h2]
    abel
  · filter_upwards [(u a).2.1.eventually_eq g₀] with g hg
    obtain ⟨y1, h1⟩ := hc g a
    obtain ⟨y2, h2⟩ := hc g₀ a
    refine ⟨y2 - y1, ?_⟩
    rw [smul_sub, ← h1, ← h2, hg]
    abel

end GlobalTheory.CocycleLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpandStatement
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
      [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ]
      (G : Matrix κ ι K⟦X⟧),
      colon (O := O) (K := K) (G.map (frob K l)) ≤
        (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have map_decomp_frob {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
      (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
      PowerSeries.map (algebraMap O K) f =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, map_X, map_expand]
    rfl
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    _root_.GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main l hl2 _
      (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    _root_.GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main l hl2 (frob K l)
      (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val *
          frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm
  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealMapExpandLeFrobeniusStatement
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type)
    [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (_root_.GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTermsStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  first | exact @GlobalTheory.BK.PhiMod.mem_MM_of_series | exact GlobalTheory.BK.PhiMod.mem_MM_of_series | (intros; apply GlobalTheory.BK.PhiMod.mem_MM_of_series <;> assumption)
end

