module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGamma
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.CosetEval

def mfMonoid (Γ : Subgroup SL(2, ℤ)) : Submonoid (Multiplicative ℤ × (ℍ → ℂ)) where
  carrier := {p | IsMF Γ (Multiplicative.toAdd p.1) p.2}
  mul_mem' := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ha hb
    exact IsMF.mul ha hb (by simp)
  one_mem' := IsMF.one Γ

def evHom (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (τ : ℍ) : mfMonoid Γ →* ℂ where
  toFun p := (p.1.2 ∣[Multiplicative.toAdd p.1.1] x) τ
  map_one' := by
    show ((1 : ℍ → ℂ) ∣[Multiplicative.toAdd (1 : Multiplicative ℤ)] x) τ = 1
    rw [toAdd_one, ModularForm.is_invariant_one]; rfl
  map_mul' p q := by
    show ((p.1.2 * q.1.2) ∣[Multiplicative.toAdd (p.1.1 * q.1.1)] x) τ = _
    rw [toAdd_mul, ModularForm.mul_slash_SL2]; rfl

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero {D : ℍ → ℂ} (hD : MDiff D) (hD0 : D ≠ 0) :
    Dense {τ | D τ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨τ, hτ⟩
  by_contra hempty
  have hzero : ∀ σ ∈ U, D σ = 0 := fun σ hσ => by_contra fun h => hempty ⟨σ, hσ, h⟩
  have hS : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ (D ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hD).analyticOnNhd hS
  have hev : D ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] 0 := by
    have hUc : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
    filter_upwards [hUc.mem_nhds ⟨τ, hτ, rfl⟩] with w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    simp [hzero σ hσ]
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hev
  apply hD0
  funext σ
  simpa using hall σ.im_pos


open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
theorem _root_.GlobalTheory.CosetEval.evals_independent : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  intro M _ hsep
  classical
  have hsep' : ∀ p : SL(2, ℤ) × SL(2, ℤ), ∃ (k : ℤ) (f : ℍ → ℂ),
      _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (p.1 * p.2⁻¹ ∉ CongruenceSubgroup.Gamma M → f ∣[k] p.1 ≠ f ∣[k] p.2) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact ⟨0, 0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h => absurd hp h⟩
    · obtain ⟨k, f, hf, hne⟩ := hsep _ hp
      refine ⟨k, f, hf, fun _ heq => hne ?_⟩
      have := congrArg (fun g => g ∣[k] p.2⁻¹) heq

      rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, mul_inv_cancel,
        SlashAction.slash_one] at this
  choose k f hf hne using hsep'
  set O : SL(2, ℤ) × SL(2, ℤ) → Set ℍ := fun p =>
    {_τ | p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M} ∪
      {τ | (f p ∣[k p] p.1) τ ≠ (f p ∣[k p] p.2) τ} with hO
  have hcont : ∀ p (y : SL(2, ℤ)), Continuous (f p ∣[k p] y) := fun p y =>
    (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ y).continuous
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    isOpen_const.union (isOpen_ne_fun (hcont p p.1) (hcont p p.2))
  have hOdense : ∀ p, Dense (O p) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact dense_univ.mono fun τ _ => Or.inl hp
    · have hD : MDiff (f p ∣[k p] p.1 - f p ∣[k p] p.2) :=
        (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _).sub (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _)
      refine (dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero hD
        (fun h0 => hne p hp (sub_eq_zero.1 h0))).mono fun τ hτ => Or.inr ?_
      exact sub_ne_zero.1 hτ
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := Subtype.countable
  obtain ⟨τ₀, hτ₀⟩ := (dense_iInter_of_isOpen hOopen hOdense).nonempty
  refine ⟨τ₀, fun ι _ x c hx hc => ?_⟩
  let χ : ι → (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M) →* ℂ) :=
    fun i => _root_.GlobalTheory.CosetEval.evHom (CongruenceSubgroup.Gamma M) (x i) τ₀
  have hinj : Function.Injective χ := by
    intro i j hij
    by_contra hij'
    have hnot : x i * (x j)⁻¹ ∉ CongruenceSubgroup.Gamma M := fun h => hij' (hx i j h)
    rcases Set.mem_iInter.1 hτ₀ (x i, x j) with h | h
    · exact hnot h
    · exact h (DFunLike.congr_fun hij
        ⟨(Multiplicative.ofAdd (k (x i, x j)), f (x i, x j)), hf (x i, x j)⟩)
  have hli := (linearIndependent_monoidHom (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M)) ℂ).comp χ hinj
  funext i
  refine Fintype.linearIndependent_iff.1 hli c ?_ i
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
  exact hc _ _ p.2

end GlobalTheory.CosetEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShell
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L]

theorem approxRoot_exists_val_pow {p : ℕ} {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) {u : L} (hu : u ∈ F) (hu0 : u ≠ 0) :
    ∃ w ∈ F, v w ^ p = v u := by
  obtain ⟨θ, hθ, h⟩ := hA
  obtain ⟨w, hw, hle⟩ := h u hu
  have hvu : 0 < v u := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hu0)
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hle (mul_lt_of_lt_one_left hvu hθ)
  refine ⟨w, hw, ?_⟩
  rw [← map_pow]
  exact Valuation.map_eq_of_sub_lt v hlt

theorem approxRoot_exists_root_of_p {p : ℕ} (hp : p.Prime) {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) :
    ∀ k : ℕ, ∃ π ∈ F, v π ^ (p ^ k) = v (p : L) := by
  intro k
  induction k with
  | zero => exact ⟨(p : L), natCast_mem F p, by simp⟩
  | succ k ih =>
    obtain ⟨π, hπ, hv⟩ := ih
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)] at hv
      exact hp0.ne hv
    obtain ⟨w, hw, hw'⟩ := approxRoot_exists_val_pow hA hπ hπ0
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', pow_mul, hw', hv]

theorem exists_scale_shell (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (F : Subfield L) (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) (hp1 : v (p : L) < 1)
    (r : ℝ≥0) (hr : r < 1) (x : L) (hx : x ≠ 0) :
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hp0 p) hr
  obtain ⟨π, hπ, hv⟩ := approxRoot_exists_root_of_p hp hA hp0 n
  set s := v π with hs
  set t := s ^ p with ht
  have hrt : r < t := by
    by_contra h
    push_neg at h
    have h1 : t ^ (p ^ n) ≤ r ^ (p ^ n) := pow_le_pow_left₀ (by positivity) h _
    have h2 : r ^ (p ^ n) ≤ r ^ n :=
      pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hp.one_lt).le
    have h3 : t ^ (p ^ n) = v (p : L) ^ p := by rw [ht, ← pow_mul, mul_comm, pow_mul, hv]
    exact absurd (lt_of_le_of_lt (h3 ▸ h1.trans h2) hn) (lt_irrefl _)
  have hs1 : s < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p ^ n) h
    rw [hv] at this
    exact absurd hp1 (not_lt.mpr this)
  have ht1 : t < 1 := pow_lt_one₀ (by positivity) hs1 hp.ne_zero
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hrt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have h0 : s = 0 := by rw [hs, map_zero]
    rw [ht, h0, zero_pow hp.ne_zero] at ht0
    exact lt_irrefl _ ht0
  have hvx : 0 < v x := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hx)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hvx ((one_lt_inv₀ ht0).mpr ht1)
  refine ⟨π ^ (m + 1), zpow_mem hπ _, zpow_ne_zero _ hπ0, ?_⟩
  have hval : v (x * (π ^ (m + 1)) ^ p) = v x * t ^ (m + 1) := by
    rw [map_mul, map_pow, map_zpow₀, ← hs, ht, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm (m + 1)]
  rw [hval]
  have htne : t ≠ 0 := ht0.ne'
  constructor
  · have e : t⁻¹ ^ m * t ^ (m + 1) = t := by
      rw [inv_zpow, zpow_add_one₀ htne, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ htne), one_mul]
    calc r < t := hrt
      _ = t⁻¹ ^ m * t ^ (m + 1) := e.symm
      _ < v x * t ^ (m + 1) := mul_lt_mul_of_pos_right hm1 (zpow_pos ht0 _)
  · have e : t⁻¹ ^ (m + 1) * t ^ (m + 1) = 1 := by
      rw [inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ htne)]
    calc v x * t ^ (m + 1) ≤ t⁻¹ ^ (m + 1) * t ^ (m + 1) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = 1 := e

theorem klc_scale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L,
    ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 →
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 :=
  fun L _ v p hp F hA hp0 hp1 r hr x hx => exists_scale_shell L v p hp F hA hp0 hp1 r hr x hx

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfCosetRepresentativeTrace
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_reps_of_cosetTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L]
    (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U,
    ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧
      (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧
      ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  intro L _ G _ _ U _ S hS y₀ hy₀
  classical
  set V : Subgroup G := fixingSubgroup G (S : Set L) with hV
  have hUV : U ≤ V := by
    intro u hu
    rw [hV, mem_fixingSubgroup_iff]
    intro s hs
    exact hS s hs ⟨u, hu⟩
  have hy0 : ∀ a b : G, (a : G ⧸ U) = b → a • y₀ = b • y₀ := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have h1 : (a⁻¹ * b) • y₀ = y₀ := hy₀ ⟨_, hab⟩
    calc a • y₀ = a • ((a⁻¹ * b) • y₀) := by rw [h1]
      _ = b • y₀ := by rw [smul_smul, mul_inv_cancel_left]
  set f : G ⧸ U → L := fun q => q.out • y₀ with hf
  have hfmk : ∀ g : G, f (g : G ⧸ U) = g • y₀ := fun g => hy0 _ _ (QuotientGroup.out_eq' _)
  have hfeq : ∀ (g : G) (q : G ⧸ U), f (g • q) = g • f q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show f ((g * a : G) : G ⧸ U) = g • f (a : G ⧸ U)
      rw [hfmk, hfmk, mul_smul]
  let π : G ⧸ U → G ⧸ V := Subgroup.quotientMapOfLE hUV
  have hπmk : ∀ g : G, π (g : G ⧸ U) = (g : G ⧸ V) := fun g => rfl
  have hπeq : ∀ (g : G) (q : G ⧸ U), π (g • q) = g • π q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a => rw [MulAction.Quotient.smul_mk, hπmk, hπmk, MulAction.Quotient.smul_mk]
  have hV1 : ∀ g : G, (g : G ⧸ V) = ((1 : G) : G ⧸ V) ↔ g ∈ V := by
    intro g
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  haveI : Finite (G ⧸ V) := Finite.of_surjective π (by
    intro c
    induction c using QuotientGroup.induction_on with
    | H a => exact ⟨(a : G ⧸ U), rfl⟩)
  letI : Fintype (G ⧸ V) := Fintype.ofFinite _
  set F : Finset (G ⧸ U) := Finset.univ.filter (fun q => π q = ((1 : G) : G ⧸ V)) with hF
  have hout : ∀ {H : Subgroup G} (a b : G ⧸ H), a.out = b.out → a = b := by
    intro H a b hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, hab]

  have hyV : ∀ v ∈ V, v • (∑ q ∈ F, f q) = ∑ q ∈ F, f q := by
    intro v hv
    rw [Finset.smul_sum]
    symm
    refine Finset.sum_nbij' (fun q => v⁻¹ • q) (fun q => v • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact V.inv_mem hv
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact hv
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      rw [hfeq, smul_inv_smul]
  refine ⟨∑ q ∈ F, f q, F.image Quotient.out, (Finset.univ : Finset (G ⧸ V)).image Quotient.out, ?_, ?_, ?_⟩
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
  · intro h
    have hgh : (h : G ⧸ V).out⁻¹ * h ∈ V := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨(h : G ⧸ V).out, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_, ?_⟩, ?_⟩
    · conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, hyV _ hgh]
    · intro s hs
      have h2 : ((h : G ⧸ V).out⁻¹ * h) • s = s := (mem_fixingSubgroup_iff G).1 hgh s hs
      conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, h2]
    · rintro g' ⟨hg'E, _, hg'S⟩
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hg'E
      have h3 : c.out⁻¹ * h ∈ V := (mem_fixingSubgroup_iff G).2 (fun s hs => by
        rw [← smul_smul, hg'S s hs, inv_smul_smul])
      have h4 : (c.out : G ⧸ V) = (h : G ⧸ V) := QuotientGroup.eq.2 h3
      rw [QuotientGroup.out_eq'] at h4
      rw [h4]
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
    unfold cosetTrace
    change _ = ∑ q : G ⧸ U, f q
    rw [← Finset.sum_fiberwise Finset.univ π f]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    have key : ∀ g : G, g⁻¹ • (g : G ⧸ V) = ((1 : G) : G ⧸ V) := fun g => by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    refine Finset.sum_nbij' (fun q => c.out • q) (fun q => c.out⁻¹ • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq]
      have h5 := key c.out
      rwa [QuotientGroup.out_eq'] at h5
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      rw [hfeq]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
section
open Polynomial

namespace GlobalTheory.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add (f := _), map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ _ g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := _root_.GlobalTheory.reduced_fibres_almost_all k A
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.SquarefreeFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroup
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_surj_hom_zmod_of_isPGroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G],
      IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  intro p hp G _ _ _ hG
  obtain ⟨n, hn, hc⟩ := hG.nontrivial_iff_card.1 inferInstance
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := m)
    (by rw [hc]; exact pow_dvd_pow p (Nat.le_succ m))
  have hi : K.index = p := by
    have := K.card_mul_index
    rw [hK, hc, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos m) this
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hi, hc, hp.out.pow_minFac (Nat.succ_ne_zero m)])
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (p := p) (by rw [← hi]; rfl) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  exact e.surjective.comp (QuotientGroup.mk'_surjective K)

end GlobalTheory.AlmostEt
end

