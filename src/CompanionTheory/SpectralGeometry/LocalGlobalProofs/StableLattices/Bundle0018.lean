module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HwMapOfLowSpan
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICHWMap

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def diagOp (A : Module.End ℂ T) (B : Module.End ℂ V) : Module.End ℂ (WithLp 2 (T × V)) :=
  (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ (A.prodMap B) ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap

theorem diagOp_fst (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).1 = A (WithLp.ofLp x).1 := rfl

theorem diagOp_snd (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).2 = B (WithLp.ofLp x).2 := rfl

theorem sum_ext {x y : WithLp 2 (T × V)} (h1 : (WithLp.ofLp x).1 = (WithLp.ofLp y).1)
    (h2 : (WithLp.ofLp x).2 = (WithLp.ofLp y).2) : x = y := by
  apply (WithLp.linearEquiv 2 ℂ (T × V)).injective
  exact Prod.ext h1 h2

theorem diag_krel {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KRel ε ET) (h2 : KRel ε E) :
    KRel ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b c d hab hcd
  have e1 := LinearMap.congr_fun (h1 a b c d hab hcd)
  have e2 := LinearMap.congr_fun (h2 a b c d hab hcd)
  refine LinearMap.ext fun x => ?_
  apply sum_ext
  · have := e1 (WithLp.ofLp x).1
    split_ifs at this ⊢ <;> exact this
  · have := e2 (WithLp.ofLp x).2
    split_ifs at this ⊢ <;> exact this

theorem diag_kunit {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KUnit ε ET) (h2 : KUnit ε E) :
    KUnit ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b hab x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, diagOp_fst, diagOp_snd, diagOp_fst, diagOp_snd,
    h1 a b hab, h2 a b hab]

theorem hwMap_of_lowSpan : LowSpan → HWMap := by
  intro hLS n ε T _ _ _ V _ _ ET E μ t v S hRT hUT hR hU ht hHT hH hS hSt hvS
  haveI := hS
  let Lm : (T × S) →ₗ[ℂ] WithLp 2 (T × V) :=
    (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ LinearMap.prodMap LinearMap.id S.subtype
  let S' : Submodule ℂ (WithLp 2 (T × V)) := LinearMap.range Lm
  have memS' : ∀ x : WithLp 2 (T × V), x ∈ S' ↔ (WithLp.ofLp x).2 ∈ S := by
    intro x
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2.2
    · intro hx
      exact ⟨((WithLp.ofLp x).1, ⟨(WithLp.ofLp x).2, hx⟩), sum_ext rfl rfl⟩
  let w0 : WithLp 2 (T × V) := WithLp.toLp 2 (t, v)
  have hw0 : w0 ≠ 0 := by
    intro h
    apply ht
    exact congrArg (fun x => (WithLp.ofLp x).1) h
  have hKR : KRel ε (fun a b => diagOp (ET a b) (E a b)) := diag_krel hRT hR
  have hKU : KUnit ε (fun a b => diagOp (ET a b) (E a b)) := diag_kunit hUT hU
  have hHW : KHighest ε (fun a b => diagOp (ET a b) (E a b)) μ w0 := by
    refine ⟨fun a => ?_, fun a b hab heq => ?_⟩
    · apply sum_ext
      · exact hHT.1 a
      · exact hH.1 a
    · apply sum_ext
      · exact hHT.2 a b hab heq
      · exact hH.2 a b hab heq
  have hStab' : KStab ε (fun a b => diagOp (ET a b) (E a b)) S' := by
    intro a b hab x hx
    rw [memS'] at hx ⊢
    exact hSt a b hab _ hx
  have hw0S' : w0 ∈ S' := (memS' w0).2 hvS
  obtain ⟨L0, -, hw0L, hL0stab, hirr, -, -⟩ :=
    hLS n ε (WithLp 2 (T × V)) (fun a b => diagOp (ET a b) (E a b)) μ w0 S' hKR hKU hw0 hHW
      inferInstance hStab' hw0S'
  let πT : WithLp 2 (T × V) →ₗ[ℂ] T := LinearMap.fst ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let πV : WithLp 2 (T × V) →ₗ[ℂ] V := LinearMap.snd ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let K : Submodule ℂ (WithLp 2 (T × V)) := L0 ⊓ LinearMap.ker πT
  have hKstab : KStab ε (fun a b => diagOp (ET a b) (E a b)) K := by
    intro a b hab x hx
    refine ⟨hL0stab a b hab x hx.1, ?_⟩
    have hx2 : πT x = 0 := hx.2
    show ET a b (πT x) = 0
    rw [hx2, map_zero]
  have hK : K = ⊥ := by
    rcases hirr K inf_le_left hKstab with h | h
    · exact h
    · exfalso
      apply ht
      have hw0K : w0 ∈ K := h ▸ hw0L
      exact hw0K.2
  let g : L0 →ₗ[ℂ] T := πT ∘ₗ L0.subtype
  have ginj : Function.Injective g := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)
    have hxK : (x : WithLp 2 (T × V)) ∈ K := ⟨x.2, hx⟩
    rw [hK] at hxK
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hxK)
  let W0 : Submodule ℂ T := LinearMap.range g
  let e : L0 ≃ₗ[ℂ] W0 := LinearEquiv.ofInjective g ginj
  have hW0stab : ∀ a b, ε a = ε b → ∀ y ∈ W0, ET a b y ∈ W0 := by
    rintro a b hab _ ⟨x, rfl⟩
    exact ⟨⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩, rfl⟩
  let P : T →L[ℂ] W0 := W0.orthogonalProjectionOnto
  have hP : ∀ a b, ε a = ε b → ∀ y : T, (P (ET a b y) : T) = ET a b (P y) := by
    intro a b hab y
    have hmem : ET a b (P y : T) ∈ W0 := hW0stab a b hab _ (P y).2
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · exact hmem
    · rw [← map_sub, hUT a b hab, Submodule.coe_orthogonalProjectionOnto_apply]
      exact Submodule.inner_left_of_mem_orthogonal (hW0stab b a hab.symm w hw)
        (Submodule.sub_starProjection_mem_orthogonal y)
  have hPe : ∀ x : L0, P (g x) = e x := by
    intro x
    have h1 : ((e x : W0) : T) = g x := LinearEquiv.ofInjective_apply _ _
    rw [← h1]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
  let φ : T →ₗ[ℂ] V := πV ∘ₗ L0.subtype ∘ₗ e.symm.toLinearMap ∘ₗ (P : T →ₗ[ℂ] W0)
  have hφ : ∀ y : T, φ y = πV (e.symm (P y) : WithLp 2 (T × V)) := fun y => rfl
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ]
    have hg0 : g ⟨w0, hw0L⟩ = t := rfl
    rw [← hg0, hPe, LinearEquiv.symm_apply_apply]
    rfl
  · intro a b hab y
    obtain ⟨x, hx⟩ : ∃ x : L0, x = e.symm (P y) := ⟨_, rfl⟩
    have hPy : P y = e x := by rw [hx, LinearEquiv.apply_symm_apply]
    let x' : L0 := ⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩
    have hgx' : g x' = ET a b (g x) := rfl
    have hPE : P (ET a b y) = e x' := by
      apply Subtype.ext
      rw [hP a b hab y, hPy, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, hgx']
    rw [hφ, hφ, hPE, LinearEquiv.symm_apply_apply, ← hx]
    rfl

end GlobalTheory.CompanionTheory.DSICHWMap
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSNormLt

open CompanionTheory.D.DSIC

variable {n : ℕ}

def sig (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

theorem sig_anti (a b : Fin n) : sig b a = - sig a b := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

theorem sig_mul {y : Fin n → ℝ} (hy : Antitone y) (a b : Fin n) : sig a b * (y a - y b) = |y a - y b| := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, one_mul, abs_of_nonneg (sub_nonneg.2 (hy h.le))]
  · simp [h]
  · rw [if_neg h.not_gt, if_pos h, abs_of_nonpos (sub_nonpos.2 (hy h.le))]; ring

theorem pair_eq (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (x : Fin n → ℝ) :
    4 * ∑ a, x a * ((∑ b, t a b) / 2) = ∑ a, ∑ b, t a b * (x a - x b) := by
  have h1 : ∑ a, ∑ b, t a b * x b = - ∑ a, ∑ b, t a b * x a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ht a b]; ring
  have h2 : ∑ a, x a * ((∑ b, t a b) / 2) = (∑ a, ∑ b, t a b * x a) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]; ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]; ring

theorem term_le {s z : ℝ} (hs : |s| ≤ 1) : s * z ≤ |z| := by
  calc s * z ≤ |s * z| := le_abs_self _
    _ = |s| * |z| := abs_mul _ _
    _ ≤ 1 * |z| := by gcongr
    _ = |z| := one_mul _

theorem normSq_le (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1) :
    ∑ a, ((∑ b, t a b) / 2) ^ 2 ≤ ∑ a : Fin n, ((∑ b, sig a b) / 2) ^ 2 := by
  set x : Fin n → ℝ := fun a => (∑ b, t a b) / 2 with hx
  set r : Fin n → ℝ := fun a => (∑ b, sig a b) / 2 with hr
  let τ : Equiv.Perm (Fin n) := Tuple.sort (fun a => - x a)
  have hτ : Antitone (fun a => x (τ a)) := by
    intro a b hab
    have := Tuple.monotone_sort (fun a => - x a) hab
    simpa using this
  have e1 : 4 * ∑ a, x a ^ 2 ≤ 4 * ∑ a, x (τ a) * r a := by
    have := pair_eq t ht x
    have h2 := pair_eq sig sig_anti (fun a => x (τ a))
    calc 4 * ∑ a, x a ^ 2 = ∑ a, ∑ b, t a b * (x a - x b) := by
          rw [← this]; simp only [hx, sq]
      _ ≤ ∑ a, ∑ b, |x a - x b| :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => term_le (h1 a b)
      _ = ∑ a, ∑ b, |x (τ a) - x (τ b)| := by
          rw [← Equiv.sum_comp τ]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Equiv.sum_comp τ]
      _ = ∑ a, ∑ b, sig a b * (x (τ a) - x (τ b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (sig_mul hτ a b).symm
      _ = _ := h2.symm
  have e2 : 2 * ∑ a, x (τ a) * r a ≤ ∑ a, x (τ a) ^ 2 + ∑ a, r a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (x (τ a) - r a)]
  have e3 : ∑ a, x (τ a) ^ 2 = ∑ a, x a ^ 2 := Equiv.sum_comp τ (fun a => x a ^ 2)
  show ∑ a, x a ^ 2 ≤ ∑ a, r a ^ 2
  linarith

theorem pair_lt (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1)
    {lam : Fin n → ℝ} (hl : StrictAnti lam) (c d : Fin n) (hcd : c ≠ d) (hne : t c d = - sig c d) :
    ∑ a, lam a * ((∑ b, t a b) / 2) < ∑ a, lam a * ((∑ b, sig a b) / 2) := by
  have e1 := pair_eq t ht lam
  have e2 := pair_eq sig sig_anti lam
  have hle : ∀ a b, t a b * (lam a - lam b) ≤ sig a b * (lam a - lam b) := fun a b => by
    rw [sig_mul hl.antitone]; exact term_le (h1 a b)
  have : ∑ a, ∑ b, t a b * (lam a - lam b) < ∑ a, ∑ b, sig a b * (lam a - lam b) := by
    refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => hle a b) ⟨c, mem_univ _, ?_⟩
    refine Finset.sum_lt_sum (fun b _ => hle c b) ⟨d, mem_univ _, ?_⟩
    rw [hne, neg_mul, sig_mul hl.antitone]
    have : 0 < |lam c - lam d| := abs_pos.2 (sub_ne_zero.2 fun h => hcd (hl.injective h))
    linarith
  linarith


open Classical in
def ind {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  if ∃ h : ε a = true ∧ ε b = false, (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0

theorem wtA_eq {ε : Fin n → Bool} (A : Finset (NC ε)) (c : Fin n) :
    wtA A c = ∑ b, (ind A c b - ind A b c) := by
  classical
  rw [Finset.sum_sub_distrib]
  unfold wtA ind
  rw [Finset.sum_boole, Finset.sum_boole]
  congr 2
  · refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(c, b), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩
  · refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(b, c), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩

theorem ind_of_not {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ¬ (ε a = true ∧ ε b = false)) :
    ind A a b = 0 := by
  unfold ind
  rw [if_neg]
  rintro ⟨h', _⟩
  exact h h'

theorem ind_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    ind A a b = if (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0 := by
  unfold ind
  congr 1
  simp [h]

def tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  sig a b + 2 * ((ind (A1 ε) a b - ind (A1 ε) b a) - (ind A a b - ind A b a))

theorem tt_anti {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : tt A b a = - tt A a b := by
  unfold tt; rw [sig_anti a b]; ring

theorem tt_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    tt A a b = if ((⟨(a, b), h⟩ : NC ε) ∈ A ↔ (⟨(a, b), h⟩ : NC ε) ∈ A1 ε) then sig a b else - sig a b := by
  have h' : ¬ (ε b = true ∧ ε a = false) := by simp [h.1]
  have hab : a ≠ b := by rintro rfl; simp [h.1] at h
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of _ h, ind_of _ h]
  have hm : (⟨(a, b), h⟩ : NC ε) ∈ A1 ε ↔ b < a := by simp [A1]
  simp only [hm]
  unfold sig
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> by_cases h2 : (⟨(a, b), h⟩ : NC ε) ∈ A <;>
    simp [h1, h1.not_gt, h2] <;> norm_num

theorem abs_sig (a b : Fin n) : |sig a b| ≤ 1 := by
  unfold sig; split_ifs <;> simp

theorem abs_tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : |tt A a b| ≤ 1 := by
  have key : ∀ a b : Fin n, (ε a = true ∧ ε b = false) → |tt A a b| ≤ 1 := fun a b h => by
    rw [tt_of A h]
    split_ifs
    · exact abs_sig a b
    · rw [abs_neg]; exact abs_sig a b
  by_cases h : ε a = true ∧ ε b = false
  · exact key a b h
  by_cases h' : ε b = true ∧ ε a = false
  · rw [tt_anti, abs_neg]; exact key b a h'
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of_not _ h, ind_of_not _ h]
  simpa using abs_sig a b

theorem rho_eq (ε : Fin n → Bool) (a : Fin n) :
    PI.UpqRep.rhoC ε a + PI.UpqRep.rhoN ε a = (∑ b, sig a b) / 2 := by
  unfold PI.UpqRep.rhoC PI.UpqRep.rhoN
  rw [← add_div]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]

theorem normLt : CompanionTheory.D.DSIC.NormLt := by
  intro n ε lam hl A hA
  obtain ⟨⟨⟨c, d⟩, h⟩, hi⟩ : ∃ i : NC ε, ¬ (i ∈ A ↔ i ∈ A1 ε) := by
    by_contra hc
    push Not at hc
    exact hA (Finset.ext fun i => by simpa using hc i)
  have hcd : c ≠ d := by rintro rfl; simp [h.1] at h
  have hne : tt A c d = - sig c d := by rw [tt_of A h, if_neg hi]
  have i1 := pair_lt (tt A) (tt_anti A) (abs_tt A) hl c d hcd hne
  have i2 := normSq_le (tt A) (tt_anti A) (abs_tt A)
  have f1 : ∀ a, (gam ε lam - wtA A + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, tt A a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [gam, PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wtA_eq, tt,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_sub_distrib (f := fun b => ind (A1 ε) a b - ind (A1 ε) b a)]
    linarith
  have f2 : ∀ a, (PI.UpqRep.lowK ε lam + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  simp only [f1, f2]
  rw [ex, ex]
  linarith

end GlobalTheory.CompanionTheory.DSNormLt
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MulMemUJset
section
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.DSSmLin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mul_mem_UJset {n : ℕ} (ε : Fin n → Bool) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

theorem ex_mem_UJset {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    ex X t ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem inG_add {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem inG_smul {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    inG ε ((s : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
    ← smul_add, hX, smul_zero]

theorem smLin : CompanionTheory.D.DSIC.SmLin := by
  intro n ε H _ _ σ hσ
  obtain ⟨⟨h1, hm⟩, -, -⟩ := hσ
  have h : RepOn (UJset ε) σ := ⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩
  refine ⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_,
    fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩
  · exact IsSm.add (G := UJset ε) hv hw
  · exact IsSm.smul (G := UJset ε) hv c
  · exact IsSm.apply h hv hg
  · have hv' : IsSm (UJset ε) σ v := hv
    refine ⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩
    rw [List.mem_singleton.1 hY]
    exact ex_mem_UJset hX t
  · have hv' : IsSm (UJset ε) σ v := hv
    obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv' 1 h.one_mem
    have key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z := fun Z hZ => by
      have hd : HasDerivAt (fun t => ex Z t) Z 0 := by simpa using hasDerivAt_mul_ex 1 Z
      exact (hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv
    refine ⟨?_, fun s => ?_⟩
    · rw [key _ (inG_add hX hY), key _ hX, key _ hY, map_add (f := _)]
    · rw [key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]

end GlobalTheory.CompanionTheory.DSSmLin
end

