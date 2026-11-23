module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0001
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf
section
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem inner_lower_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hR : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ⟪A b a w, A b a w⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) * ⟪w, w⟫_ℂ := by
  have hba : b ≠ a := ne_of_gt hab
  have hc := hR a b b a he he.symm
  simp only [if_true] at hc
  have hx := congrArg (fun F : Module.End ℂ V => F w) hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw.2 a b hab he, map_zero, sub_zero] at hx
  have h1 := hU b a he.symm w (A b a w)
  rw [h1, hx, hw.1 a, hw.1 b, ← sub_smul, inner_smul_right]
  push_cast
  ring

theorem kType_dom {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : KDom ε Λ := by
  intro a b hab he
  have h := inner_lower_self (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hab he
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, T.w_norm] at h
  have h2 : ‖kunits T b a T.w‖ ^ 2 = Λ a - Λ b := by
    have h' : ((‖kunits T b a T.w‖ ^ 2 : ℝ) : ℂ) = ((Λ a - Λ b : ℝ) : ℂ) := by
      have h0 := h
      simp only [RCLike.ofReal_one, one_pow, mul_one] at h0
      simpa using h0
    exact Complex.ofReal_injective h'
  have h3 : (0 : ℝ) ≤ ‖kunits T b a T.w‖ ^ 2 := sq_nonneg _
  linarith

theorem kTypeIntDom_of
    (hint : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ), ∀ a, ∃ m : ℤ, Λ a = m) :
    KTypeIntDomStatement :=
  fun n ε Λ T => ⟨hint n ε Λ T, kType_dom T⟩

theorem kTypeIntDom : KTypeIntDomStatement :=
  kTypeIntDom_of fun _ _ _ T => kType_int T

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem tensHW_mem_khwSub {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem tensHW_hw_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hA : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    (hspan : Formalism.REAL.kSpan ε A w = ⊤) {μ : Fin n → ℝ} {y : V}
    (hy : Formalism.REAL.KHighest ε A μ y) (hy0 : y ≠ 0) :
    μ = Λ ∧ ∃ c : ℂ, y = c • w := by
  rcases Formalism.REAL.kHiUniq V n ε A Λ μ w y hA hU hw (by rw [hspan]; exact Submodule.mem_top) hy with h | h
  · exact absurd h hy0
  · exact h

theorem tensHW_of (h : LowCompStatement) : TensHWStatement := by
  intro V _ _ n ε A Λ w ι _ _ M γ hA hU hw hspan hM hdiag
  have key : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x →
      ∃ i, ν = Λ + γ i ∧ x i ≠ 0 ∧ ∃ c : ℂ, x i = c • w := by
    intro ν x hx hK
    obtain ⟨β, ⟨i, hi, hxi⟩, hall⟩ := h V n ε A ι M γ hM hdiag ν x hx hK
    obtain ⟨hμ, c, hc⟩ := tensHW_hw_eq hA hU hw hspan (hall i hi) hxi
    refine ⟨i, ?_, hxi, c, hc⟩
    rw [hi, ← hμ, sub_add_cancel]
  refine ⟨fun ν x hx hK => ?_, fun ν => ?_⟩
  · obtain ⟨i, hi, -⟩ := key ν x hx hK
    exact ⟨i, hi⟩
  · classical
    let L : khwSub ε (tensAct A M) ν →ₗ[ℂ] ({i : ι // ν = Λ + γ i} → ℂ) :=
      { toFun := fun x i => ⟪w, (x : PiLp 2 (fun _ : ι => V)) i.1⟫_ℂ
        map_add' := fun x y => by ext i; simp
        map_smul' := fun c x => by ext i; simp }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      by_contra hne
      have hx' : (x : PiLp 2 (fun _ : ι => V)) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have hK := (tensHW_mem_khwSub ε _ ν _).1 x.2
      obtain ⟨i, hi, hxi, c, hc⟩ := key ν x hx' hK
      have h1 : ⟪w, (x : PiLp 2 (fun _ : ι => V)) i⟫_ℂ = 0 := congrFun hx0 ⟨i, hi⟩
      rw [hc, inner_smul_right] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact hxi (by rw [hc, h2, zero_smul])
      · exact hxi (by rw [hc, inner_self_eq_zero.1 h2, smul_zero])
    have : FiniteDimensional ℂ (khwSub ε (tensAct A M) ν) := Module.Finite.of_injective L hL
    refine ⟨this, ?_⟩
    calc Module.finrank ℂ (khwSub ε (tensAct A M) ν)
        ≤ Module.finrank ℂ ({i : ι // ν = Λ + γ i} → ℂ) :=
          LinearMap.finrank_le_finrank_of_injective hL
      _ = Nat.card {i : ι // ν = Λ + γ i} := by
          rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem tensHW : TensHWStatement := tensHW_of lowComp

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Lin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensL_add_left (m m' : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (m + m') S = tensL m S + tensL m' S := by
  ext x i
  simp [tensL_apply, add_smul, Finset.sum_add_distrib]

theorem tensL_smul_left (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (c • m) S = c • tensL m S := by
  ext x i
  simp [tensL_apply, mul_smul, Finset.smul_sum]

theorem tensL_add_right (m : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL m (S + S') = tensL m S + tensL m S' := by
  ext x i
  simp [tensL_apply, smul_add, Finset.sum_add_distrib]

theorem tensL_smul_right (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL m (c • S) = c • tensL m S := by
  ext x i
  simp [tensL_apply, Finset.smul_sum, smul_comm c]

end Lin

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

def tensD (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) where
  toFun X := tensL (dρ X) 1 + tensL 1 (T.dτ X)
  map_add' X Y := by
    simp only [map_add (f := _), tensL_add_left, tensL_add_right]
    abel
  map_smul' c X := by
    simp only [map_smul, tensL_smul_left, tensL_smul_right, RingHom.id_apply, smul_add]

theorem tensD_apply (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensD T dρ X x i = T.dτ X (x i) + ∑ j, dρ X i j • x j := by
  simp [tensD, Matrix.one_apply, add_comm]

theorem tens_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 := by
  apply onep_KG_ext
  rw [hγ]
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
  simp

theorem tensD_hasDeriv (ρ : KG ε →* unitary (Matrix ι ι ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (hd : ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
      (dρ X i j) 0) :
    HasDerivAt (fun t : ℝ => ((tensTau T ρ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
      PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (tensD T dρ X) 0 := by
  have h0 := tens_curve_zero γ hγ
  have hD := hasDerivAt_tensL (V := T.V) hd (T.hasDeriv X hX γ hγ)
  simp only [tensTau_coe, tensOp_eq]
  convert hD using 1
  simp [tensD, h0]

theorem tensD_units (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (a b : Fin n) :
    ((tensD T dρ (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
      Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b := by
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [tensAct, tensD_apply, kunits]


include T in
def tensKRep (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) : KRep ε where
  V := PiLp 2 (fun _ : ι => T.V)
  τ := tensTau T ρ
  cont := tensTau_cont T ρ hc
  dτ := tensD T dρ
  hasDeriv X hX γ hγ := tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ)

theorem tensKRep_units (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) :
    (tensKRep T ρ dρ hc hd).units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
  funext fun a => funext fun b => tensD_units T dρ a b

theorem tensRep : TensRepStatement := by
  intro n ε Λ T ι _ _ ρ dρ hc hd
  exact ⟨tensTau T ρ, tensD T dρ, tensTau_cont T ρ hc,
    fun X hX γ hγ => tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ), fun a b => tensD_units T dρ a b⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylVanish
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem weylK_eq_zero_of_eq (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b)
    (h : (μ + rhoC ε) a = (μ + rhoC ε) b) : weylK ε μ = 0 := by
  unfold weylK
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  refine Finset.prod_eq_zero (i := b) (Finset.mem_filter.2 ⟨Finset.mem_univ b, hab, hε⟩) ?_
  rw [h, sub_self, zero_div]

theorem exists_consec_pred (ε : Fin n → Bool) {a s : Fin n} (has : a < s) (hε : ε a = ε s) :
    ∃ a', a ≤ a' ∧ a' < s ∧ ε a' = ε s ∧ ∀ c, a' < c → c < s → ε c ≠ ε a' := by
  set S := univ.filter fun c => c < s ∧ ε c = ε s with hS
  have hne : S.Nonempty := ⟨a, by simp [hS, has, hε]⟩
  have hm := S.max'_mem hne
  simp only [hS, mem_filter, mem_univ, true_and] at hm
  refine ⟨S.max' hne, S.le_max' a (by simp [hS, has, hε]), hm.1, hm.2, fun c h1 h2 he => ?_⟩
  have : c ∈ S := by simp [hS, h2, he.trans hm.2]
  exact absurd (S.le_max' c this) (not_le.2 h1)

theorem exists_consec_succ (ε : Fin n → Bool) {s b : Fin n} (hsb : s < b) (hε : ε s = ε b) :
    ∃ b', s < b' ∧ b' ≤ b ∧ ε s = ε b' ∧ ∀ c, s < c → c < b' → ε c ≠ ε s := by
  set S := univ.filter fun c => s < c ∧ ε c = ε s with hS
  have hne : S.Nonempty := ⟨b, by simp [hS, hsb, hε]⟩
  have hm := S.min'_mem hne
  simp only [hS, mem_filter, mem_univ, true_and] at hm
  refine ⟨S.min' hne, hm.1, S.min'_le b (by simp [hS, hsb, hε]), hm.2.symm, fun c h1 h2 he => ?_⟩
  have : c ∈ S := by simp [hS, h1, he]
  exact absurd (S.min'_le c this) (not_le.2 h2)

private theorem int_eq_of_le_lt {x y : ℝ} (hx : ∃ m : ℤ, x = m) (hy : ∃ m : ℤ, y = m) (h1 : x ≤ y)
    (h2 : y < x + 1) : y = x := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  have e1 : m ≤ k := by exact_mod_cast h1
  have e2 : k < m + 1 := by exact_mod_cast h2
  have : k = m := by omega
  rw [this]

theorem weylK_eq_zero_of_up (ε : Fin n → Bool) (Λ μ : Fin n → ℝ) (s : Fin n) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (hμ : ∀ c, ε c = ε s → μ c = Λ c + if c = s then 1 else 0)
    {a b : Fin n} (hab : a < b) (hε : ε a = ε b) (has : ε a = ε s) (hlt : μ a < μ b) : weylK ε μ = 0 := by
  have hbs' : ε b = ε s := hε.symm.trans has
  have hma := hμ a has
  have hmb := hμ b hbs'
  have hΛ := hdom a b hab hε

  have hbs : b = s := by
    by_contra hne
    rw [if_neg hne] at hmb
    split_ifs at hma <;> linarith
  subst hbs
  have has' : a ≠ b := ne_of_lt hab
  rw [if_neg has'] at hma
  rw [if_pos rfl] at hmb
  have hEq : Λ a = Λ b := int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)
  obtain ⟨a', haa', ha's, hε', hc⟩ := exists_consec_pred ε hab hε
  have hΛ' : Λ a' = Λ b := by
    have h1 : Λ b ≤ Λ a' := hdom a' b ha's hε'
    have h2 : Λ a' ≤ Λ a := by
      rcases eq_or_lt_of_le haa' with h | h
      · rw [h]
      · exact hdom a a' h (hε.trans hε'.symm)
    linarith
  have hρ := rhoC_consec ε ha's hε' hc
  have hma' := hμ a' hε'
  rw [if_neg (ne_of_lt ha's)] at hma'
  refine weylK_eq_zero_of_eq ε μ ha's hε' ?_
  simp only [Pi.add_apply]
  linarith

theorem weylK_eq_zero_of_down (ε : Fin n → Bool) (Λ μ : Fin n → ℝ) (s : Fin n) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (hμ : ∀ c, ε c = ε s → μ c = Λ c - if c = s then 1 else 0)
    {a b : Fin n} (hab : a < b) (hε : ε a = ε b) (has : ε a = ε s) (hlt : μ a < μ b) : weylK ε μ = 0 := by
  have hbs' : ε b = ε s := hε.symm.trans has
  have hma := hμ a has
  have hmb := hμ b hbs'
  have hΛ := hdom a b hab hε

  have has : a = s := by
    by_contra hne
    rw [if_neg hne] at hma
    split_ifs at hmb <;> linarith
  subst has
  rw [if_neg (ne_of_lt hab).symm] at hmb
  rw [if_pos rfl] at hma
  have hEq : Λ a = Λ b := int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)
  obtain ⟨b', hab', hb'b, hε', hc⟩ := exists_consec_succ ε hab hε
  have hΛ' : Λ b' = Λ a := by
    have h1 : Λ b' ≤ Λ a := hdom a b' hab' hε'
    have h2 : Λ b ≤ Λ b' := by
      rcases eq_or_lt_of_le hb'b with h | h
      · rw [h]
      · exact hdom b' b h (hε'.symm.trans hε)
    linarith
  have hρ := rhoC_consec ε hab' hε' hc
  have hmb' := hμ b' hε'.symm
  rw [if_neg (ne_of_lt hab').symm] at hmb'
  refine weylK_eq_zero_of_eq ε μ hab' hε' ?_
  simp only [Pi.add_apply]
  linarith

theorem exists_viol_of_not_kDom (ε : Fin n → Bool) (μ : Fin n → ℝ) (h : ¬ KDom ε μ) :
    ∃ a b, a < b ∧ ε a = ε b ∧ μ a < μ b := by
  unfold KDom at h
  push Not at h
  obtain ⟨a, b, hab, hε, hlt⟩ := h
  exact ⟨a, b, hab, hε, hlt⟩

theorem weylK_std_vanish (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (s : Fin n) (h : ¬ KDom ε (Λ + stdWt n s)) : weylK ε (Λ + stdWt n s) = 0 := by
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + stdWt n s) c = Λ c + if c = s then 1 else 0 := by
    intro c
    simp only [Pi.add_apply, stdWt, Pi.single_apply]
  by_cases has : ε a = ε s
  · exact weylK_eq_zero_of_up ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt
  · exfalso
    have ha : a ≠ s := fun h => has (h ▸ rfl)
    have hb : b ≠ s := fun h => has (h ▸ hε)
    rw [hμ, hμ, if_neg ha, if_neg hb] at hlt
    linarith [hdom a b hab hε]

theorem weylK_dual_vanish (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (s : Fin n) (h : ¬ KDom ε (Λ + dualWt n s)) : weylK ε (Λ + dualWt n s) = 0 := by
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + dualWt n s) c = Λ c - if c = s then 1 else 0 := by
    intro c
    simp only [Pi.add_apply, dualWt, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> ring
  by_cases has : ε a = ε s
  · exact weylK_eq_zero_of_down ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt
  · exfalso
    have ha : a ≠ s := fun h => has (h ▸ rfl)
    have hb : b ≠ s := fun h => has (h ▸ hε)
    rw [hμ, hμ, if_neg ha, if_neg hb] at hlt
    linarith [hdom a b hab hε]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

