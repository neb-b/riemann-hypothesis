module

public import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoeffIdentityPlainChartOfThree
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem sg_lin (X : RawChart C d I κ) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    X.sg (fun i => ∑ q, m q * u q i) = ∑ q, m q • X.sg (u q) := by
  apply MvPowerSeries.ext
  intro μ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  show -∑ i, (∑ q, m q * u q i) * _ = ∑ q, m q * -∑ i, u q i * _
  simp only [Finset.sum_mul, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem alongCv_lin {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {ι : Type} [Fintype ι]
    (m : ι → C) (f : ι → MvPowerSeries κ C) : alongCv γ (∑ q, m q • f q) = ∑ q, m q • alongCv γ (f q) := by
  have hS : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  unfold alongCv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← MvPowerSeries.substAlgHom_apply hS, map_sum, map_smul]

theorem phi_lin (X : RawChart C d I κ) (l : ℕ) (hl : 0 < l) (ζ : C) {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    phi X l ζ γ δ (fun i => ∑ q, m q * u q i) = ∑ q, m q • phi X l ζ γ δ (u q) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  unfold phi
  rw [sg_lin, alongCv_lin hγ, alongCv_lin hδ]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [← PowerSeries.coe_substAlgHom hS, map_sum, map_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
    ring

theorem ge_of_mm {V : VF C} {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.MM at h
  unfold VF.Ge
  exact_mod_cast le_of_lt h

theorem mm_pow_sub {V : VF C} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a - b)) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  rw [← geom_sum₂_mul]
  exact mm_mul_ge' (VF.Ge.sum fun i _ => by simpa using (ha.pow i).mul (hb.pow (n - 1 - i))) h

theorem coeffIdentity_plainChart_of_three [IsAlgClosed C] [CharZero C] (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g)
    (hA : StepA X V H) (hB : StepB X V) (hC : LemC X V) : IndependenceBoundPlain.PlainCoefficientIdentity X H := by
  intro _ g a _
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have hl0 : 0 < V.l := V.l_prime.pos
  choose z ε m hz hε hrel hz1 hε1 hm using hB ζ hζ g
  refine ⟨fun q' q => m q q', fun w x hg hV => ?_⟩
  obtain ⟨γ, δ, hγ, hδ, hrel', hmm, hq⟩ := hA ζ hζ g a w x hg hV
  refine ⟨fun q' => (V.l : C) * x 2 (Sum.inr q'), fun q hne => ?_, fun q => ?_⟩
  · have h2 := hg.1.2.2 2 (Sum.inr q) (by
      show X.ty (1 - g) q ≠ a + ((2 : ℕ) : ZMod d)
      simpa using hne)
    show (V.l : C) * x 2 (Sum.inr q) = 0
    rw [h2, mul_zero]
  · have h1 := hC ζ hζ γ δ (z q) (ε q) hγ hδ (hz q) (hε q) hrel' (hrel q) hmm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [funext (hz1 q), funext (hε1 q), phi_lin X V.l hl0 ζ (fun i => (hγ i).1) (fun i => (hδ i).1), map_sum] at h1
    simp only [PowerSeries.coeff_smul, smul_eq_mul] at h1
    obtain ⟨hc0, hcA, _⟩ := hq q
    have hAint : V.Ge 0 (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q))) := by
      have := (ge_of_mm hcA).add hc0
      simpa using this
    have h3 := mm_pow_sub hAint hc0 hcA V.l
    have h4 : V.MM (∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
        (V.l : C) * x 2 (Sum.inr q'))) := mm_sum _ _ fun q' _ => mm_mul_ge' (hm q q') (hq q').2.2
    have e : (RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' =
        -(PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l - (RawChart.cart (H g)).c0' x q ^ V.l) +
        ((PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l -
          ∑ q', m q q' * PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q'))) +
        ∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
          (V.l : C) * x 2 (Sum.inr q'))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' = ∑ q', m q q' * ((V.l : C) * x 2 (Sum.inr q')) :=
        Finset.sum_congr rfl fun q' _ => by ring
      rw [this]
      ring
    rw [e]
    exact mm_add (mm_neg h3) (mm_add h1 h4)

end SelfConjCharts

section Self

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

theorem FBChart.rawSelf_axis1 (Y : FBChart C V O dd) (p : SelfData Y d I0) (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ 1) : MvPowerSeries.coeff e (Y.rawSelf p).h = 0 := by
  show MvPowerSeries.coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 1 Y.h (gauge_axes Y 1)) e he

theorem FBChart.rawSelf_basic (Y : FBChart C V O dd) (p : SelfData Y d I0) : SelfConjCharts.Basic (Y.rawSelf p) V := by
  exact
    { lg0 := Y.self_chart_log_constantCoeff p
      exlg := Y.rawSelf_exlg p
      lin := Y.rawSelf_lin p
      axis0 := Y.rawSelf_axis0 p
      axis1 := Y.rawSelf_axis1 p
      uint := Y.rawSelf_u_integral p
      hmis := hStabSelf_holds C V O dd Y d I0 p }

end Self

theorem coeffIdentity_selfConj_of_four (hA : GoodCurveClosed) (hB : OtherGroupCurvesClosed) (hC : MixedCoefficientClosed) (hD : BiadditiveOnColumns) : CoefficientIdentitySelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p _ H
  have := Y.algClosed
  have hb := Y.rawSelf_basic p
  exact SelfConjCharts.coeffIdentity_plainChart_of_three (Y.rawSelf p) V H (hA C V d _ _ _ hb H) (hB C V d _ _ _ hb H)
    (hC C V d _ _ _ hb (hD C V O dd Y d I0 p))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoeffOneAlongCvLg
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_tyS_Fs {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) := by
  rw [← tyS_Vpow hl]
  apply tyS_eq hl
  · intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
    rw [← Finset.sum_mul]
    cases s with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ s =>
      have h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  · intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

theorem rescale_sum_smul {ι : Type} [Fintype ι] (a : C) (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.rescale a (∑ c, u c • f c) = ∑ c, u c • PowerSeries.rescale a (f c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem subst_pow_sum_smul {n : ℕ} (hn : 0 < n) {ι : Type} [Fintype ι] (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (∑ c, u c • f c) =
      ∑ c, u c • PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (f c) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← PowerSeries.coe_substAlgHom hS, map_sum]
  simp only [map_smul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem coeff_one_alongCv_lg (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    PowerSeries.coeff 1 (alongCv γ (X.lg i)) = PowerSeries.coeff 1 (γ i) := by
  rw [coeff_alongCv_low le_rfl (fun j m hm => by
      have : m = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]
  rw [Finset.sum_eq_single i]
  · rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]
    intro h
    exact hj (Finsupp.single_left_injective one_ne_zero h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_one_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.coeff 1 (tyS l a) = a 0 := by
  have h := coeff_tyS_pow hl a 0
  rwa [pow_zero] at h

theorem coeff_one_of_mem (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {g : Fin 2} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {x : ℕ → I g ⊕ JJ I g → C}
    (h1 : ∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) (i : κ) :
    PowerSeries.coeff 1 (γ i) = ∑ c : I g, X.u g c i * x 0 (Sum.inl c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]

end SelfConjCharts

open SelfConjCharts in
theorem r1sRestB_holds : OtherGroupCurvesClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g q
  have hl2 := V.l_prime.two_le
  set g' : Fin 2 := 1 - g with hg'
  obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0)
    (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one])
    (fun c hc => by
      rw [if_neg]
      rintro rfl
      exact hc rfl)
  have hF := (H g').Fm x hx
  obtain ⟨z, -, hz, -, hz1, -⟩ := id hx
  obtain ⟨ε, -, hε, -, hε1, -⟩ := hF
  refine ⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hε1 i, hz1 i, subst_pow_sum_smul (by omega)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    exact subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]
    simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro q'
    exact (H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

end SelfConjCharts

open SelfConjCharts

def PowerSeriesFrobeniusCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f → ∀ μ : σ →₀ ℕ,
    V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l)

def RootsOfUnityProductCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2) (f : MvPowerSeries (Fin 2) C), IntS V f →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (∏ k ∈ Finset.range V.l, rs j (ζ ^ k) f - f ^ V.l))

def ExpLowOrderTruncation : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (F : MvPowerSeries (Fin 2) C) (m : ℕ), 1 ≤ m →
    (∀ i j, j < m → MvPowerSeries.coeff (ee i j) F = 0) →
    ∀ i j, j < 2 * m → MvPowerSeries.coeff (ee i j) (mvExp F) =
      MvPowerSeries.coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) + MvPowerSeries.coeff (ee i j) F

def GaugeLeadingTermLinear : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ),
    (∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0) →
    ∀ x c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) → ∀ m : ℕ, 1 ≤ m →
    (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
    (∀ n j, j < m → MvPowerSeries.coeff (ee n j) (HH X x c) = 0) ∧
      ∀ n, MvPowerSeries.coeff (ee n m) (HH X x c) =
        -PowerSeries.coeff n (alongCv x (X.sg fun i => PowerSeries.coeff m (c i)))

def GaugeRescalingSymmetry : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (x i) = 0) →
    (∀ i, PowerSeries.constantCoeff (z i) = 0) → ∀ c : C,
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z)

def IntegralUnitFamilies : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ γ δ c : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V c → NormRel X V.l n ζ γ δ →
    IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ)))

def GenericPointUnitCongruence : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ z ε δ : κ → PowerSeries C, IsCv V z → IsCv V ε → IsCv V δ → NormRel X V.l n ζ z ε →
    (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) → ∀ N : ℕ, 0 < N → ∀ i j, i ≤ N →
    V.MM (MvPowerSeries.coeff (ee i j)
      (mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
section
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.SelectionLemmas

open Formalism.MainNotions.G

variable {p : ℕ} {O : Type} [CommRing O]

def esymmOn {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ B ∈ VV.powersetCard k, ∏ v ∈ B, κ v

def monoN (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (x : G.Fn) : G.Fn :=
  ((p : G.O) ^ (∑ v ∈ VV \ B, Sv v)) •
    ((B.sort (· ≤ ·)).foldr (fun v f => (G.yv v)^[m] ∘ f) id) x

def prodIdeal (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (M : Submodule G.O G.Fn) : Submodule G.O G.Fn :=
  Submodule.span G.O (⋃ B ∈ VV.powerset, monoN G VV B m Sv '' (M : Set G.Fn))

def tau {ι : Type} (VV : Finset ι) (m D : ℕ) (t : ι → ℕ) : ℕ := ∑ v ∈ VV, m * (t v + D + 1)

def IsSaturatedIn {X : Type} [AddCommGroup X] [Module O X] (M' M : Submodule O X) : Prop :=
  M' ≤ M ∧ ∀ (a : O) (x : X), x ∈ M → a ≠ 0 → a • x ∈ M' → x ∈ M'

def adm1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.TrivStab

def adm2 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.FinClasses

def adm3 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F)

def admitted (D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := adm1 D G ∧ adm2 D G ∧ adm3 D G

def Conclusion1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ),
    1 ≤ m → (∀ v ∈ VV, Sv v ≤ S) →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
      (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    let M := G.Mna
    let d : ℕ := G.dna
    let N := prodIdeal G VV m Sv M
    let τ : ℕ := tau VV m Dd t
    ((∀ β : ℕ, Formalism.G0.AllButLE (p : G.O) M N
        ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S)) ∧
      Formalism.G0.AllButLE (p : G.O) M N 0 (∑ v ∈ VV, Sv v)) ∧
    ((m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2 →
      let Sig : ℝ := (m : ℝ) * ∑ v ∈ VV, κ v
      let Nst := N ⊓ (Ideal.span {(p : G.O) ^ τ}) • M
      (∀ β : ℕ, (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) ≤
          (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ)) ∧
      (∃ ℓ : ℕ, Module.length G.O (↥M ⧸ Submodule.comap M.subtype Nst) = ℓ ∧
        (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
          ((d : ℝ) * τ + 2 * S * Sig * d)) ∧
      ∀ (M' : Submodule G.O G.Fn) (hM' : IsSaturatedIn M' M),
        Nst ⊓ M' ≤ (Ideal.span {(p : G.O) ^ τ}) • M' ∧
        Function.Injective (Submodule.mapQ (Submodule.comap M'.subtype Nst) (Submodule.comap M.subtype Nst)
          (Submodule.inclusion hM'.1) (fun _ hx => hx)) ∧
        ∀ (Y : Type) [AddCommGroup Y] [Module G.O Y] (K : G.Fn →ₗ[G.O] Y) (Z : Submodule G.O Y),
          N.map K ≤ Z → (Nst ⊓ M').map K ≤ Z)

end Formalism.MainNotions.SelectionLemmas
end
end

