module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

@[expose] public section

noncomputable section
open PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomOne

def wK (d : ℕ) : ℂ := (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def InOK (d : ℕ) (z : ℂ) : Prop := ∃ u v : ℤ, z = (u : ℂ) + (v : ℂ) * wK d

def Split (d q : ℕ) : Prop := (q = 2 ∧ d % 8 = 7) ∨ (q ≠ 2 ∧ jacobiSym (-(d : ℤ)) q = 1)

def eis (d k : ℕ) : ℂ := ∑' w : {w : ℂ // InOK d w ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def discr (d : ℕ) : ℂ := (60 * eis d 2) ^ 3 - 27 * (140 * eis d 3) ^ 2

def IsOK (d : ℕ) (L : PeriodPair) : Prop := ∀ z : ℂ, z ∈ L.lattice ↔ InOK d z

def h1 (d : ℕ) (z w : ℂ) : ℂ := ((2 / Real.sqrt d : ℝ) : ℂ) * (z * conj w)

def U1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (z + x) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)

def W1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * U1 d x F z

def kap1 (d : ℕ) (x y : ℂ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d x y).im : ℝ) : ℂ))

def IsTh (d : ℕ) (θ : ℂ → ℂ) : Prop :=
  Differentiable ℂ θ ∧ θ 0 = 1 ∧ (∀ z, θ (-z) = θ z) ∧ (∀ x, InOK d x → W1 d x θ = θ) ∧
    ∀ z, θ z = 0 → InOK d (z - 1 / 2)

def PrimeTo (d q : ℕ) (t : ℂ) : Prop := ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ InOK d ((s : ℂ) * t)

def tay (G : ℂ → ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun n => iteratedDeriv n G 0 / (n.factorial : ℂ)

def Ell (L : PeriodPair) (φ : ℂ → ℂ) : Prop := Meromorphic φ ∧ ∀ l ∈ L.lattice, ∀ z, φ (z + l) = φ z

variable {q : ℕ} [Fact q.Prime]

def zc (a : ℤ_[q]) : ℂ_[q] := algebraMap ℚ_[q] ℂ_[q] (a : ℚ_[q])

def logS : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) / (n : ℂ_[q])

def mulS (a : ℤ_[q]) : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else zc (Ring.choose a n)

def DT (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ := (1 + X) * PowerSeries.derivative f

def Bd (C : ℝ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ C

def Bdd (f : ℂ_[q]⟦X⟧) : Prop := ∃ C, Bd C f

def ev (f : ℂ_[q]⟦X⟧) (x : ℂ_[q]) : ℂ_[q] := ∑' n, coeff n f * x ^ n

def shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ :=
  PowerSeries.mk fun n => ∑' m, coeff m f * ((m.choose n : ℂ_[q]) * ζ ^ n * (ζ - 1) ^ (m - n))

def hat (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (G : ℂ → ℂ) : ℂ_[q]⟦X⟧ :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay G)).subst ℓ

structure Mdl (q : ℕ) [Fact q.Prime] where

  ι : ℂ ≃+* ℂ_[q]

  L : PeriodPair

  c : ℂ

  W : WeierstrassCurve ℂ_[q]

namespace Mdl
variable (M : Mdl q)

def Ok : Prop :=
  M.c ≠ 0 ∧ ‖M.W.a₁‖ ≤ 1 ∧ ‖M.W.a₂‖ ≤ 1 ∧ ‖M.W.a₃‖ ≤ 1 ∧ ‖M.W.a₄‖ ≤ 1 ∧ ‖M.W.a₆‖ ≤ 1 ∧ ‖M.W.Δ‖ = 1 ∧
    M.W.c₄ / 12 = M.ι (M.L.g₂ / M.c ^ 4) ∧ M.W.c₆ / 216 = M.ι (M.L.g₃ / M.c ^ 6)

def x (z : ℂ) : ℂ := M.L.weierstrassP z / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)

def y (z : ℂ) : ℂ :=
  (M.L.derivWeierstrassP z / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x z - M.ι.symm M.W.a₃) / 2


open Classical in
def u (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -M.x z / M.y z


open Classical in
def w (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -1 / M.y z

def Small (z : ℂ) : Prop := z ∈ M.L.lattice ∨ 1 < ‖M.ι (M.x z)‖

def Chart (ℓ : ℂ_[q]⟦X⟧) : Prop :=
  M.Ok ∧ constantCoeff ℓ = 0 ∧ Bd 1 (hat M.ι ℓ M.u) ∧ ‖coeff 1 (hat M.ι ℓ M.u)‖ = 1

def MChart (ω : ℂ_[q]) : Prop := M.Chart (C ω * logS)

def At (ω ζ : ℂ_[q]) (z : ℂ) : Prop :=
  M.Small z ∧ ‖ζ - 1‖ < 1 ∧ ev (hat M.ι (C ω * logS) M.u) (ζ - 1) = M.ι (M.u z)

end Mdl

def Good (ι : ℂ ≃+* ℂ_[q]) (d n s : ℕ) (y : ℂ) : Prop :=
  ∃ v : ℂ, InOK d v ∧ ‖ι (conj v)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ y = (s : ℂ) * v / (q : ℂ) ^ n

def ThetaLaws (ι : ℂ ≃+* ℂ_[q]) (d : ℕ) (ω : ℂ_[q]) (θ : ℂ → ℂ) : Prop :=
  (∀ t, PrimeTo d q t → Bd 1 (hat ι (C ω * logS) (U1 d t θ))) ∧
  (∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y →
    ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧
    hat ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (ι (kap1 d 1 y)) (hat ι (C ω * logS) (U1 d t θ))) ∧
  ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d (s j) θ) ^ a) →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a)

namespace Basic
open Filter Topology


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.discr_eq {d : ℕ} {L : PeriodPair}
    (h : _root_.GlobalTheory.MomOne.IsOK d L) :
    _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ∧
      _root_.GlobalTheory.MomOne.discr d ≠ 0 := by
  have hG : ∀ k, 0 < k → _root_.GlobalTheory.MomOne.eis d k = L.G (2 * k) := by
    intro k hk
    unfold _root_.GlobalTheory.MomOne.eis PeriodPair.G
    have e1 := tsum_subtype {w : ℂ | _root_.GlobalTheory.MomOne.InOK d w ∧ w ≠ 0}
      (fun w : ℂ => 1 / w ^ (2 * k))
    have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    ext z
    by_cases hz : z = 0
    · subst hz
      have : (2 * k) ≠ 0 := by omega
      simp [Set.indicator, zero_pow this]
    · have hz' : z ∈ (L.lattice : Set ℂ) ↔ _root_.GlobalTheory.MomOne.InOK d z := h z
      by_cases hm : _root_.GlobalTheory.MomOne.InOK d z
      · simp [Set.indicator, hz, hm, hz'.2 hm]
      · simp [Set.indicator, hm, mt hz'.1 hm]
  have hdisc : _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
    unfold _root_.GlobalTheory.MomOne.discr PeriodPair.g₂ PeriodPair.g₃
    rw [hG 2 (by norm_num), hG 3 (by norm_num)]
  refine ⟨hdisc, ?_⟩
  rw [hdisc, ← _root_.GlobalTheory.latticeCurve_Δ]
  exact _root_.GlobalTheory.latticeCurve_Δ_ne_zero L

def okPair (d : ℕ) (hd : 0 < d) : PeriodPair := ⟨1, wK d, LinearIndependent.pair_iff.2 fun s t h => by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1 := congrArg Complex.re h
  simp [wK, hs] at h1 h2
  subst h2
  exact ⟨by simpa using h1, rfl⟩⟩


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.isOK_okPair (d : ℕ) (hd : 0 < d) :
    _root_.GlobalTheory.MomOne.IsOK d (_root_.GlobalTheory.MomOne.Basic.okPair d hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨u, v, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
private theorem cardinal_le_seq_of_denseRange {X Y : Type} [TopologicalSpace X]
    [FrechetUrysohnSpace X] [T2Space X] (i : Y → X) (hi : DenseRange i) : #X ≤ #(ℕ → Y) := by
  have h : ∀ x : X, ∃ u : ℕ → Y, Tendsto (i ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range i) := by rw [hi.closure_range]; trivial
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have : i ∘ u = v := funext fun n => hu n
    rw [this]; exact hlim
  choose u hu using h
  refine Cardinal.mk_le_of_injective (f := u) fun x y hxy => ?_
  have := hu y
  rw [← hxy] at this
  exact tendsto_nhds_unique (hu x) this

open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
private theorem cardinal_padicComplex_eq_continuum (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  have hQ : #ℚ_[q] ≤ 𝔠 := by
    calc #ℚ_[q] ≤ #(ℕ → ℚ) := cardinal_le_seq_of_denseRange _ (Padic.denseRange_ratCast q)
      _ = 𝔠 := by rw [← power_def, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat, aleph0_power_aleph0]
  have hA : #(PadicAlgCl q) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
      (max_le hQ aleph0_le_continuum)
  apply le_antisymm
  · calc #ℂ_[q] ≤ #(ℕ → PadicAlgCl q) :=
          cardinal_le_seq_of_denseRange _ UniformSpace.Completion.denseRange_coe
      _ = #(PadicAlgCl q) ^ ℵ₀ := by rw [← power_def, Cardinal.mk_nat]
      _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right hA
      _ = 𝔠 := continuum_power_aleph0
  · obtain ⟨f, -, -, hf⟩ := Perfect.exists_nat_bool_injection
      (PerfectSpace.univ_perfect (α := ℚ_[q])) ⟨0, trivial⟩
    calc 𝔠 = #(ℕ → Bool) := by rw [← power_def, mk_bool, Cardinal.mk_nat, two_power_aleph0]
      _ ≤ #ℚ_[q] := mk_le_of_injective hf
      _ ≤ #ℂ_[q] := mk_le_of_injective (algebraMap ℚ_[q] ℂ_[q]).injective


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
theorem _root_.GlobalTheory.MomOne.Basic.nonempty_iso (q : ℕ) [Fact q.Prime] :
    Nonempty (ℂ ≃+* ℂ_[q]) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  · exact Cardinal.eq.1 (by rw [Cardinal.mk_complex, cardinal_padicComplex_eq_continuum])


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.norm_nat_eq_one {m : ℕ} (h : Nat.Coprime q m) :
    ‖(m : ℂ_[q])‖ = 1 := by
  have h1 : (m : ℂ_[q]) = (((m : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact h

theorem hasDerivAt_u (M : Mdl q) (hc : M.c ≠ 0) : HasDerivAt M.u M.c 0 := by
  have ha := M.L.analyticAt_weierstrassPExcept 0
  have hb := M.L.analyticAt_derivWeierstrassPExcept 0
  set β := M.ι.symm (M.W.b₂ / 12)
  set a1 := M.ι.symm M.W.a₁
  set a3 := M.ι.symm M.W.a₃
  obtain ⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun z => (1 + z ^ 2 * M.L.weierstrassPExcept 0 z) / M.c ^ 2 - β * z ^ 2 := ⟨_, rfl⟩
  have hA : AnalyticAt ℂ A 0 := by rw [hAd]; fun_prop
  obtain ⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun z =>
      ((z ^ 3 * M.L.derivWeierstrassPExcept 0 z - 2) / M.c ^ 3 - a1 * z * A z - a3 * z ^ 3) / 2 := ⟨_, rfl⟩
  have hB : AnalyticAt ℂ B 0 := by rw [hBd]; fun_prop
  have hA0 : A 0 = 1 / M.c ^ 2 := by simp [hAd]
  have hB0 : B 0 = -1 / M.c ^ 3 := by simp [hBd]; ring
  have hB0' : B 0 ≠ 0 := by rw [hB0]; exact div_ne_zero (by norm_num) (pow_ne_zero _ hc)
  have hx : ∀ z : ℂ, z ≠ 0 → M.x z = A z / z ^ 2 := by
    intro z hz
    have h := M.L.weierstrassPExcept_add 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.x, ← h, hAd]
    field_simp
    ring
  have hy : ∀ z : ℂ, z ≠ 0 → M.y z = B z / z ^ 3 := by
    intro z hz
    have h := M.L.derivWeierstrassPExcept_sub 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.y, ← h, hBd, hx z hz]
    simp only [a1, a3]
    field_simp
  have hQ : AnalyticAt ℂ (fun z => -A z / B z) 0 := hA.neg.div hB hB0'
  have h := (hasDerivAt_id (0 : ℂ)).mul hQ.differentiableAt.hasDerivAt
  have e : -A 0 / B 0 = M.c := by rw [hA0, hB0]; field_simp
  simp only [id, zero_mul, add_zero, one_mul, e] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hB.continuousAt.eventually_ne hB0', M.L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h2 h3
  by_cases hz : z = 0
  · subst hz; simp [Mdl.u]
  · have : z ∉ M.L.lattice := fun h => h3 ⟨h, hz⟩
    simp only [Mdl.u, ite_eq_right this, hx z hz, hy z hz, Pi.mul_apply, id]
    field_simp

theorem exists_chart (M : Mdl q) (h : M.Ok) : ∃ ℓ, M.Chart ℓ ∧ hat M.ι ℓ M.u = X := by
  set P := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hP
  have h0 : constantCoeff P = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hP, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  have h1 : IsUnit (coeff 1 P) := by
    rw [hP, coeff_map, tay, coeff_mk]
    simp [(hasDerivAt_u M h.1).deriv, h.1]
  have e : hat M.ι (P.substInvOfIsUnit h1) M.u = X := subst_substInvOfIsUnit_right P h0 h1
  refine ⟨P.substInvOfIsUnit h1, ⟨h, constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩, e⟩
  · intro n; rw [e, coeff_X]; split_ifs <;> simp
  · rw [e]; simp


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.cmLatticeCommutatorPairing_pow_eq_one_of_good_lift (ι : ℂ ≃+* ℂ_[q]) {d n s : ℕ}
    (hd : 0 < d) {y : ℂ} (h : _root_.GlobalTheory.MomOne.Good ι d n s y) :
    ι (_root_.GlobalTheory.MomOne.kap1 d 1 y) ^ (q ^ n) = 1 := by
  obtain ⟨v, ⟨u, w, rfl⟩, -, rfl⟩ := h
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hs : Real.sqrt d ≠ 0 := by positivity
  have hd2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have him : ((q : ℂ) ^ n).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_im]
  have hre : ((q : ℂ) ^ n).re = (q : ℝ) ^ n := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hIm : (_root_.GlobalTheory.MomOne.h1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) *
      _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n)).im = -((s : ℝ) * w) / (q : ℝ) ^ n := by
    simp [_root_.GlobalTheory.MomOne.h1, _root_.GlobalTheory.MomOne.wK, Complex.div_im,
      Complex.div_re, Complex.mul_im, Complex.mul_re, him, hre]
    field_simp
    rw [hd2]
    ring
  have key : _root_.GlobalTheory.MomOne.kap1 d 1 ((s : ℂ) * ((u : ℂ) + (w : ℂ) *
      _root_.GlobalTheory.MomOne.wK d) / (q : ℂ) ^ n) ^ (q ^ n) = 1 := by
    unfold _root_.GlobalTheory.MomOne.kap1
    rw [← Complex.exp_nat_mul, hIm]
    have hqn : ((q : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
    have : ((q ^ n : ℕ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) *
        ((-((s : ℝ) * w) / (q : ℝ) ^ n : ℝ) : ℂ)) = ((s * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [← map_pow, key, map_one]


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.cmLatticeHermitianForm_mul_left (d : ℕ) (a z w : ℂ) :
    _root_.GlobalTheory.MomOne.h1 d (a * z) w = a * _root_.GlobalTheory.MomOne.h1 d z w := by
  unfold _root_.GlobalTheory.MomOne.h1; ring


open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
theorem _root_.GlobalTheory.MomOne.Basic.shiftS_one (f : ℂ_[q]⟦X⟧) :
    _root_.GlobalTheory.MomOne.shiftS 1 f = f := by
  ext n
  rw [_root_.GlobalTheory.MomOne.shiftS, coeff_mk, tsum_eq_single n]
  · simp
  · intro m hm
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have : m - n ≠ 0 := by omega
      simp [zero_pow this]

end Basic

end GlobalTheory.MomOne
