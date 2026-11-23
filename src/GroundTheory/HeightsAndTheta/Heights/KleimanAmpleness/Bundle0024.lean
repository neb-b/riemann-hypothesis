module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionPowers
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionSystems
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def redSys (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : SubSystem k y K' where
  sub I := Submodule.span (chartRing k y I)
    ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy I))
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing k y J)
      ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy J))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, P.mono _ _ h q hq, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

def RedGood (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : Prop :=
  ∀ (I : Chart y), ∀ q ∈ P.sub (liftChart hxy I), q / γ ∈ locAt k x y

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem mem_redSys_iff {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ q ∈ P.sub (liftChart hxy I),
      redAt k x y (q / γ) = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, by rw [zero_div]; exact (locAt_zero hsp).2⟩
    · rintro u v _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      refine ⟨q + q', Submodule.add_mem _ hq hq', ?_⟩
      rw [add_div]; exact (locAt_add hsp (hP I q hq) (hP I q' hq')).2
    · rintro c u _ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, hac⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I c.2
      refine ⟨a * q, ?_, ?_⟩
      · have := Submodule.smul_mem _ (⟨a, ha⟩ : chartRing k x (liftChart hxy I)) hq
        rwa [chartRing_smul_def] at this
      · rw [chartRing_smul_def, ← hac, mul_div_assoc]
        exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I ha).1 (hP I q hq)).2
  · rintro ⟨q, hq, rfl⟩; exact Submodule.subset_span ⟨q, hq, rfl⟩

theorem redGood_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) : RedGood hxy (P.twist Q) (γ * δ) := by
  intro I z hz
  refine Submodule.span_induction (p := fun z _ => z / (γ * δ) ∈ locAt k x y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, p, hp, rfl⟩
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    rw [this]; exact (locAt_mul hsp (hQ I q hq) (hP I p hp)).1
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

theorem redSys_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) :
    redSys hxy (P.twist Q) (γ * δ) = (redSys hxy P γ).twist (redSys hxy Q δ) := by
  have hPQ := redGood_twist hsp hxy hP hQ
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction (p := fun z _ => redAt k x y (z / (γ * δ)) ∈
      ((redSys hxy P γ).twist (redSys hxy Q δ)).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, p, hp, rfl⟩
      have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
      rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨q, hq, rfl⟩, _,
        Submodule.subset_span ⟨p, hp, rfl⟩, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hPQ I u hu) (hPQ I v hv)).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hPQ I u hu)).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q', hq', p', hp', rfl⟩
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hQ I q').mp hq'
    obtain ⟨p, hp, rfl⟩ := (mem_redSys_iff hsp hxy hP I p').mp hp'
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    refine Submodule.subset_span ⟨q • p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, ?_⟩
    change redAt k x y (q • p / (γ * δ)) = redAt k x y (q / δ) * redAt k x y (p / γ)
    rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]

theorem redGood_twistSys_zero : RedGood hxy (twistSys k x 0) 1 := by
  intro I q hq
  rw [div_one]; exact (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).1

theorem redSys_twistSys_zero : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    change redAt k x y (q / 1) ∈ twistMod k y 0 I
    rw [div_one]
    exact res_mem_twistMod_zero_of_mem_chartRing
      (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hz)
    exact Submodule.subset_span ⟨a, res_mem_twistMod_zero_of_mem_chartRing ha, by
      change redAt k x y (a / 1) = redAt k x y a
      rw [div_one]⟩

theorem redSys_pow {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (n : ℕ) :
    RedGood hxy (P.pow n) (γ ^ n) ∧ redSys hxy (P.pow n) (γ ^ n) = (redSys hxy P γ).pow n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨redGood_twistSys_zero hsp hxy, redSys_twistSys_zero hsp hxy⟩
  | succ n ih =>
    rw [pow_succ]
    change RedGood hxy ((P.pow n).twist P) (γ ^ n * γ) ∧
      redSys hxy ((P.pow n).twist P) (γ ^ n * γ) = ((redSys hxy P γ).pow n).twist (redSys hxy P γ)
    exact ⟨redGood_twist hsp hxy ih.1 hP, by rw [redSys_twist hsp hxy ih.1 hP, ih.2]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Lift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ s : Chart x → Ω,
      (∀ I, s I ∈ ((T.L.pow b).twist (twistSys k x c)).sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I₂) →
      ∃ t ∈ ((T.L.pow b).twist (twistSys k x c)).secs, ∀ I, t - s I ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (Nf : Fin (n + 1) → FinGradedSub (S := S) (x := x) E) (g : Fin n → E) (deg : Fin n → ℤ)
      (pr : Fin n → Ideal (Poly S N)),
      Nf 0 = M₂ ∧ Nf (Fin.last n) = M₁ ∧
      ∀ k : Fin n, (pr k).IsPrime ∧ (∀ p ∈ pr k, ∀ d : ℕ, homogeneousComponent d p ∈ pr k) ∧
        primeOf (S := S) x ≤ pr k ∧
        (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr k) ∧
        g k ∈ (Nf k.succ).piece (deg k) ∧
        (∀ c, (Nf k.succ).piece c = (Nf k.castSucc).piece c ⊔ Submodule.span S
          {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ deg k + d = c ∧ z = aeval x f • g k}) ∧
        ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d →
          (f ∈ pr k ↔ aeval x f • g k ∈ (Nf k.castSucc).piece (deg k + d))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoPieceSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Piece.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (N₀ N₁ : FinGradedSub (S := S) (x := x) E) (g : E) (e : ℤ)
    (pp : Ideal (Poly S N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → g ∈ N₁.piece e →
    (∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g}) →
    (∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) →
    ∀ (Q : LineBundle S x) (c : ℤ),
      ((∃ j, (X j : Poly S N) ∉ pp) →
        Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
          ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1)) →
      Subsingleton (SubSystem.quotH ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
        ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


variable (S x E) in
def FinGradedSub.zero : FinGradedSub (S := S) (x := x) E where
  piece _ := ⊥
  smul_mem _ _ _ m _ hm := by
    rw [Submodule.mem_bot] at hm ⊢
    rw [hm, smul_zero]
  fg := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun _ => bot_le⟩

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

def twLocPart (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (I : Finset (Fin (N + 1))) :
    Submodule S Ω :=
  Submodule.span S {y | ∃ (z : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I ∧ s.IsHomogeneous e ∧
    z ∈ twPart η M₀ a b ∧ a - e = c ∧ y = (aeval x s)⁻¹ * z}

theorem twLocPart_eta_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} {I : Finset (Fin (N + 1))}
    (j : Fin (r + 1)) {y : Ω} (hy : y ∈ twLocPart η M₀ b c I) : η j * y ∈ twLocPart η M₀ (b + 1) c I := by
  refine Submodule.span_induction (p := fun y _ => η j * y ∈ twLocPart η M₀ (b + 1) c I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨η j * z, s, a, e, hs, hse, twPart_eta_mul η M₀ j hz, hae, ?_⟩
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

theorem twLocPart_chart_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} (K : Chart x)
    (a : chartRing S x K) {y : Ω} (hy : y ∈ twLocPart η M₀ b c K.1) : (a : Ω) * y ∈ twLocPart η M₀ b c K.1 := by
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  rw [ha]
  refine Submodule.span_induction (p := fun y _ => aeval x f / aeval x s * y ∈ twLocPart η M₀ b c K.1)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₁, a₁, e₁, hs₁, hse₁, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨aeval x f * z, s * s₁, a₁ + e, e + e₁, mul_mem hs hs₁, hse.mul hse₁,
      twPart_form_mul η M₀ hf hz, by push_cast; omega, ?_⟩
    rw [map_mul, mul_inv, div_eq_mul_inv]
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

def twLocPartA (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (K : Chart x) :
    Submodule (chartRing S x K) Ω where
  carrier := twLocPart η M₀ b c K.1
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' a y hy := by rw [chartRing_smul_def]; exact twLocPart_chart_mul η M₀ K a hy

theorem mul_mem_of_mem_span {K : Chart x} (T : Submodule (chartRing S x K) Ω) {s t : Set Ω} (w : Ω)
    (h : ∀ u ∈ s, ∀ v ∈ t, w * (u * v) ∈ T) {u v : Ω} (hu : u ∈ Submodule.span (chartRing S x K) s)
    (hv : v ∈ Submodule.span (chartRing S x K) t) : w * (u * v) ∈ T := by
  induction hu using Submodule.span_induction generalizing v with
  | mem u hu =>
    induction hv using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => rw [mul_zero, mul_zero]; exact T.zero_mem
    | add v v' _ _ h₁ h₂ => rw [mul_add, mul_add]; exact T.add_mem h₁ h₂
    | smul a v _ h₁ =>
      have : w * (u * (a • v)) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem a h₁
  | zero => rw [zero_mul, mul_zero]; exact T.zero_mem
  | add u u' _ _ h₁ h₂ => rw [add_mul, mul_add]; exact T.add_mem (h₁ hv) (h₂ hv)
  | smul a u _ h₁ =>
    have : w * ((a • u) * v) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]; exact T.smul_mem a (h₁ hv)

variable {G B : SubSystem S x Ω}

theorem pow_sub_le_span (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) : (B.pow n).sub K ≤ Submodule.span (chartRing S x K) (Set.range η ^ n) := by
  induction n with
  | zero =>
    change twistMod S x 0 K ≤ _
    rw [twistMod, Submodule.span_le]
    rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have he : e' = e := by omega
    subst he
    have hmem : aeval x f / aeval x s ∈ chartRing S x K := ⟨f, s, e', hs, hf, hse, rfl⟩
    have h1 : (1 : Ω) ∈ Submodule.span (chartRing S x K) (Set.range η ^ 0) :=
      Submodule.subset_span (by rw [pow_zero]; exact Set.mem_one.mpr rfl)
    have := Submodule.smul_mem _ (⟨_, hmem⟩ : chartRing S x K) h1
    rwa [chartRing_smul_def, mul_one] at this
  | succ n ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hB K] at hq
    have := mul_mem_of_mem_span (Submodule.span (chartRing S x K) (Set.range η ^ (n + 1))) 1
      (s := Set.range η) (t := Set.range η ^ n)
      (fun u hu v hv => by
        rw [one_mul, pow_succ']
        exact Submodule.subset_span (Set.mul_mem_mul hu hv)) hq (ih hy)
    rwa [one_mul, ← smul_eq_mul] at this

theorem range_pow_subset (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) {q : Ω} (hq : q ∈ Set.range η ^ n) : q ∈ (B.pow n).sub K := by
  induction n generalizing q with
  | zero =>
    rw [pow_zero, Set.mem_one] at hq
    subst hq
    exact one_mem_twistMod_zero (S := S) K
  | succ n ih =>
    rw [pow_succ', Set.mem_mul] at hq
    obtain ⟨u, hu, v, hv, rfl⟩ := hq
    have hu' : u ∈ B.sub K := by rw [← hB K]; exact Submodule.subset_span hu
    exact Submodule.subset_span ⟨u, hu', v, ih hv, smul_eq_mul _ _⟩

variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem twistSub_le_twLocPart (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    y ∈ twLocPart η M₀ n c K.1 := by
  change y ∈ twLocPartA η M₀ n c K
  revert y
  change Submodule.span _ _ ≤ twLocPartA η M₀ n c K
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, y', hy', rfl⟩
  rw [smul_eq_mul, ← one_mul (t * y')]
  refine mul_mem_of_mem_span _ 1 ?_ ht hy'
  rintro u ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ v ⟨q, hq, g, hg, rfl⟩
  rw [one_mul, smul_eq_mul]
  rw [← hG K] at hg
  refine mul_mem_of_mem_span _ (aeval x f / aeval x s) ?_ (pow_sub_le_span η hB K n hq) hg
  rintro q' hq' _ ⟨m, s₁, a, e₁, hs₁, hse₁, hm, hae, rfl⟩
  refine Submodule.subset_span ⟨(aeval x f * m) * q', s * s₁, a + e', e + e₁, mul_mem hs hs₁,
    hse.mul hse₁, ?_, by push_cast; omega, ?_⟩
  · rw [twPart_of_nonneg]
    exact Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem e' a f m hf hm) hq')
  · rw [smul_eq_mul, map_mul, mul_inv, div_eq_mul_inv]
    ring

theorem twLocPart_le_twistSub (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ twLocPart η M₀ n c K.1) :
    y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K := by
  obtain ⟨i, hi⟩ := K.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (K.2.2 hi)
  set T := ((G.twist (B.pow n)).twist (twistSys S x c)).sub K with hT
  refine Submodule.span_induction (p := fun y _ => y ∈ T) ?_ (T.zero_mem) (fun _ _ _ _ h₁ h₂ => T.add_mem h₁ h₂)
    (fun r' y _ h => Submodule.smul_of_tower_mem T r' h) hy
  rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos K hs
  rw [twPart_of_nonneg] at hz
  refine Submodule.span_induction (p := fun z _ => (aeval x s)⁻¹ * z ∈ T) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, hm, q, hq, rfl⟩
    have hq' := range_pow_subset η hB K n hq
    have hxc : x i ^ c ∈ twistMod S x c K := by
      rw [twistMod_eq_span c K hi]; exact Submodule.mem_span_singleton_self _
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have hg : (aeval x (s * X i ^ k))⁻¹ • m ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨m, s * X i ^ k, a, e + k, mul_mem hs (pow_mem (X_mem_monos hi) k),
          hse.mul (isHomogeneous_X_pow i k), hm, by push_cast; omega, rfl⟩
      have hmem : x i ^ (k : ℤ) • (q • ((aeval x (s * X i ^ k))⁻¹ • m)) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast]
      field_simp
    · have hg : (aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨aeval x (X i ^ k : Poly S N) • m, s, a + k, e, hs, hse,
          M₀.smul_mem k a (X i ^ k : Poly S N) m (isHomogeneous_X_pow i k) hm, by omega, rfl⟩
      have hmem : x i ^ (-(k : ℤ)) • (q • ((aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m))) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast]
      field_simp
  · rw [mul_zero]; exact T.zero_mem
  · intro u v _ _ hu hv; rw [mul_add]; exact T.add_mem hu hv
  · intro r' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_of_tower_mem T r' hu

end Chart

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section Aug

variable (S : Type u) [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {n : ℕ}

def Cech.AugExact {y : Fin (n + 1) → Ω} (G : Chart y → Submodule S E) (B : Submodule S E) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ b ∈ B, (∀ _ : Cech.Idx (support y) 0, b = 0) → b = 0) ∧
  (∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G 0,
      Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G (p + 1),
    Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) (p + 1) s = 0 →
      ∃ t ∈ Cech.Cdeg (fun _ : Chart y => E) G p,
        Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) p t = s

end Aug

section Z

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E] {r : ℕ}

def secsOnZChart (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (I : Chart x)
    (J : Chart h) : Submodule S E :=
  Submodule.span S {e | ∃ n : ℕ, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I}

def secsOnZ (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (J : Chart h) : Submodule S E :=
  ⨅ I : Chart x, secsOnZChart G H h I J

end Z

end

end GroundTheory.Heights₂.Heights.Kleiman
end

