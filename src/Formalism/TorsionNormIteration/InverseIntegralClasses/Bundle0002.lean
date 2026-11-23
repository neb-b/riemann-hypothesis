module

public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Formalism.FormalGroupLog.LogDeterminesLaw
public import Formalism.FormalGroupLog.Statement
public import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
public import Formalism.TorsionNormIteration.InverseIntegralClasses.Bundle0001

@[expose] public section

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.IsHomOfSubstEqSmul
section
noncomputable section

open PowerSeries

namespace Formalism.LT.PadicP

open Formalism.G

section LtLog

variable {p : ℕ} [hp : Fact p.Prime]


end LtLog

theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
    · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

end Formalism.LT.PadicP

namespace Formalism.LT

end Formalism.LT
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.LTLemma
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.LTL

open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP

section Near

variable {K : Type u} [NormedField K] {ι : Type*}

def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)

end Near

section Master

variable {K : Type u} [NormedField K] {ι : Type*}

end Master

section Cong

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)

end Cong

section FrobPi

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

end FrobPi

section Defect

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

end Defect

section Constr

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

end Constr

end Formalism.LT.LTL

namespace Formalism.LT

open Formalism.G Formalism.LT.LTL

end Formalism.LT
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.MapSubtypeInjective
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.Asm

open Formalism.G

section Integral

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_add {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a + b) := by
  intro d
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) (hb d))

theorem integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem integralMv_X {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem funEqMv_add {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a + b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_add ha hb using 1
  simp only [map_add (f := _), smul_add]
  abel

theorem funEqMv_sub {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a - b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_sub ha hb using 1
  simp only [map_sub, smul_sub]
  abel

end Integral

theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero

theorem two_le_q {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  obtain ⟨hp, ⟨k, hk, rfl⟩, -⟩ := h
  exact hp.two_le.trans (Nat.le_self_pow (by omega) _)

theorem funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ (f.subst h)) : IntegralMv h :=
  h2 K ι (IsFunEqTypeMv p q (q_ne_zero hS) σ) f hf0 hf1
    (fun _ _ ha hb => funEqMv_sub _ _ ha hb)
    (fun P hP0 hPI => hk K p q (q_ne_zero hS) σ hS f hf0 hfE ι P hP0 hPI)
    (fun D hD N hN hlow d hd => h3 K ι p q (q_ne_zero hS) σ (two_le_q hS) D hD N hN hlow d hd)
    h hh0 hC

theorem FunEqGroup_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  have hq := q_ne_zero hS
  have hG0 : MvPowerSeries.constantCoeff (atX f + atY f) = 0 := by
    rw [map_add (f := _), atX, atY, PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0, add_zero]
  have hGE : IsFunEqTypeMv p q hq σ (atX f + atY f) :=
    funEqMv_add hq σ (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 0))
      (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 1))
  obtain ⟨F, hF0, hF⟩ := h1 K (Fin 2) f (atX f + atY f) hf0 hf1 hG0
  refine ⟨F, hF0, funEqInv h2 h3 hk hS hf0 hf1 hfE F hF0 ?_, hF⟩
  rw [hF]
  exact hGE

theorem funEqType_unit {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg (d ())
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rw [hd]
  exact this

theorem FunEqHom_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI : IntegralMv h := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 (by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE)
  exact ⟨h, hh0, fun n => hI _, hh⟩

section FG

open Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

end FG

end Formalism.LT.Asm

namespace Formalism.LT

theorem FunEqGroup_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} :=
  Formalism.LT.Asm.FunEqGroup_of' h1 h2 h3 hk

theorem FunEqHom_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk

end Formalism.LT
end
end

