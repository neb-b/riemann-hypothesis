module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyConst
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def e1 (D : D7) : ℕ := (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) / 3

def rdExp (D : D7) : ℕ := 2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) + e1 D

def Anum (D : D7) : ℝ := D.host.rdE ^ rdExp D * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Kexp (P : Parts X u u') : ℝ := Anum D / P.Gam0


variable (X u u') in
def LemmaMS (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p =
    D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) *
      (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ

theorem anum_pow : Anum D ^ D.R.f =
    Formalism.L2.SG.MassDataConc.kapN D * (D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3)))) := by
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) =
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) *
        ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f) := by
    rw [← pow_add]
    congr 1
    ring
  rw [key]
  simp only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

theorem rdE_pos' : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (by exact_mod_cast h)

theorem energy_constant_nonneg (P : Parts X u u') : 0 ≤ P.Gam0 := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev
  apply Finset.prod_nonneg
  intro l _
  apply div_nonneg
  · apply zpow_nonneg
    unfold Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd
    positivity
  · unfold Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd
    positivity

theorem constPin_of (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : LemmaMS X u u' ψ)
    (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f) :
    ConstPin P ψ (fun _ => Kexp P) := by
  obtain ⟨-, -, -, -, -, -, hZZ, hPP, -⟩ := hC
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hrd : 0 < D.host.rdE := rdE_pos'
  have hA : 0 ≤ Anum D := by
    unfold Anum
    exact mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hK0 : 0 ≤ Kexp P := div_nonneg hA (energy_constant_nonneg P)
  refine ⟨fun _ => hK0, ?_⟩
  have hfS : P.S.f = D.R.f := by
    rw [← hf, ← Fintype.card_fin P.S.f]
    exact Fintype.card_congr P.τ
  have hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f := by
    rw [Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]
  have hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ := hZZ
  have hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos (fun l _ => (hPP l).2)
  have hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
    unfold Formalism.L2.SG.MassDataConc.kapN
    exact mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))
  have hM : D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)
  rw [hprod, anum_pow, hMS, hfS]
  field_simp

end Formalism.L2.SG.Pf.Carrier.EnergyConst
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gram

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem inner_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c d : α →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f c, Finsupp.linearCombination ℂ f d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ g c, Finsupp.linearCombination ℂ g d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

theorem norm_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c : α →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  have hsq : ‖Finsupp.linearCombination ℂ f c‖ ^ 2 = ‖Finsupp.linearCombination ℂ g c‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_lc f g h c c]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem exists_linearIsometryEquiv_of_inner_eq (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ a, U (f a) = g a := by
  classical
  set F := Finsupp.linearCombination ℂ f with hF
  set G := Finsupp.linearCombination ℂ g with hG
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := norm_lc f g h c
    rw [← hF, ← hG, hc, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  let φ : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hφ c]
    show ‖G c‖ = ‖F c‖
    exact (norm_lc f g h c).symm
  let L : LinearMap.range F →ₗᵢ[ℂ] V := { φ with norm_map' := hφn }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hfa : f a ∈ LinearMap.range F := ⟨Finsupp.single a 1, by simp [hF]⟩
  have e1 : (L.extend.toLinearIsometryEquiv rfl) (f a) = L.extend (f a) := rfl
  rw [e1, show f a = ((⟨f a, hfa⟩ : LinearMap.range F) : V) from rfl, LinearIsometry.extend_apply]
  have e2 : (⟨f a, hfa⟩ : LinearMap.range F) =
      ⟨F (Finsupp.single a 1), LinearMap.mem_range_self F _⟩ := by
    ext; simp [hF]
  rw [e2]
  show φ _ = g a
  rw [hφ]
  simp [hG]

end Gram

section Loc

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem wu_ne (u : D.what₂.Word) : ∃ x0, X.Wu u x0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 := (X.Wu_spec u).2.2.2.2
  simp [hc] at h1

open Classical in
theorem inner_upd (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (x0 : X.B.I.Ginf)
    (y y' : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ =
      ⟪X.Wloc u v y, X.Wloc u v y'⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ := by
  rw [X.Wu_tens, X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]


open Classical in
theorem wloc_gram (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wloc u v (s * a), X.Wloc u v (s * b)⟫_ℂ = ⟪X.Wloc u v a, X.Wloc u v b⟫_ℂ := by
  obtain ⟨x0, hx0⟩ := wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      simpa [S] using hs
    · simp only [S, Function.update_of_ne hw, Pi.one_apply]
      refine ⟨fun a => ?_, ?_⟩ <;> simp [uMat]
  have hmul : ∀ y, S * Function.update x0 v y = Function.update x0 v (s * y) := by
    intro y
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : ∀ x, X.Wu u (S * x) = X.psiInfU u S • X.piU u S (X.Wu u x) := fun x => (X.Wu_spec u).1 S hS x
  have hU : ∀ x y, ⟪X.piU u S x, X.piU u S y⟫_ℂ = ⟪x, y⟫_ℂ := (X.piU_rep u).2.2.1 S hS
  have hψ : conj (X.psiInfU u S) * X.psiInfU u S = 1 := by
    rw [Complex.conj_mul', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u S]
    simp
  have key : ∀ y y', ⟪X.Wu u (S * Function.update x0 v y), X.Wu u (S * Function.update x0 v y')⟫_ℂ =
      ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ := by
    intro y y'
    rw [hW, hW, inner_smul_left, inner_smul_right, hU, ← mul_assoc, hψ, one_mul]
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have h2 := key a b
  rw [hmul, hmul, inner_upd, inner_upd] at h2
  exact mul_right_cancel₀ hK h2

theorem wloc_unit (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) :
    ∃ A : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u v, ∀ x, X.Wloc u v (s * x) = (1 : ℂ) • A (X.Wloc u v x) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_inner_eq (fun x => X.Wloc u v x) (fun x => X.Wloc u v (s * x))
    (fun a b => (wloc_gram X u v s hs a b).symm)
  exact ⟨A, fun x => by rw [one_smul, hA x]⟩

theorem hilbertSchmidt_sq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ hs2 A := by
  unfold Formalism.L2.SG.RealObj.hs2
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hilbertSchmidt_double_coset_invariant (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g s s' : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s))
    (hs' : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s')) :
    hs2 (JvX X u u' v (s * g * s'⁻¹)) = hs2 (JvX X u u' v g) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := FiniteDimensional.complete ℂ (X.Vloc u' v)
  obtain ⟨A, hA⟩ := wloc_unit X u v s hs
  obtain ⟨B, hB⟩ := wloc_unit X u' v s' hs'
  unfold JvX Formalism.L2.SG.RealObj.Jv
  rw [Formalism.L2.SG.RealObj.InfCut.OO_equiv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g s s' 1 1 A B hA hB,
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_left _ _ (fun x => A.norm_map x),
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right]
  simp

theorem jvX_meas (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Measurable (fun g => hs2 (JvX X u u' v g)) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  have hF : Continuous (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v p.2) (X.Wloc u' v (p.1⁻¹ * p.2))) :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator ((X.Wloc_cont u v).comp continuous_snd)
      ((X.Wloc_cont u' v).comp ((continuous_fst.inv).mul continuous_snd))
  have hJ : StronglyMeasurable (fun g => JvX X u u' v g) := by
    have := hF.stronglyMeasurable.integral_prod_right' (ν := Formalism.REAL.muG (X.B.I.ε v))
    unfold JvX Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    simpa [Measure.restrict_univ] using this
  have hc : Continuous (fun A : X.Vloc u' v →L[ℂ] X.Vloc u v => hs2 A) := by
    unfold hs2
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℂ (X.Vloc u v) (stdOrthonormalBasis ℂ (X.Vloc u' v) i)).continuous.norm.pow 2)
  exact hc.measurable.comp hJ.measurable

end Loc

def StepSecX : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ h : (Fin (D.R.rS + 1) → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Measurable h ∧
      ∀ cv ∈ GoodV (D := D) u u', Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (h cv)) = Matrix.diagonal cv

theorem locRep_of_sec (hS : StepSecX) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L := by
  classical
  choose h hm hsec using hS D X u u'
  refine ⟨fun v cv => hs2 (JvX X u u' v (h v cv)),
    ⟨fun v => ⟨(jvX_meas X u u' v).comp (hm v), fun cv => hilbertSchmidt_sq_nonneg _⟩, ?_⟩⟩
  intro c hc v
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hsec w (c w) (hc w)⟩
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u')
    (c v) (hc v).1 (hc v).2 (h v (c v)) ((hOf X u u' 1 c) v) (hsec v (c v) (hc v)) (hh v)
  show hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = hs2 (JvX X u u' v (h v (c v)))
  rw [heq]
  exact hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem dcrel_of_heq {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (h : Λ₁ = Λ₂) {T T' : E} (F : LFlag S r T)
    (P : Submodule (𝓞 E) S.V → LFlag S r T' → Prop) (x : TermDef.Carrier (P Λ₁)) (y : TermDef.Carrier (P Λ₂))
    (he : HEq (TermDef.mk Λ₁ F (P Λ₁) x) (TermDef.mk Λ₂ F (P Λ₂) y)) : TermDef.DCRel Λ₂ F x.1 y.1 := by
  subst h
  have h2 : Quot.mk _ x = Quot.mk _ y := eq_of_heq he
  have h3 := Quot.eqvGen_exact h2
  clear he h2
  induction h3 with
  | rel a b hab => exact hab
  | refl a => apply Formalism.L2.SG.TermDef.dcrel_refl
  | symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)
  | trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)

theorem nlam_isom {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := hn.1.1

theorem nlam_gmap {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2

theorem gmap_inv_of {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (h : Formalism.HermitianLatticesTheory.gmap g Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ = Λ := by
  have hinv : ∀ y : S.V, g⁻¹ (g y) = y := fun y => g.symm_apply_apply y
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by rw [h]; exact hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    rw [hinv]
    exact hz
  · intro hx
    refine ⟨g x, ?_, hinv x⟩
    rw [← h]
    exact Submodule.mem_map_of_mem hx

end Gen

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem frame_lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a = F0.fvec a := rfl

theorem lin_isom (s : Formalism.L2.SG.PackageTie2.TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem lin_gmap (s : Formalism.L2.SG.PackageTie2.TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

theorem frame_eq (s : Formalism.L2.SG.PackageTie2.TT Y u u') : s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_isom s)]
  rfl

theorem frame_apply (s : Formalism.L2.SG.PackageTie2.TT Y u u') (a : Fin (D.R.rS + 1)) : frame s.frame a = s.lin ((X.Fu u').fvec a) := by
  rw [frame_eq]
  show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a =
    s.lin ((lf D (X.Fu u')).fl.fvec a)
  generalize (lf D (X.Fu u')).fl = F
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]

theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : c ∈ stabF D F0 := by
  have he : ∀ i, c (F0.e i) = F0.e i := fun i => by
    have h1 := hfix i.castSucc
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  refine ⟨hc, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, he]
  · have h1 := hfix (Fin.last _)
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using h1

theorem fib_dec {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s.lam' (lf D (X.Fu u')),
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
        s'.lin = n * s.lin * ν * c := by

  have hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x :=
    fun f x => f.symm_apply_apply x
  have hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x :=
    fun f x => f.apply_symm_apply x
  have gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L) := by
    intro f g L
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
    intro L
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id L

  have h' := h
  unfold Formalism.L2.SG.TermOp.GTerm.toTerm at h'
  injection h' with h1 h3
  have hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame :=
    dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u')
      ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hd
  have hnL : n ∈ NLam s.lam (lf D (X.Fu u)) := by rw [h1]; exact hn

  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u'))) := by
    rw [lin_gmap, h1, ← frame_eq]
    exact hm
  have hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'
  have hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
    rw [← lin_gmap s, ← gmul, inv_mul_cancel, gone]
  generalize hνdef : s.lin⁻¹ * m * s.lin = ν at hν
  refine ⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin,
    ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')
  · rw [gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL),
      hback, gmap_inv_of (nlam_gmap hν)]
  · intro a
    have e1 := hfr a
    rw [frame_apply, frame_apply] at e1
    rw [hmul, e1]
    have e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a) := by
      rw [← hνdef]
      simp only [hmul, hinv']
    rw [e2, hinv]

theorem lam'_eq {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) : s.lam' = s'.lam' := by
  obtain ⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩ := fib_dec h
  have hstab : c ∈ stabF D (X.Fu u') := stabF_of_fix (X.Fu u') hc hfix
  have hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u') :=
    stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)
  have hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam' := by
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id _
  have hR := Y.rowsOK u'
  obtain ⟨Λ0, -, huniq⟩ := hR.2 s.lam' (hR.1 _ s.mem')
  have e1 := huniq s.lam' ⟨s.mem', 1, hone, hg1⟩
  have e2 := huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩
  exact e1.trans e2.symm

theorem gterm_eq {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    (h : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') : s = s' := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  rcases s with ⟨l, hm, l', hm', c⟩
  rcases s' with ⟨k, km, k', km', c'⟩
  simp only at hl hl'
  subst hl
  subst hl'
  have hc : c = c' :=
    (Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))
  subst hc
  rfl

end Fib

end Formalism.L2.SG.Pf.FibreCounting
end
end

