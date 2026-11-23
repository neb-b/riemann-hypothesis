module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0041

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIotaA
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Proj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_zero (e : Fin r → S.V) (v : S.V) (h : ∀ b, S.hT (e b) v = 0) :
    ∀ x ∈ Submodule.span E (Set.range e), S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem proj_exists (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {T' : E} (F' : LFlag S r T') :
    ∃ u : Fin r → S.V, ∀ l ∈ Λ, l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ Lrep Λ F' := by
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')
  have li := F'.fl.e_indep
  have hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e) := fun y => hρX y

  let co : Fin r → Λ →ₗ[𝓞 E] E := fun a =>
    { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a
      map_add' := fun y y' => by
        have e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) =
            ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩ :=
          Subtype.ext (by simp only [map_add (f := _), Submodule.coe_add])
        rw [e, map_add (f := _), Finsupp.add_apply]
      map_smul' := fun c y => by
        have e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) =
            (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩ :=
          Subtype.ext (by
            show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)
            rw [LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])
        rw [e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  have hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a := fun _ _ => rfl
  have hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a := by
    intro y
    have h := li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)] at h
    rw [← h]
    rfl
  have hR := fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)
  choose u hu using hR

  have hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0 := by
    intro a b
    obtain ⟨d, hd0, hdΛ⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    have hdX : d • F'.fl.e b ∈ Xsp F' := by
      rw [← algebraMap_smul E d]
      exact (Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩ := hρid _ hdX
    have hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0) := by
      rw [hco]
      have e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) =
          ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩ :=
        Subtype.ext (by
          show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b
          rw [hρd]
          exact (algebraMap_smul E d _).symm)
      rw [e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
    have h1 := hu a (d • F'.fl.e b) hdΛ
    rw [hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul] at h1
    have h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0 := mul_left_cancel₀ hdE h1
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  refine ⟨u, fun l hl => ⟨?_, ?_⟩⟩
  ·
    refine Λ.sub_mem hl ?_
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]
    rw [hval]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl
    rw [← ho, Submodule.mem_one]
    exact ⟨o, rfl⟩
  ·
    show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
    refine hT_span_zero F'.fl.e _ fun b => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]

end Proj

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_beta {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) :
    ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
  intro w hw
  have hg : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨l, hl, hlw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw
  have h2 := (hP.2.2.2 w hw l hl).1 hlw
  have hle : ∀ F₁ : LFlag (D.sp.Y 0) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ →
      NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
    intro F₁ ha hc
    unfold NgX
    exact sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)
  have e : β w - w = (l - w) - (l - β w) := by abel
  rw [e]
  exact Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)

end D7

end Formalism.L2.SG.Pf.ScalarFrameIota
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviSteps
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviStabFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    ∃ T : Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      (∀ τ ∈ T, τ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap τ Λ = Λ ∧ ∃ t : X.B.I.GA, RatLink X t τ ∧ t ∈ Srat X u') ∧
      ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ = Λ →
        ∃ τ ∈ T, ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), (τ⁻¹ * σ) x - x ∈ Xsp (lf D (X.Fu u'))

def Usp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u'})

def Wsp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  orth (VS D) (Usp X u')

def LeviPosC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word), ∀ w ∈ Wsp X u', w ≠ 0 →
    0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

def SratZC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → s ∈ Srat X u' →
      σ (X.zu u') - X.zu u' ∈ Xsp (lf D (X.Fu u'))

def piWL {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) - ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a) -
    ((VS D).hT (X.zu u')).smulRight (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u')

def hW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    Wsp X u' →ₗ⋆[D.host.E] Wsp X u' →ₗ[D.host.E] D.host.E :=
  ((VS D).hT.comp (Wsp X u').subtype).compl₂ (Wsp X u').subtype

def LW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Submodule (𝓞 D.host.E) (Wsp X u') :=
  ((Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
    ((piWL X u').restrictScalars (𝓞 D.host.E))).comap ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E))

def LeviWFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    Set.Finite {g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' | g ∈ Formalism.HermitianLatticesTheory.isom (hW X u') ∧ Formalism.HermitianLatticesTheory.gmap g (LW X u' Λ) = LW X u' Λ}

theorem srat_flag {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {u' : D.what₂.Word} {s : X.B.I.GA}
    {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : RatLink X s σ) (hS : s ∈ Srat X u') :
    ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j := by
  have hX : ∀ j : ℕ, Xflag (lf D (X.Fu u')) j = Submodule.span D.host.E (X.eX '' {b | b.1 < j}) := by
    intro j
    unfold Formalism.MainNotions.S.Lat.Xflag Formalism.MainNotions.S.FlagG.Xa
    simp only [Formalism.MainNotions.S.lf, X.Fu_e]
  intro j x hx
  rw [hX (j + 1)] at hx
  rw [hX j]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have h := Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.flag_e (X := X) hs hS b
    refine Submodule.span_mono ?_ h
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_of_lt_of_le hc (Nat.lt_succ_iff.mp hb), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), add_sub_add_comm]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hy

private theorem gmap_mul_lemma {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

private theorem gmap_one_explicit_D {D : D7} (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.coe_one, id_eq, exists_eq_right]

private theorem gmap_inv_of_gmap_eq {D : D7} (a : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L M : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap a L = M) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ M = L := by
  rw [← h, ← gmap_mul_lemma, inv_mul_cancel, gmap_one_explicit_D]

theorem leviFinC_of (h : LeviStabFinC) : LeviFinC := by
  intro D X Y u'
  let P : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V → Prop := fun Λ₁ Λ₂ =>
    Λ₂ ∈ Y.what₂ u' ∧ ∃ (σ₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s₀ : X.B.I.GA), RatLink X s₀ σ₀ ∧
      σ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ s₀ ∈ Srat X u' ∧ Formalism.HermitianLatticesTheory.gmap σ₀ Λ₂ = Λ₁
  refine ⟨fun Λ₁ Λ₂ => if hP : P Λ₁ Λ₂ then
      (h D X Y u' Λ₂ hP.1).choose.image (fun τ => hP.2.choose * τ) else ∅, ?_⟩
  intro Λ₁ _ Λ₂ hΛ₂ σ s hs hσ hS hmap
  have hP : P Λ₁ Λ₂ := ⟨hΛ₂, σ, s, hs, hσ, hS, hmap⟩
  simp only [dif_pos hP]
  obtain ⟨s₀, hs₀, hσ₀, hS₀, hmap₀⟩ := hP.2.choose_spec
  obtain ⟨hT1, hT2⟩ := (h D X Y u' Λ₂ hP.1).choose_spec
  generalize hP.2.choose = σ₀ at hs₀ hσ₀ hmap₀ ⊢
  generalize (h D X Y u' Λ₂ hP.1).choose = T at hT1 hT2 ⊢

  have hρL : RatLink X (s₀⁻¹ * s) (σ₀⁻¹ * σ) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hs₀) hs
  have hρI : σ₀⁻¹ * σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hσ₀) hσ
  have hρS : s₀⁻¹ * s ∈ Srat X u' := (Srat X u').mul_mem ((Srat X u').inv_mem hS₀) hS
  have hρΛ : Formalism.HermitianLatticesTheory.gmap (σ₀⁻¹ * σ) Λ₂ = Λ₂ := by
    rw [gmap_mul_lemma, hmap]
    exact gmap_inv_of_gmap_eq σ₀ Λ₂ Λ₁ hmap₀
  obtain ⟨τ, hτ, hτo⟩ := hT2 (σ₀⁻¹ * σ) (s₀⁻¹ * s) hρL hρI hρS hρΛ
  obtain ⟨hτI, hτΛ, t, ht, htS⟩ := hT1 τ hτ
  refine ⟨σ₀ * τ, Finset.mem_image.mpr ⟨τ, hτ, rfl⟩, ?_⟩
  have heq : (σ₀ * τ)⁻¹ * σ = τ⁻¹ * (σ₀⁻¹ * σ) := by
    rw [mul_inv_rev, mul_assoc]
  rw [heq]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hτI) hρI, ?_⟩, ?_, hτo⟩
  · rw [gmap_mul_lemma, hρΛ]
    exact gmap_inv_of_gmap_eq τ Λ₂ Λ₂ hτΛ
  · exact srat_flag X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X ht) hρL)
      ((Srat X u').mul_mem ((Srat X u').inv_mem htS) hρS)

end Formalism.L2.SG.Pf.SlabCount
end
end

