module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DefFinWOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DefFinW : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (P : Submodule ℤ (VS D).V), P.FG → ∀ c : D.host.E,
    {w : (VS D).V | w ∈ P ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = c}.Finite

def WPos : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (w : (VS D).V), (∀ a, (VS D).hT (D.sp.hypE a) w = 0) →
    (∀ a, (VS D).hT (D.sp.hypF a) w = 0) → (VS D).hT D.sp.zm w = 0 → w ≠ 0 →
      0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

theorem defFinW_of (hW : WPos) : DefFinW := by
  intro D P hP c
  classical
  letI : Module ℚ (VS D).V := Module.compHom (VS D).V (algebraMap ℚ D.host.E)
  have hsm : ∀ (q : ℚ) (v : (VS D).V), q • v = (algebraMap ℚ D.host.E q) • v := fun _ _ => rfl
  have hsmL : ∀ (q : ℚ) (v w : (VS D).V), (VS D).hT (q • v) w = (q : D.host.E) * (VS D).hT v w := by
    intro q v w
    rw [hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, eq_ratCast, map_ratCast]
  have hsmR : ∀ (q : ℚ) (v w : (VS D).V), (VS D).hT v (q • w) = (q : D.host.E) * (VS D).hT v w := by
    intro q v w
    rw [hsm, map_smul, smul_eq_mul, eq_ratCast]
  have htr : ∀ (q : ℚ) (y : D.host.E), Algebra.trace ℚ D.host.E ((q : D.host.E) * y) = q * Algebra.trace ℚ D.host.E y := by
    intro q y
    rw [show (q : D.host.E) * y = q • y by rw [Algebra.smul_def, eq_ratCast], map_smul, smul_eq_mul]
  let Wq : Submodule ℚ (VS D).V :=
    { carrier := {w | (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
        (VS D).hT D.sp.zm w = 0}
      add_mem' := by
        rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
        exact ⟨fun a => by rw [map_add (f := _), hx1, hy1, add_zero],
          fun a => by rw [map_add (f := _), hx2, hy2, add_zero], by rw [map_add (f := _), hx3, hy3, add_zero]⟩
      zero_mem' := ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩
      smul_mem' := by
        rintro q x ⟨hx1, hx2, hx3⟩
        exact ⟨fun a => by rw [hsmR, hx1, mul_zero], fun a => by rw [hsmR, hx2, mul_zero],
          by rw [hsmR, hx3, mul_zero]⟩ }
  let A0 : Submodule ℤ (VS D).V := P ⊓ Wq.restrictScalars ℤ
  have hA0 : A0.FG := by
    haveI := isNoetherian_of_fg_of_noetherian P hP
    have hfg : (A0.comap P.subtype).FG := IsNoetherian.noetherian _
    have := hfg.map P.subtype
    rwa [Submodule.map_comap_subtype, inf_of_le_right (inf_le_left : A0 ≤ P)] at this
  obtain ⟨s, hs⟩ := hA0
  let U : Submodule ℚ (VS D).V := Submodule.span ℚ (s : Set (VS D).V)
  haveI : FiniteDimensional ℚ U := FiniteDimensional.span_finset ℚ s
  have hA0U : ∀ w ∈ A0, w ∈ U := fun w hw => by
    rw [← hs] at hw
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hw
  have hUle : U ≤ Wq := by
    refine Submodule.span_le.mpr fun x hx => ?_
    have hx' : x ∈ A0 := by
      rw [← hs]
      exact Submodule.subset_span hx
    exact (Submodule.mem_inf.mp hx').2
  let B : LinearMap.BilinForm ℚ U := LinearMap.mk₂ ℚ
    (fun u v : U => (Algebra.trace ℚ D.host.E ((VS D).hT u v) + Algebra.trace ℚ D.host.E ((VS D).hT v u)) / 2)
    (fun m1 m2 n => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; ring)
    (fun q m n => by simp only [Submodule.coe_smul, hsmL, hsmR, htr, smul_eq_mul]; ring)
    (fun m n1 n2 => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; ring)
    (fun q m n => by simp only [Submodule.coe_smul, hsmL, hsmR, htr, smul_eq_mul]; ring)
  have hS : ∀ x y, B x y = B y x := fun x y => by
    simp only [B, LinearMap.mk₂_apply]
    ring
  have hpos : ∀ v, v ≠ 0 → 0 < B v v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hUle v.2
    have := hW D v h1 h2 h3 (fun h => hv (Subtype.ext h))
    simp only [B, LinearMap.mk₂_apply]
    linarith
  let A : Submodule ℤ U := A0.comap (U.subtype.restrictScalars ℤ)
  have hA : A.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars ℤ)
      Subtype.val_injective ?_
    rw [Submodule.map_comap_eq_self (fun w hw => ⟨⟨w, hA0U w hw⟩, rfl⟩)]
    exact ⟨s, hs⟩
  have hfin := finite_le_of_posDef B hS hpos A hA (Algebra.trace ℚ D.host.E c)
  refine (hfin.image U.subtype).subset ?_
  rintro w ⟨hwP, h1, h2, h3, hc⟩
  have hwA0 : w ∈ A0 := Submodule.mem_inf.mpr ⟨hwP, ⟨h1, h2, h3⟩⟩
  refine ⟨⟨w, hA0U w hwA0⟩, ⟨hwA0, ?_⟩, rfl⟩
  simp only [B, LinearMap.mk₂_apply, Subtype.coe_mk, hc]
  linarith

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensMultOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PrimeZeta2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Summable (fun p : HeightOneSpectrum (𝓞 K) => 1 / ((p.asIdeal.absNorm : ℝ) ^ 2))

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnipotentIntegralIsGroup : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ ∧
    (∀ n ∈ N0 F0 Λ, n.symm ∈ N0 F0 Λ) ∧
    (∀ n ∈ N0 F0 Λ, ∀ m ∈ N0 F0 Λ, n.trans m ∈ N0 F0 Λ)

def OrbitReps : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂,
        ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
          ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K

end PI.UnitaryGroupMassFormula.CntFormula
end
end

