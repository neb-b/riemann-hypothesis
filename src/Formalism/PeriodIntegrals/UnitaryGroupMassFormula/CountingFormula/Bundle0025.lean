module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassOfSplit

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CoordsUnique
section
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Coords

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem pb_coords (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {v : V}
    (hv : v ∈ pbLat x 𝔞) : ∃ c : ι → K, (∀ i, c i ∈ 𝔞 i) ∧ v = ∑ i, c i • x i := by
  unfold pbLat at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, c, hc, rfl⟩ := hy
    refine ⟨Pi.single i c, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact hc
      · rw [Pi.single_eq_of_ne hj]
        exact (𝔞 j : Submodule (𝓞 K) K).zero_mem
    · symm
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  | zero => exact ⟨0, fun i => (𝔞 i : Submodule (𝓞 K) K).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    exact ⟨c + d, fun i => (𝔞 i : Submodule (𝓞 K) K).add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  | smul r y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨fun i => algebraMap (𝓞 K) K r * c i, fun i => ?_, ?_⟩
    · have hm := Submodule.smul_mem (𝔞 i : Submodule (𝓞 K) K) r (hc i)
      rwa [Algebra.smul_def] at hm
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, algebraMap_smul]

theorem coords_unique {x : ι → V} (hind : LinearIndependent K x) {c d : ι → K}
    (h : ∑ i, c i • x i = ∑ i, d i • x i) : c = d := by
  have h0 : ∑ i, (c - d) i • x i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hz := Fintype.linearIndependent_iff.mp hind (c - d) h0
  funext i
  exact sub_eq_zero.mp (hz i)

end Coords

theorem sStable_prod {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} (s : Finset ι)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (h : ∀ i, SStable (𝔞 i)) : SStable (∏ i ∈ s, 𝔞 i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact sStable_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact sStable_mul (h j) ih

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsSE
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Section

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def lpS (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  Λ ⊓ (perpS (VS D) F0.X).restrictScalars (𝓞 D.host.E)

variable {D F0}

theorem sE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (ρ : lpS D F0 Λ →ₗ[𝓞 D.host.E] lpS D F0 Λ)
    (hρid : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ F0.X → ρ y = y)
    {s : Type} [Fintype s] (c : Basis s D.host.E (WbQ D F0)) (a : s → perpS (VS D) F0.X)
    (hac : ∀ i, (Submodule.Quotient.mk (a i) : WbQ D F0) = c i)
    (y : s → lpS D F0 Λ) (hya : ∀ i, (y i : (VS D).V) = a i)
    (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X)
    (hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V))
    (b : perpS (VS D) F0.X) (yb : lpS D F0 Λ) (hyb : (yb : (VS D).V) = b)
    (d : 𝓞 D.host.E) (hd0 : d ≠ 0) (o : s → 𝓞 D.host.E)
    (ho : ∑ i, o i • c i = d • (Submodule.Quotient.mk b : WbQ D F0)) :
    (sE (Submodule.Quotient.mk b) : (VS D).V) = (b : (VS D).V) - (ρ yb : (VS D).V) := by
  have hsm : ∀ (r : 𝓞 D.host.E) (v : (VS D).V),
      r • v = (algebraMap (𝓞 D.host.E) D.host.E r) • v := fun r v => (algebraMap_smul D.host.E r v).symm
  have hq : (Submodule.Quotient.mk (∑ i, o i • a i - d • b) : WbQ D F0) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply, hac, ho, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
  rw [Submodule.mem_comap] at hmem
  have hzX : ((∑ i, o i • y i - d • yb : lpS D F0 Λ) : (VS D).V) ∈ F0.X := by
    convert hmem using 1
    simp [hya, hyb]
  have hρz := hρid _ hzX
  have e := congrArg (fun u : lpS D F0 Λ => (u : (VS D).V)) hρz
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, Submodule.coe_sub, Submodule.coe_sum,
    Submodule.coe_smul] at e
  have h1 : ∑ i, o i • (y i : (VS D).V) - ∑ i, o i • (ρ (y i) : (VS D).V) =
      d • (yb : (VS D).V) - d • (ρ yb : (VS D).V) := by
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact e.symm
  have h2 := congrArg (fun q => ((sE q : perpS (VS D) F0.X) : (VS D).V)) ho
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    hsEc] at h2
  have hd : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 := by
    intro h0
    apply hd0
    exact (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)
  apply smul_right_injective (VS D).V hd
  simp only
  rw [← hsm, ← hsm, ← h2]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [h1, hyb]

theorem exists_sE (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsFullLattice D.host.E Λ) :
    ∃ sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X,
      (∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a) ∧
      ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ := by
  classical
  have hlpfg : (lpS D F0 Λ).FG := Submodule.FG.of_le hL.fg inf_le_left
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract (lpS D F0 Λ) hlpfg F0.X
  have hlpP : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ perpS (VS D) F0.X := fun y => (Submodule.mem_inf.1 y.2).2
  have hlpΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ Λ := fun y => (Submodule.mem_inf.1 y.2).1
  have hPmem : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ perpS (VS D) F0.X :=
    fun y => Submodule.sub_mem _ (hlpP y) (hlpP (ρ y))
  have hPΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ Λ :=
    fun y => Submodule.sub_mem _ (hlpΛ y) (hlpΛ (ρ y))
  have hMlat := Mof_isLattice D F0 Λ hL.toIsLattice
  obtain ⟨s, _, c, hcv, hsM⟩ :=
    Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 D.host.E) (Mof D F0 Λ)
      (Mof_span D F0 Λ hL.span_eq_top)
  have hci : ∀ i, c i ∈ Mof D F0 Λ := fun i => by rw [hcv]; exact hsM i.2
  choose a haΛ hac using fun i => (mem_Mof D F0 Λ (c i)).1 (hci i)
  let y : s → lpS D F0 Λ := fun i => ⟨(a i : (VS D).V), Submodule.mem_inf.2 ⟨haΛ i, (a i).2⟩⟩
  let sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X :=
    c.constr D.host.E (fun i => ⟨(y i : (VS D).V) - (ρ (y i) : (VS D).V), hPmem (y i)⟩)
  have hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V) := by
    intro i
    simp only [sE, Basis.constr_basis]
  have hsE : ∀ b, (Submodule.Quotient.mk (sE b) : WbQ D F0) = b := by
    have hlin : (F0.X.comap (perpS (VS D) F0.X).subtype).mkQ ∘ₗ sE = LinearMap.id := by
      refine c.ext fun i => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.id_coe, id_eq]
      conv_rhs => rw [← hac i]
      rw [mk_eq_mk, hsEc]
      have : (y i : (VS D).V) = (a i : (VS D).V) := rfl
      rw [this, sub_sub_cancel_left]
      exact F0.X.neg_mem (hρX (y i))
    intro b
    exact LinearMap.congr_fun hlin b
  refine ⟨sE, hsE, ?_⟩
  intro m hm
  obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
  let yb : lpS D F0 Λ := ⟨(b : (VS D).V), Submodule.mem_inf.2 ⟨hbΛ, b.2⟩⟩
  obtain ⟨d, hd0, hdM⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom c (Mof D F0 Λ) hMlat.fg
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 (hdM _ hm)
  rw [sE_eq Λ ρ hρid c a hac y (fun i => rfl) sE hsEc b yb rfl d hd0 o ho]
  exact hPΛ yb

end Section

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HermFormShiftedVectorZero
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adjust

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def IsDual0 (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ a b, (VS D).hT (F0.e a) (g b) = if a = b then 1 else 0

def AggOK (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ v ∈ Λ, ycL F0 g v ∈ Λ

variable {F0}

theorem int_smul_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E}
    (hc : c ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) {v : (VS D).V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ o hv

theorem hT_g_e {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a b : Fin D.R.rS) :
    (VS D).hT (g a) (F0.e b) = if b = a then 1 else 0 := by
  rw [hT_swap D, hg b a]
  split_ifs <;> simp

theorem hT_g_xc {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a : Fin D.R.rS) (v : (VS D).V) :
    (VS D).hT (g a) (xcL F0 g v) = (VS D).hT (g a) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xcL_apply, map_sum]
  simp [hT_g_e hg]

theorem hT_xc_yc (g : Fin D.R.rS → (VS D).V) (l w : (VS D).V) :
    (VS D).hT l (xcL F0 g w) = (VS D).hT (ycL F0 g l) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xcL_apply, ycL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_smul, smul_eq_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hT_swap D,
    mul_comm]

theorem xc_agg {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V}
    (hok : AggOK F0 Λ g) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {w : (VS D).V} (hw : w ∈ Λ) :
    xcL F0 g w ∈ Λ := by
  have h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hu
  rw [← h, mem_dual_iff]
  intro l hl
  rw [hT_xc_yc]
  exact int_of_unimod hu (hok l hl) hw

theorem isSplitF_of {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f : Fin D.R.rS → (VS D).V}
    (hf : IsDualF F0 f) (hz : ∀ a, (VS D).hT (f a) F0.z = 0) (hok : AggOK F0 Λ f)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) : IsSplitF F0 Λ f := by
  refine ⟨hf, hz, ?_⟩
  intro v hv
  have hy : ycL F0 f v ∈ Λ := hok v hv
  have hw : v - ycL F0 f v ∈ Λ := Submodule.sub_mem _ hv hy
  have hx : xcL F0 f (v - ycL F0 f v) ∈ Λ := xc_agg hok hu hw
  refine ⟨xcL F0 f (v - ycL F0 f v), v - ycL F0 f v - xcL F0 f (v - ycL F0 f v), ycL F0 f v,
    hx, xc_mem_X _, Submodule.sub_mem _ hw hx, ?_, ?_, hy, yc_mem_span _, by abel⟩
  · intro a
    rw [map_sub, map_sub, hT_e_yc hf, sub_self, zero_sub, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), neg_zero]
  · intro a
    rw [map_sub, hT_f_xc hf, sub_self]

end Adjust

def RowDualFrame : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ g : Fin D.R.rS → (VS D).V, IsDual0 F0 g ∧ AggOK F0 Λ g

def RowZUnit : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ l0 ∈ Λ, l0 ∈ perpS (VS D) F0.X ∧ (VS D).hT l0 F0.z = 1

def TraceOne : Prop :=
  ∀ D : D7, ∃ t : 𝓞 D.host.E, (t : D.host.E) + star (t : D.host.E) = 1

section Assembly

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}

def gz (g : Fin D.R.rS → (VS D).V) (l0 : (VS D).V) : Fin D.R.rS → (VS D).V :=
  fun b => g b - (VS D).hT F0.z (g b) • l0

def giso (F0 : FlagG (VS D) D.R.rS T) (g : Fin D.R.rS → (VS D).V) (t : D.host.E) : Fin D.R.rS → (VS D).V :=
  fun b => g b - t • xcL F0 g (g b)

theorem gz_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {l0 : (VS D).V}
    (hl : l0 ∈ perpS (VS D) F0.X) : IsDual0 F0 (gz (F0 := F0) g l0) := by
  intro a b
  rw [gz, map_sub, map_smul, hl _ (e_mem_X F0 a), smul_zero, sub_zero, hg a b]

theorem hermForm_shifted_vector_zero {g : Fin D.R.rS → (VS D).V} {l0 : (VS D).V} (hl1 : (VS D).hT l0 F0.z = 1) (b : Fin D.R.rS) :
    (VS D).hT (gz (F0 := F0) g l0 b) F0.z = 0 := by
  rw [gz, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hl1, starRingEnd_apply, smul_eq_mul,
    mul_one, ← hT_swap D, sub_self]

theorem yc_gz (g : Fin D.R.rS → (VS D).V) (l0 v : (VS D).V) :
    ycL F0 (gz (F0 := F0) g l0) v = ycL F0 g v - (VS D).hT F0.z (ycL F0 g v) • l0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ycL_apply, ycL_apply, map_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [gz, smul_sub, map_smul, smul_eq_mul, smul_smul]

theorem gz_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (hzΛ : F0.z ∈ Λ) {l0 : (VS D).V} (hl0 : l0 ∈ Λ) :
    AggOK F0 Λ (gz (F0 := F0) g l0) := by
  intro v hv
  rw [yc_gz]
  exact Submodule.sub_mem _ (hok v hv) (int_smul_mem (int_of_unimod hu hzΛ (hok v hv)) hl0)

theorem giso_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (t : D.host.E) : IsDual0 F0 (giso F0 g t) := by
  intro a b
  rw [giso, map_sub, map_smul, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), smul_zero, sub_zero, hg a b]

theorem hT_giso_z_eq_zero_of_hT_z_eq_zero {g : Fin D.R.rS → (VS D).V} (hz : ∀ b, (VS D).hT (g b) F0.z = 0) (t : D.host.E) (b : Fin D.R.rS) :
    (VS D).hT (giso F0 g t b) F0.z = 0 := by
  rw [giso, map_sub, LinearMap.sub_apply, hz b, map_smulₛₗ, LinearMap.smul_apply,
    hX_perp F0 (xc_mem_X _) (z_mem_perp D F0), smul_zero, sub_zero]

theorem yc_giso (g : Fin D.R.rS → (VS D).V) (t : D.host.E) (v : (VS D).V) :
    ycL F0 (giso F0 g t) v = ycL F0 g v - t • xcL F0 g (ycL F0 g v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ycL_apply, ycL_apply, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [giso, smul_sub, map_smul, smul_comm]

theorem giso_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (t : 𝓞 D.host.E) : AggOK F0 Λ (giso F0 g (t : D.host.E)) := by
  intro v hv
  rw [yc_giso]
  refine Submodule.sub_mem _ (hok v hv) ?_
  rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, algebraMap_smul]
  exact Submodule.smul_mem _ t (xc_agg hok hu (hok v hv))

theorem giso_iso {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {t : D.host.E} (ht : t + star t = 1) :
    ∀ a b, (VS D).hT (giso F0 g t a) (giso F0 g t b) = 0 := by
  intro a b
  have h1 : (VS D).hT (g a) (xcL F0 g (g b)) = (VS D).hT (g a) (g b) := hT_g_xc hg a (g b)
  have h2 : (VS D).hT (xcL F0 g (g a)) (g b) = (VS D).hT (g a) (g b) := by
    rw [hT_swap D, hT_g_xc hg b (g a), ← hT_swap D]
  have h3 : (VS D).hT (xcL F0 g (g a)) (xcL F0 g (g b)) = 0 := hX_X F0 (xc_mem_X _) (xc_mem_X _)
  simp only [giso, map_sub, LinearMap.sub_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, h1, h2, h3, mul_zero]
  linear_combination (-(VS D).hT (g a) (g b)) * ht

end Assembly

theorem rowSplitF_of (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowSplitF := by
  intro D u F0 Λ hΛ
  obtain ⟨g, hg, hok⟩ := h1 D u F0 Λ hΛ
  obtain ⟨l0, hl0, hlp, hl1⟩ := h2 D u F0 Λ hΛ
  obtain ⟨t, ht⟩ := h3 D
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hzΛ : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have hg' := gz_dual hg hlp
  have hok' := gz_ok hok hu hzΛ hl0
  have hz' := hermForm_shifted_vector_zero (F0 := F0) (g := g) hl1
  have hd := giso_dual hg' (t : D.host.E)
  exact ⟨giso F0 (gz (F0 := F0) g l0) (t : D.host.E),
    isSplitF_of ⟨hd, giso_iso hg' ht⟩ (hT_giso_z_eq_zero_of_hT_z_eq_zero hz' _) (giso_ok hok' hu t) hu⟩

theorem rowClass_of_three (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowClass :=
  rowClass_of_split (rowSplitF_of h1 h2 h3)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RsMemPerpIff
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coord

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem rs_e_mem_X (a : Fin D.R.rS) : F0.e a ∈ F0.X := Submodule.subset_span ⟨a, rfl⟩

theorem rs_hT_e_X (a : Fin D.R.rS) {x : (VS D).V} (hx : x ∈ F0.X) : (VS D).hT (F0.e a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso a b
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem rs_mem_perp_iff' (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ ∀ a, (VS D).hT (F0.e a) y = 0 := by
  constructor
  · intro hy a
    exact hy _ (rs_e_mem_X D F0 a)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact h b
    | zero => simp
    | add w w' _ _ h1 h2 => simp [h1, h2]
    | smul c w _ h' => simp [h']

theorem rs_X_le_perp : F0.X ≤ perpS (VS D) F0.X := fun x hx =>
  (rs_mem_perp_iff' D F0 x).2 fun a => rs_hT_e_X D F0 a hx

theorem rs_mk_X_zero {x : (VS D).V} (hx : x ∈ F0.X) (hp : x ∈ perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨x, hp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact hx

variable {D F0} {f : Fin D.R.rS → (VS D).V}

theorem rs_hT_f_e (hf : PartnerOK D F0 f) (a b : Fin D.R.rS) :
    (VS D).hT (f a) (F0.e b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
  split_ifs <;> simp

end Coord

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

