module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HTAaLbMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFiniteR : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

def RowLatExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u : D.what₂.Word), ∃ Λ, IsRowLat D (T.X.Fu u) Λ

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cExpl_pos' (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (hne : what₂.Nonempty) :
    0 < cExpl D F0 what₂ := by
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hc := (Formalism.L2.SG.Pf.Asm.cMass_spec hK hF (D.R.k - 1) (by omega)).1
  have hd : 0 < |(NumberField.discr D.host.F : ℝ)| ^
      (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
    apply zpow_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hL : 0 < ∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← lValEta_eq_lValEtaF hK hF i hi2]
    exact lValEta_pos hK i hi2
  have hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂ := by
    intro Λ hΛ
    exact _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) (D.mem u).A.T (D.mem u).A.T_prime.pos F0 Λ (hR.1 Λ hΛ)
  have hm := Formalism.L2.SG.PairVal.massRows_pos D F0 what₂ hA hne
  unfold cExpl
  positivity


end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsoGenLeft
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_e_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.eX c) (nL X X0 xs M w) = 0 := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).1, X.ee]

theorem h_f_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.fY c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).2, h_fe, Finset.sum_ite_eq]

theorem h_xs_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (xs c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(inW_left X (hxs c) _).1]

theorem g_ew (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nL X X0 xs M w) = (VS D).hT (X.eX a) w := by
  rw [h_nE_left, (hw a).1]
  simp [h_e_nLw X X0 xs M hxs hw]

theorem g_fw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nL X X0 xs M w) = (VS D).hT (X.fY a) w := by
  rw [h_nF_left, (hw a).2]
  simp [h_e_nLw X X0 xs M hxs hw, h_f_nLw X X0 xs M hxs hw, h_xs_nLw X X0 xs M hxs hw]

theorem g_ww (hxs : ∀ b, InW X (xs b)) {w w' : (VS D).V} (hw : InW X w) (hw' : InW X w') :
    (VS D).hT (nL X X0 xs M w) (nL X X0 xs M w') = (VS D).hT w w' := by
  rw [nL_w X X0 xs M hw, nL_w X X0 xs M hw', LinearMap.map_add₂, map_add (f := _), map_add (f := _), h_sum_left, h_sum_left,
    h_sum_right]
  simp [h_sum_right, (hw' _).1, (inW_left X hw _).1, X.ee]

theorem iso_gen_left (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (g : (VS D).V) (hg : ∀ c, (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.eX c)) = (VS D).hT g (X.eX c) ∧
      (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.fY c)) = (VS D).hT g (X.fY c))
    (hgw : ∀ w, InW X w → (VS D).hT (nL X X0 xs M g) (nL X X0 xs M w) = (VS D).hT g w) (y : (VS D).V) :
    (VS D).hT (nL X X0 xs M g) (nL X X0 xs M y) = (VS D).hT g y := by
  conv_lhs => rw [decomp X y]
  conv_rhs => rw [decomp X y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul]
  rw [hgw _ (inW_pW X y)]
  simp only [(hg _).1, (hg _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MapInv
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section Inv

variable (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0)
  (hd : ∀ a, X0 a a = 1)

include hup hd

theorem det_one : X0.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hup i j hij)]
  simp [hd]

theorem inv_mul : X0⁻¹ * X0 = 1 := Matrix.nonsing_inv_mul _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem mul_inv : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem inv_up : ∀ b a : Fin D.R.rS, a < b → X0⁻¹ b a = 0 := by
  have hU : IsUnit X0.det := by rw [det_one X0 hup hd]; exact isUnit_one
  have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
  have : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
  exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h

theorem inv_diag : ∀ a, X0⁻¹ a a = 1 := by
  intro a
  have h := congrFun (congrFun (mul_inv X0 hup hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [inv_up X0 hup hd e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

theorem map_inv' {K : Type*} [Field K] (f : D.host.E →+* K) : (X0.map f)⁻¹ = X0⁻¹.map f := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, inv_mul X0 hup hd, Matrix.map_one _ f.map_zero f.map_one]

end Inv

theorem gram_mem (xs : Fin D.R.rS → (VS D).V) (hxs : ∀ b, xs b ∈ aaLb X b) (b c : Fin D.R.rS) :
    Gq D xs b c ∈ aaD D b * aaD D c := by
  show (VS D).hT (xs b) (xs c) ∈ aaD D b * aaD D c
  suffices H : ∀ y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ d ∈ (aaD D c : Set D.host.E), ∃ l ∈ X.Lb, y = d • l},
      (VS D).hT (xs b) y ∈ aaD D b * aaD D c from H _ (hxs c)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, hdm, l, hl, rfl⟩ := hz
    rw [map_smul, smul_eq_mul, mul_comm d]
    exact FractionalIdeal.mul_mem_mul (LatA.hT_aaLb_mem X (hxs b) hl) hdm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul]
    have h := ((aaD D b * aaD D c : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx
    rw [Algebra.smul_def] at h
    exact h

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowRankHolds
section
noncomputable section

open NumberField Formalism.BasicNotions Module
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem rowRank_holds : RowRank := by
  intro D X b
  set S := Submodule.span D.host.E (aaLbS X b : Set (VS D).V) with hSdef
  have hSfin : finrank D.host.E S = D.R.k + 1 := by
    rw [hSdef, span_aaLbS, finrank_span_Lb]
  have hSle : ∀ x ∈ aaLbS X b, x ∈ S := fun x hx => Submodule.subset_span hx
  let B : Basis (Fin (D.R.k + 1)) D.host.E S := Module.finBasisOfFinrankEq D.host.E S hSfin
  let eS : S ≃ₗ[D.host.E] (Fin (D.R.k + 1) → D.host.E) := B.equivFun
  let Φ : (Fin (D.R.k + 1) → D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
    (S.subtype.comp eS.symm.toLinearMap).restrictScalars (𝓞 D.host.E)
  have hΦ : ∀ y, Φ y = ((eS.symm y : S) : (VS D).V) := fun y => rfl
  have hΦinj : Function.Injective Φ := by
    intro y y' h
    rw [hΦ, hΦ] at h
    exact eS.symm.injective (Subtype.ext h)
  let A : Submodule (𝓞 D.host.E) (Fin (D.R.k + 1) → D.host.E) := (aaLbS X b).comap Φ
  have hmemA : ∀ y, y ∈ A ↔ Φ y ∈ aaLbS X b := fun y => Iff.rfl

  have hmap : A.map Φ = aaLbS X b := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun x hx => ?_
    refine ⟨eS ⟨x, hSle x hx⟩, ?_, ?_⟩
    · show Φ (eS ⟨x, hSle x hx⟩) ∈ aaLbS X b
      rw [hΦ, LinearEquiv.symm_apply_apply]
      exact hx
    · show Φ (eS ⟨x, hSle x hx⟩) = x
      rw [hΦ, LinearEquiv.symm_apply_apply]
  have hAfg : A.FG := Submodule.fg_of_fg_map_injective Φ hΦinj (by rw [hmap]; exact fg_aaLbS X b)

  have hAspan : Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have key : ∀ (v : (VS D).V) (hv : v ∈ S), eS ⟨v, hv⟩ ∈ Submodule.span D.host.E (A : Set _) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        show Φ (eS ⟨x, _⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact hx
      | zero =>
        have : eS ⟨0, S.zero_mem⟩ = 0 := by
          rw [show (⟨0, S.zero_mem⟩ : S) = 0 from rfl, map_zero]
        rw [this]
        exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
        have : eS ⟨x + y, S.add_mem hx hy⟩ = eS ⟨x, hx⟩ + eS ⟨y, hy⟩ := by
          rw [← map_add (f := _)]; rfl
        rw [this]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ihx =>
        have : eS ⟨c • x, S.smul_mem c hx⟩ = c • eS ⟨x, hx⟩ := by
          rw [← map_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ c ihx
    have := key _ (eS.symm y).2
    rwa [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at this

  let Az : Submodule ℤ (Fin (D.R.k + 1) → D.host.E) := A.restrictScalars ℤ
  have h1 : Module.Finite (𝓞 D.host.E) A := Module.Finite.iff_fg.2 hAfg
  have h2 : Module.Finite ℤ A := Module.Finite.trans (𝓞 D.host.E) _
  have h3 : Module.Finite ℤ Az :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) _ A).restrictScalars ℤ).symm
  have hlat : Submodule.IsFullLattice ℚ Az := by
    letI : Submodule.IsLattice ℚ Az := Submodule.IsLattice.of_fg ℚ (Module.Finite.iff_fg.1 h3)
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) := by rw [hAspan]; trivial
    obtain ⟨n, hn, hnx⟩ := Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem A hx
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)
  have hr : finrank ℤ Az = finrank ℚ (Fin (D.R.k + 1) → D.host.E) :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsFullLattice.rank_eq ℚ Az).trans (Module.finrank_eq_rank ℚ (Fin (D.R.k + 1) → D.host.E)).symm)
  let bZ : Basis (Fin (finrank ℚ (Fin (D.R.k + 1) → D.host.E))) ℤ Az := Module.finBasisOfFinrankEq ℤ Az hr
  have hdim : finrank ℚ (Fin (D.R.k + 1) → D.host.E) = finrank ℚ D.host.E * (D.R.k + 1) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

  let eqv : Az ≃ₗ[ℤ] ((aaLbS X b).restrictScalars ℤ) :=
    { toFun := fun y => ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), (hmemA _).1 y.2⟩
      invFun := fun x => ⟨eS ⟨x, hSle x x.2⟩, by
        show Φ (eS ⟨x, hSle x x.2⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact x.2⟩
      map_add' := fun y y' => Subtype.ext (map_add Φ (y : Fin (D.R.k + 1) → D.host.E) y')
      map_smul' := fun c y => Subtype.ext (by
        show Φ (c • (y : Fin (D.R.k + 1) → D.host.E)) = c • Φ (y : Fin (D.R.k + 1) → D.host.E)
        exact map_zsmul Φ c _)
      left_inv := fun y => Subtype.ext (by
        show eS ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), _⟩ = (y : Fin (D.R.k + 1) → D.host.E)
        have : (⟨Φ (y : Fin (D.R.k + 1) → D.host.E), hSle _ ((hmemA _).1 y.2)⟩ : S) = eS.symm y := Subtype.ext (hΦ _)
        rw [this, LinearEquiv.apply_symm_apply])
      right_inv := fun x => Subtype.ext (by
        show Φ (eS ⟨x, _⟩) = (x : (VS D).V)
        rw [hΦ, LinearEquiv.symm_apply_apply]) }
  exact ⟨(bZ.map eqv).reindex (finCongr hdim)⟩

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

