module

public import Formalism.LocalToGlobal.GroupLattices.JointServices
public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Mathlib
public import Formalism.SizeWindowBrackets.Bundle0003
public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
public import Formalism.SizeWindowBrackets.Bundle0001
public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.SizeWindowBrackets.Bundle0004
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.LocalToGlobal.GroupLattices.JointServices.VAddEqVw
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.JointServices.Cut
section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem carrier_sum {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {ι : Type} (S : Finset ι) (f : ι → V) (h : ∀ i ∈ S, f i ∈ M.carrier) : ∑ i ∈ S, f i ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq] at h ⊢
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨c1, hc1⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨c2, hc2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨c1 + c2, ?_⟩
    rw [hc1, hc2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [add_smul]

theorem gen_mem_carrier {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {v : V} (hv : v ∈ M.gen) : v ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq]
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd hv h)]
  simp

theorem cutUp_of_stable (D : D7) (μ : D.what₂.Tup)
    (h : ∀ (a : 𝓞 D.what₂.LL), ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • x ∈ (D.what₂.Mtilde μ).carrier) :
    CutUp D μ := by
  classical
  unfold CutUp
  rintro x ⟨c, hc⟩ hx0
  have hxM : x ∈ (D.what₂.Mtilde μ).carrier := by
    rw [hc]
    exact carrier_sum _ _ _ (fun w hw => h (c w) w (gen_mem_carrier _ hw))
  refine ⟨{x}, fun _ => 1, ?_, ?_⟩
  · rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Set.mem_inter hxM hx0
  · simp

end Formalism.L2.G.ServJoint

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.JointServices.ShiftIdealSgFl
section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Indef Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.G.ServJoint

variable {D : D7}

def sgFl (L : SizeData₂ D) (u : D.what₂.Word) (z : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℝ :=
  ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ)

theorem sg_off (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : w ∉ L.supp) : L.sg u w = 0 := by
  unfold SizeData₂.sg
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : L.gain j w = 0 := L.gain_supp j w hw
  have h2 := L.F_supp j w hw
  have h3 := L.E_supp u j w hw
  simp [SizeData₂.gainD, h1, h2, h3]

theorem shiftZ_sgFl (L : SizeData₂ D) (u : D.what₂.Word) (z : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    shiftZ (sgFl L u) z = ⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ := by
  first
  | rfl
  | (simp [shiftZ, sgFl])
  | (unfold shiftZ sgFl; simp)

theorem shiftIdeal_sgFl (L : SizeData₂ D) (u : D.what₂.Word) : Formalism.DivisionValues.shiftIdeal (shiftZ (sgFl L u)) = Iu D L u := by
  unfold Formalism.DivisionValues.shiftIdeal Iu
  rw [finprod_eq_prod_of_mulSupport_subset (s := L.supp.map D.plEq.toEmbedding)]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [shiftZ_sgFl]
  · intro z hz
    rw [Function.mem_mulSupport] at hz
    rw [Finset.coe_map, Set.mem_image]
    refine ⟨D.plEq.symm z, ?_, by simp⟩
    by_contra h
    apply hz
    rw [shiftZ_sgFl, sg_off L u _ h]
    simp [ur]

theorem Iu_ne_zero (L : SizeData₂ D) (u : D.what₂.Word) : Iu D L u ≠ 0 := by
  unfold Iu
  rw [Finset.prod_ne_zero_iff]
  intro x _
  apply zpow_ne_zero
  first
  | exact FractionalIdeal.coeIdeal_ne_zero.mpr (D.plEq x).ne_bot
  | exact (FractionalIdeal.coeIdeal_ne_zero).2 (HeightOneSpectrum.ne_bot _)
  | simp [(D.plEq x).ne_bot]

theorem nu_map_eq (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC Nu : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L = NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)))
    (hshift : NuC = shiftLat Nu (sgFl L u)) :
    Nu.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) = L.NuLat u := by
  set f := ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) with hf

  have hmap : ∀ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (N : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL)),
      (Formalism.HermitianLatticesTheory.idealSmul I N).map f = Formalism.HermitianLatticesTheory.idealSmul I (N.map f) := by
    intro I N
    unfold Formalism.HermitianLatticesTheory.idealSmul
    rw [Submodule.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, f x, Submodule.mem_map_of_mem hx, by simp [hf]⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp [hf]⟩
  have hN' : (D.div.Nu u).L = Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (L.NuLat u) := by
    rw [hN u]
    rfl
  have h1 : Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (Nu.map f) =
      Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (L.NuLat u) := by
    rw [← hmap, ← hN', hlat, hshift, shiftLat, shiftIdeal_sgFl]
  have hIu : Iu D L u ≠ 0 := Iu_ne_zero L u
  have hone : ∀ X : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V,
      Formalism.HermitianLatticesTheory.idealSmul ((((Iu D L u)⁻¹ * Iu D L u : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL)) :
        Submodule (𝓞 D.what₂.LL) D.what₂.LL) X = X := by
    intro X
    rw [inv_mul_cancel₀ hIu, FractionalIdeal.coe_one, Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_one]
  rw [← hone (Nu.map f), ← hone (L.NuLat u), FractionalIdeal.coe_mul, Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_mul,
    Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_mul, h1]

theorem nu_into (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC Nu : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L = NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)))
    (hshift : NuC = shiftLat Nu (sgFl L u)) : ∀ x ∈ Nu, e x ∈ L.NuLat u := by
  intro x hx
  rw [← nu_map_eq L hN u e NuC Nu hlat hshift]
  exact Submodule.mem_map_of_mem hx

end Formalism.L2.G.ServJoint

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg
section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem perCol_lin (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (φ : D.what₂.Mu u) :
    ∃ f : D.what₂.Amb μ →ₗ[ℂ] ℂ, ∀ F, D.what₂.perCol u μ φ F = f F := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    refine ⟨((D.mem u).P.period ((D.mem u).P.lowerMap ((D.mem u).P.evz ((D.mem u).C.col ↑(D.eMu u φ))))).comp
      (D.eMt u).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_base_eq_PtilCol]
    rfl
  · refine ⟨((D.PTw u μ).period ((D.PTw u μ).lowerMap ((D.PTw u μ).evz
      ((D.chTw u μ).col (D.e0Tw u μ ↑(D.eMu u φ)))))).comp (D.eMtTw u μ).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_tie u μ h]
    rfl

theorem perToVal2 : PerToVal2 := by
  intro D B hB u t hcut z s N h φ hφ F hF
  obtain ⟨s0, hOk⟩ := hB.ok
  have hV0 : B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F) ∈ D.what₂.V0 (B.I.tup t) := by
    refine ⟨B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F), ?_⟩
    have h1 := (hB.sharp.forms t).op_eq ((rV0 D B.A B.Ps B.ψs t).mulVec F)
    rw [level_operator_fixes_image hOk B.Ps B.ψs B.Zs t F] at h1
    exact h1
  have hgen := ((hB.sharp.Mtilde t).2 _).1 ((image_mem_nabla_iff hOk B.Ps B.ψs B.Zs t F).2 hF)
  obtain ⟨S, c, hS, hx0⟩ := hcut _ hgen hV0
  have key : ∀ φ ∈ Submodule.span (𝓞 D.what₂.LL) N, VGeq z s (B.Dc.Pt (B.I.wU u) t φ F) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      have hex : ∀ y : D.what₂.Amb (B.I.tup t), ∃ a : D.what₂.LL, y ∈ S →
          (D.what₂.embLL a = D.what₂.perCol u (B.I.tup t) (D.jN u (B.I.eNu u x)) y ∧ (a = 0 ∨ s ≤ (vAdd z a : ℝ))) := by
        intro y
        by_cases hy : y ∈ S
        · obtain ⟨a, ha⟩ := h x hx y (hS hy).1 (hS hy).2
          exact ⟨a, fun _ => ha⟩
        · exact ⟨0, fun h' => absurd h' hy⟩
      choose a ha using hex
      obtain ⟨f, hf⟩ := perCol_lin D u (B.I.tup t) (D.jN u (B.I.eNu u x))
      have heq : B.Dc.Pt (B.I.wU u) t x F = ∑ y ∈ S, ((c y : 𝓞 D.what₂.LL) : D.what₂.LL) * a y := by
        apply D.what₂.embLL.injective
        rw [hB.dcPt u t x F, hf]
        refine (congrArg f hx0).trans ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [map_smul, smul_eq_mul, map_mul, (ha y hy).1, hf]
      rw [heq]
      exact VGeq.sum S _ fun y hy => VGeq.int_mul (c y) (ha y hy).2
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact VGeq.zero z s
    | add x y _ _ hx hy =>
      rw [map_add (f := _), LinearMap.add_apply]
      exact hx.add hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact VGeq.int_mul a hx
  exact (key φ hφ).vw

theorem val2AllAtR : SecondLevelValuationAtRestricted := by
  intro D L B hB hcut h u Nu hNu z
  have hμ := hB.mu (D.plEq.symm z)
  rw [Equiv.apply_symm_apply] at hμ
  have h2 : ∀ μ, D.what₂.muAt (D.plEq.symm z) = μ → ∀ φ ∈ L.NuLat u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
        (y = 0 ∨ ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) ≤ (vAdd (D.plEq (D.plEq.symm z)) y : ℝ)) := by
    rintro μ rfl
    exact h u (D.plEq.symm z)
  have h3 := perToVal2 D B hB u (B.S1.μ z) (hcut _ (hμ ▸ used_muAt D (D.plEq.symm z))) z ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) (Nu : Set _)
    (fun x hx F hF1 hF0 => by
      have h4 := h2 _ hμ _ (hNu x hx) F hF1 hF0
      rw [Equiv.apply_symm_apply] at h4
      exact h4)
  rw [Submodule.span_eq] at h3
  exact h3

end Formalism.L2.G.ServJoint

end
end

