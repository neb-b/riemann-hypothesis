module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixStandardChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixNbhd

open Matrix

def fixTrans {M : Type} [AddCommGroup M] (g : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, g (x + u) = g x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_fixTrans {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {g : M → ℂ}
    (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) : IsOpen (fixTrans g : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, g (x + u) = g x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport g
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport g
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem exists_dot_ker {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (χ : AddChar K ℂ) (hχ : IsLocallyConstant χ) (κ : Type) [Fintype κ] [NonarchimedeanAddGroup (κ → K)]
    (C : Set (κ → K)) (hC : IsCompact C) :
    ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  let V : Set K := {t | χ t = 1}
  have hV : IsOpen V := hχ.isOpen_fiber 1
  have h0 : (0 : K) ∈ V := AddChar.map_zero_eq_one χ
  have hadd : ∀ s t, s ∈ V → t ∈ V → s + t ∈ V := fun s t hs ht => by
    show χ (s + t) = 1
    rw [AddChar.map_add_eq_mul, show χ s = 1 from hs, show χ t = 1 from ht, one_mul]
  have hc1 : Continuous fun p : (κ → K) × (κ → K) => p.2 ⬝ᵥ p.1 := continuous_snd.dotProduct continuous_fst
  have hc2 : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 := continuous_fst.dotProduct continuous_snd
  have N0 : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ V := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    exact hc1.tendsto ((0 : κ → K), z) (hV.mem_nhds (by simpa using h0))
  have N1 : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ V} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hc2.tendsto ((0 : κ → K), (0 : κ → K)) (hV.mem_nhds (by simpa using h0))
  rw [nhds_prod_eq, Filter.mem_prod_iff] at N1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := N1
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (Filter.inter_mem (Filter.inter_mem N0 ht₁) ht₂)
  refine ⟨H, fun z hz a ha b hb => hadd _ _ ((hH hb).1.1 z hz) ?_⟩
  exact hsub (Set.mk_mem_prod (hH ha).1.2 (hH hb).2)

variable {F : Type} [Field F] [NumberField F]

theorem adeleJoin_zero_apply {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dotProduct_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let q1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let q2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = q1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = q2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, dotProduct, map_sum]
    change ∑ i, q1 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    exact mul_zero _
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, dotProduct, map_sum]
    change ∑ i, q2 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i) = ∑ i, (v i).2 * y i
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    rfl

theorem exists_fix_pure [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (κ : Type) [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y)
        (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨H, hH⟩ := exists_dot_ker (GlobalTheory.HeisSchA.finChar ψ) (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ) κ
    (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨fixTrans g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_fixTrans hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    rfl
  have hz : GlobalTheory.WeilM.pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = GlobalTheory.WeilM.pureA F f g z := by
    simp only [GlobalTheory.WeilM.pureA]
    rw [hf, hgz, hx1]
  simp only [GlobalTheory.WeilM.schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [GlobalTheory.WeilM.pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dotProduct_adeleJoin_zero, dotProduct_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [GlobalTheory.WeilM.schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

theorem schr_fix_nbhd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) Φ = Φ := by
  intro D ψ hψ κ _ Φ hΦ
  exact exists_fix D.host.F ψ hψ.1.1 κ Φ hΦ

end GlobalTheory.SchrFixNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatMulInvIdealLatticeMemIntegral
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.IdealDenom

open Formalism.MainNotions.StandardLatticesGL3 (IhE OhE inc)

theorem exists_nat_mul_mem {D : D7} (cc : Ideal (𝓞 D.host.K)) : ∃ n : ℕ, 0 < n ∧
    ∀ t ∈ IhE D cc, (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t ∈ OhE D := by
  obtain ⟨a₀, ha₀, hint⟩ := D.host.AA0.isFractional
  have ha₀' : (algebraMap (𝓞 D.host.E) D.host.E a₀) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero ha₀ (IsFractionRing.injective (𝓞 D.host.E) D.host.E (by simpa using h))
  obtain ⟨n, hn, hmem⟩ := GlobalTheory.NormSum.Expand.denom (inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹)
  refine ⟨n, hn, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hci : IsIntegral ℤ (((c : D.host.K) : D.host.E)) :=
      (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    have hcm : inc D (((c : D.host.K) : D.host.E)) ∈ OhE D :=
      GlobalTheory.NormSum.Expand.inc_int (⟨_, hci⟩ : 𝓞 D.host.E)
    have hbm := GlobalTheory.NormSum.Expand.inc_int b
    have hab : a = (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹ * algebraMap (𝓞 D.host.E) D.host.E b := by
      rw [hb, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ha₀', one_mul]
    have key : (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        ((n : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹) *
          (inc D (((c : D.host.K) : D.host.E)) *
            inc D (algebraMap (𝓞 D.host.E) D.host.E b) * s) := by
      rw [hab, map_mul, map_mul]; ring
    rw [key]
    exact (OhE D).mul_mem hmem ((OhE D).mul_mem ((OhE D).mul_mem hcm hbm) hs)
  | zero => rw [mul_zero]; exact (OhE D).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (OhE D).add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact (OhE D).neg_mem hx

theorem exists_nat_mul_inv_mul_mem : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), ∃ M : ℕ, 0 < M ∧
    ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  intro D cc r
  obtain ⟨n₁, h₁, m₁⟩ := GlobalTheory.NormSum.Expand.denom (inc D r⁻¹)
  obtain ⟨n₂, h₂, m₂⟩ := exists_nat_mul_mem cc
  refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, fun t ht => ?_⟩
  have key : ((n₁ * n₂ : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D r⁻¹ * t) =
      ((n₁ : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D r⁻¹) * ((n₂ : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) := by
    push_cast; ring
  rw [key]
  exact (OhE D).mul_mem m₁ (m₂ t ht)

end GlobalTheory.NormSum.IdealDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelParabolicConjInvTransposeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelParabolic_conj_invTranspose : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  first | exact @GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | exact GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | (intros; apply GlobalTheory.SiegelTransposeInverse.exists_siegel_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLevi
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

namespace GlobalTheory.CentralLevi

theorem exists_unit_smul_of_central : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ f g hg hc
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ f

  let Dα : GL (Fin (r + 1)) (AF F ⊗[F] E) → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun α =>
    ⟨cT (sigR (AF F) σ) (α⁻¹).1, cT (sigR (AF F) σ) α.1,
      by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one],
      by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]⟩
  have hmem : ∀ α, lv α ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := fun α => by
    refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨⟨α, trivial, hlv.onC α⟩, ⟨Dα α, trivial, hlv.onD α⟩⟩
  obtain ⟨B, -, hB⟩ := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg (Fin.last r)) (Finset.mem_singleton_self _)).1
  change GL (Fin (r + 1)) (AF F ⊗[F] E) at B
  change (matHom _ σ J g).1 * adMat F X = adMat F X * B.1 at hB
  have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, f.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ α : GL (Fin (r + 1)) (AF F ⊗[F] E), B.1 * α.1 = α.1 * B.1 := fun α => by
    have e := congrArg (fun h => (matHom _ σ J h).1 * adMat F X) (hc (lv α) (hmem α))
    simp only [map_mul, Units.val_mul] at e
    have e1 : (matHom _ σ J g).1 * (matHom _ σ J (lv α)).1 * adMat F X = adMat F X * (B.1 * α.1) := by
      rw [Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have e2 : (matHom _ σ J (lv α)).1 * (matHom _ σ J g).1 * adMat F X = adMat F X * (α.1 * B.1) := by
      rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hlv.onC, Matrix.mul_assoc]
    have := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) (e1.symm.trans (e.trans e2))
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  obtain ⟨c, hcB⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := B.1) fun t =>
    (hcomm ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩).symm
  have hu : IsUnit c := by
    have h1 := congrFun (congrFun (Units.mul_inv B) 0) 0
    rw [← hcB, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    exact ⟨⟨c, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, ?_⟩
  rw [hB, ← hcB, IsUnit.unit_spec]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

end GlobalTheory.CentralLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finsetSum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoordsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_action_on_tensorCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  first | exact @GlobalTheory.InertCoordAct.act_kap | exact GlobalTheory.InertCoordAct.act_kap | (intros; apply GlobalTheory.InertCoordAct.act_kap <;> assumption)
end

