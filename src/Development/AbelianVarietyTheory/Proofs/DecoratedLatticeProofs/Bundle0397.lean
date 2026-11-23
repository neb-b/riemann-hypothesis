module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

variable {v : Pl D}

theorem intAt_mul {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem intAt_zero : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [(finPart D).map_neg]; exact neg_mem ha.2⟩

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [zero_mul]

theorem evalV_single_self (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1

theorem evalV_single_ne {v w : Pl D} (hw : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw

theorem single_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self]; exact one_mem _
  · rw [evalV_single_ne hw]; exact zero_mem _

theorem mul_single {α : Af D.host.F} (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * singleV D.host.F v 1 = α := by
  apply RestrictedProduct.ext
  intro w
  change evalV D.host.F w (α * singleV D.host.F v 1) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self, mul_one]
  · rw [hα w hw, zero_mul]

theorem gen_mem {𝔞 : FI D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ 𝔞) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, rfl⟩

theorem tmul_mem_idAt {α : Af D.host.F} (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hαv _ w.2, TensorProduct.zero_tmul]

theorem tmul_one_mem_intAt {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨tmul_mem_idAt hαv 1, ?_⟩
  change α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D
  exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩

theorem tmul_mul_tmul' (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
      (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]

theorem incA_mul_tmul (x : D.host.E) (α : AF D.host.F) (b : D.host.E) :
    incA D x * (α ⊗ₜ[D.host.F] b : AE D) = α ⊗ₜ[D.host.F] (x * b) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * (α ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_mem_idV {𝔞 𝔟 : FI D} {a b : AE D} (ha : a ∈ idV 𝔞 v) (hb : b ∈ idV 𝔟 v) : a * b ∈ idV (𝔞 * 𝔟) v := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨α, hα, hαv, a, ha, rfl⟩ := ha'
    induction hb using AddSubgroup.closure_induction with
    | mem b' hb' =>
      obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hb'
      rw [tmul_mul_tmul']
      refine gen_mem (fun w => ?_) (fun w hw => ?_) (FractionalIdeal.mul_mem_mul ha hb)
      · rw [map_mul]; exact mul_mem (hα w) (hβ w)
      · rw [map_mul, hαv w hw, zero_mul]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg x _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem incA_mul_mem {𝔞 𝔟 : FI D} {x : D.host.E} (hx0 : x ≠ 0)
    (hx : ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (𝔞 * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem t' ht' =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := ht'
    have e : incA D x * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
        ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] x : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
      rw [incA_mul_tmul, tmul_mul_tmul', mul_single hβv]
    rw [e]
    refine mul_mem_idV ((hx _).2 ⟨?_, tmul_mem_idAt hβv x⟩)
      (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
    rw [incA_mul_tmul, inv_mul_cancel₀ hx0]
    exact tmul_one_mem_intAt hβ hβv
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem idV_mul_gen : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D) (x y : D.host.E), x ≠ 0 → y ≠ 0 → (∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → (∀ s, s ∈ idV 𝔟 v ↔ incA D y⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → ∀ s, s ∈ idV (𝔞 * 𝔟) v ↔ incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 𝔟 x y hx0 hy0 hx hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  intro s
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun s _ => incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨α, hα, hαv, c, hc, rfl⟩
      refine FractionalIdeal.mul_induction_on (C := fun c => incA D (x * y)⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] c) ∈
        intAt D (· = v) ∧ (pairA D.host.F 0 α) ⊗ₜ[D.host.F] c ∈ idAt D (· = v)) hc ?_ ?_
      · intro a ha b hb
        have hA := (hx _).1 (gen_mem hα hαv ha)
        have hB := (hy _).1 (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
        have e : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * b) =
            ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
          rw [tmul_mul_tmul', mul_single hαv]
        rw [e]
        refine ⟨?_, Ideal.mul_mem_right _ _ hA.2⟩
        have e2 : incA D (x * y)⁻¹ * (((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) *
            ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) =
            (incA D x⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a)) *
              (incA D y⁻¹ * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) := by
          rw [mul_inv, (incA D).map_mul]; ring
        rw [e2]
        exact intAt_mul hA.1 hB.1
      · intro c d hc hd
        rw [TensorProduct.tmul_add, mul_add]
        exact ⟨intAt_add hc.1 hd.1, add_mem hc.2 hd.2⟩
    · rw [mul_zero]; exact ⟨intAt_zero, zero_mem _⟩
    · intro a b _ _ ha hb
      rw [mul_add]; exact ⟨intAt_add ha.1 hb.1, add_mem ha.2 hb.2⟩
    · intro a _ ha
      rw [mul_neg]; exact ⟨intAt_neg ha.1, neg_mem ha.2⟩
  · rintro ⟨ho, hs⟩
    have hso : s = incA D x * (incA D y * (incA D (x * y)⁻¹ * s)) := by
      rw [← mul_assoc, ← mul_assoc, ← (incA D).map_mul, ← (incA D).map_mul, mul_inv_cancel₀ hxy0, (incA D).map_one,
        one_mul]
    have ht : incA D y * (incA D (x * y)⁻¹ * s) ∈ idV 𝔟 v := by
      refine (hy _).2 ⟨?_, Ideal.mul_mem_left _ _ ho.1⟩
      rw [← mul_assoc, ← (incA D).map_mul, inv_mul_cancel₀ hy0, (incA D).map_one, one_mul]
      exact ho
    rw [hso]
    exact incA_mul_mem hx0 hx ht

end GlobalTheory.SeeSaw.IdVMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPlaceSplit

variable {D : D7}

theorem coeff_mul_eq {G : Type} [AddMonoid G] (x y : AddMonoidAlgebra ℂ G) :
    (x * y).coeff = x.coeff.sum fun g a => y.coeff.sum fun h b => Finsupp.single (g + h) (a * b) := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]

theorem aconv_eq_prod {G : Type} [AddCommMonoid G] (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv l) = (l.map AddMonoidAlgebra.ofCoeff).prod := by
  induction l with
  | nil =>
    apply AddMonoidAlgebra.ext
    rw [List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_ofCoeff]
    rfl
  | cons e l ih =>
    apply AddMonoidAlgebra.ext
    rw [List.map_cons, List.prod_cons, ← ih, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff,
      AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff]
    rfl

theorem support_prod_mem {G ι : Type} [AddCommMonoid G] (M : AddSubmonoid G) (s : Finset ι) (g : ι → G →₀ ℂ)
    (h : ∀ i ∈ s, ∀ y ∈ (g i).support, y ∈ M) :
    ∀ y ∈ (∏ i ∈ s, AddMonoidAlgebra.ofCoeff (g i)).coeff.support, y ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hy
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
    exact M.zero_mem
  | insert a s ha ih =>
    intro y hy
    rw [Finset.prod_insert ha, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff] at hy
    obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
    obtain ⟨z, hz, hy3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy2)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy3)]
    exact M.add_mem (h a (Finset.mem_insert_self a s) x hx)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) z hz)

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO hO
  simp

theorem comb_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AddMonoidAlgebra ℂ (WO S T))
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (a * b).coeff f = comb ψ S T a.coeff (comb ψ S T b.coeff f) := by
  have hz : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have ha : ∀ u (r r' : ℂ), (r + r') • heisO ψ S T u f = r • heisO ψ S T u f + r' • heisO ψ S T u f :=
    fun u r r' => add_smul _ _ _
  rw [GlobalTheory.HeisComb.comb_comb, coeff_mul_eq, GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha]
  simp only [Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha, Finsupp.sum_single_index, zero_smul]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, symplOH, h x hx y hy, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (b : WO S T →₀ ℂ)
    (h : ∀ y ∈ b.support, symplO S T u y = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (comb ψ S T b f) = comb ψ S T b (heisO ψ S T u f) := by
  unfold comb
  rw [GlobalTheory.HeisComb.heisO_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T u y = 0 := by unfold symplOH; rw [h y hy, mul_zero]
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm y u, h0, GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]

theorem map_infPart_of_mxAt {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {y : Mx D m n} (hy : GlobalTheory.FinPl.MxAt P y) :
    y.map (infPart D) = 0 := by
  funext a b
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact (RingHom.mem_ker).1 (Submodule.mem_inf.1 (hy a b)).1

end GlobalTheory.TwistPlaceSplit

namespace GlobalTheory.TwistPlaceSplit


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  intro D c v t w F hc hv hP j hj i Ψ₁ hΨ
  classical
  set v₀ := (F.Q i).q.v with hv₀def
  have hv₀ : v₀ ∈ w.Q := (hP.places v₀).2 ⟨i, rfl⟩

  have hat : ∀ i', ∀ u ∈ ((F.Q i').eL j).support, GlobalTheory.FinPl.MxAt (· = (F.Q i').q.v) u := by
    intro i' u hu
    have hs := (F.Q i').hs
    obtain ⟨d, hd⟩ : ∃ d, j + d = (F.Q i').s := ⟨(F.Q i').s - j, by omega⟩
    exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (F.Q i').q u (((F.Q i').eL_at j d hd).1 u hu)

  let M : AddSubmonoid (WO (c.V j) (c.V (j + 1))) :=
    { carrier := {y | (∀ x, GlobalTheory.FinPl.MxAt (· = v₀) x → symplO _ _ x y = 0) ∧ y.map (infPart D) = 0}
      add_mem' := fun {y y'} hy hy' => ⟨fun x hx => by rw [symplO_add_right, hy.1 x hx, hy'.1 x hx, add_zero], by
        rw [Matrix.map_add _ (map_add (infPart D)), hy.2, hy'.2, add_zero]⟩
      zero_mem' := ⟨fun x _ => symplO_zero_right _ _ x, by
        funext a b
        simp⟩ }
  have hM : ∀ i' ∈ Finset.univ.erase i, ∀ y ∈ ((F.Q i').eL j).support, y ∈ M := by
    intro i' hi' y hy
    have hne : v₀ ≠ (F.Q i').q.v := fun e => Finset.ne_of_mem_erase hi' (hP.inj e).symm
    exact ⟨fun x hx => GlobalTheory.FinPl.OverSwap.symplO_eq_zero_of_ne hne hx (hat i' y hy), map_infPart_of_mxAt (hat i' y hy)⟩
  set B := ∏ i' ∈ Finset.univ.erase i, AddMonoidAlgebra.ofCoeff ((F.Q i').eL j) with hB
  have hb : ∀ y ∈ B.coeff.support, y ∈ M := support_prod_mem M _ (fun i' => (F.Q i').eL j) hM
  have hprod : w.eQ j = (AddMonoidAlgebra.ofCoeff ((F.Q i).eL j) * B).coeff := by
    rw [hB, Finset.mul_prod_erase Finset.univ (fun i' => AddMonoidAlgebra.ofCoeff ((F.Q i').eL j)) (Finset.mem_univ i),
      ← Fin.prod_ofFn, hP.eQ j hj, ← AddMonoidAlgebra.coeff_ofCoeff (aconv _), aconv_eq_prod, List.map_ofFn]
    rfl

  have hmono : ∀ u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· = v₀),
      u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· ∈ w.Q) := by
    intro u hu
    refine AddSubgroup.closure_mono ?_ hu
    rintro x ⟨α, hα, hvα, rest⟩
    exact ⟨α, hα, fun v' hv' => hvα v' fun e => hv' (by rw [e]; exact hv₀), rest⟩
  refine ⟨comb c.ψ _ _ B.coeff Ψ₁, ⟨(GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 B.coeff Ψ₁ hΨ.1 (fun u hu => (hb u hu).2) hc.std,
    fun u hu => ?_, fun e he u hu hue => ?_⟩, ?_⟩
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt (AddSubgroup.nsmul_mem _ hu 2))),
      hΨ.2.1 u (hmono u hu)]
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)), hΨ.2.2 e he u (hmono u hu) hue]
  · rw [hprod, comb_mul _ _ _ _ _ (fun x hx y hy => (hb y hy).1 x (hat i x (by rwa [AddMonoidAlgebra.coeff_ofCoeff] at hx))),
      AddMonoidAlgebra.coeff_ofCoeff]

end GlobalTheory.TwistPlaceSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw.TwLaw
variable {D : D7}

theorem levChi_flag (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    Lev.levChi V β (Lev.flagL (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) κ =
      Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) κ := by
  unfold Lev.levChi levFn
  congr 3
  simp only [Lev.flagL, Lev.withP, Lev.datY, LevelP.full, LevelP.triv, if_true]
  exact (Lev.subgroupCharExtension_one_apply _ _).trans (Lev.subgroupCharExtension_one_apply _ _).symm

theorem lift_one_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) (hκ : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) :
    Lev.IsLevelLift V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) 1 κ := by
  refine ⟨(Subgroup.mem_inf.1 hκ).1, hκ.2.1, ?_⟩
  have h2 := hκ.2.2
  simp only [Lev.datY, LevelP.triv, if_true] at h2
  exact Subgroup.mem_bot.1 h2

theorem lift_one_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β L 1 = 1 := by
  unfold Lev.levChi
  rw [map_one]
  have : levFn β L 1 = 1 := (levChar D.sp.cm V.gram β L).map_one
  rw [this, Units.val_one]


set_option maxHeartbeats 1000000 in
open Classical in
theorem vecLawQ (D : D7) (c : Com D) (w : Twist D) (hw : w.Is c) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D)
    (hs : IsStage c w k s) (hs' : IsStage c w (k + 1) s') (p : Step c s s') (hp : IsStep w (k + 1) p) :
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  obtain ⟨hr, hL, hfs⟩ := hs
  obtain ⟨hr', hL', hfs'⟩ := hs'
  obtain ⟨f₀, hv⟩ := hp.vec
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  rw [hw.union] at hres uS uT
  have hG : ∀ PP ∈ w.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.chi (k + 1) PP)⁻¹ ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.chi (k + 1) PP)⁻¹ := fun PP hP => by
    rw [← hw.chiPg (k + 1) PP hP]; exact hres PP (Finset.mem_union_left _ hP)
  have hQ : ∀ PP ∈ w.Q, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.ξ PP) ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.ξ PP) := fun PP hP => by
    have := hres PP (Finset.mem_union_right _ hP)
    rwa [hw.chiQ (k + 1) PP hP, inv_inv] at this
  rw [hL] at hv
  have ea : s.V.rank = D.R.r + k * D.R.t := hfs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hfs'.rank
  have law := fun {g0 : G0 w.Pg D.R.r} {g : GA D s.V} {h : GA D s'.V} =>
    @GlobalTheory.StepVecLaw.step_law D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β f₀ p.f
      hp.weil hfs.sigOK hfs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
      hfs.selfDual hfs'.selfDual hfs.frame hfs'.frame D.R.r D.R.t k hr hr' ea eb w.Pg w.Q hw.disj w.chi w.ξ hv hG hQ uS uT g0 g h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · rw [hL] at hκ ⊢
    have h1 := law (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ) (lift_one_one _ _ _)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    have hne : Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t k hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) κ ≠ 0 := by
      unfold Lev.levChi; exact Units.ne_zero _
    exact (inv_smul_eq_iff₀ hne).1 h1
  · rw [hL'] at hκ ⊢
    have h1 := law (lift_one_one _ _ _) (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    exact h1

theorem levelLawQ : ∀ D : D7, LevelLawQ D := by
  intro D _ c w hw k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := vecLawQ D c w hw k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainTw.TwLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryKeepsBaseLatticeOfSplitComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_keeps_baseLattice_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  first | exact @GlobalTheory.SplitStab.stab_of_split_components | exact GlobalTheory.SplitStab.stab_of_split_components | (intros; apply GlobalTheory.SplitStab.stab_of_split_components <;> assumption)
end

