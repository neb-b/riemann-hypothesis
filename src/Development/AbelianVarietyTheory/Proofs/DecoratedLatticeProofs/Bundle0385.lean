module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitUpStd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul' (q : GlobalTheory.FinPl.SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

set_option maxHeartbeats 800000 in
theorem int_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  intro D k _ _ _ _ q S T a₀ ha₀ _ FS FT hβ _ hγ t ht
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]

  let G : Fin T.rank → Fin S.rank → WO S T := fun i l =>
    Matrix.of fun i' j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)
  have hsingle : ∀ (n : ℕ) (l : Fin n), (Pi.single l (1 : D.host.E) : Fin n → D.host.E) ∈ intVecSub D n := by
    intro n l m
    by_cases hm : m = l
    · subst hm; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hm]; exact isIntegral_zero
  have hG : ∀ i l, G i l ∈ stdHom S T := fun i l =>
    Formalism.IndefR.Fin.gen_mem S T (intVecSub D S.rank) (intVecSub D T.rank) hα ha₀ (hsingle _ l) (hsingle _ i)
  have htm : ∀ (x : k) (y : D.host.E), q.sec x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) = q.sec (x * q.pr (incA D y)) := by
    intro x y
    have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] y = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D y := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h2 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    rw [e1, ← mul_assoc, ← h2, mul_assoc q.e, mul_comm (q.sec x), ← mul_assoc q.e, hee, h2, sec_mul']
  have hrow : ∀ (l : Fin S.rank) j,
      ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j = S.gram l j := by
    intro l j
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, star_one, one_mul]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hGapp : ∀ i l i' j, (q.sec (t i l) • G i l) i' j = q.sec (t i l) * (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)) := fun _ _ _ _ => rfl
  have key : (Place.ofSplitPt q).up FS FT t = ∑ i, ∑ l, q.sec (t i l) • G i l := by
    ext i' j
    change q.sec ((FT.β * t * FS.γ) i' j) = _
    rw [hβ, hγ, Matrix.one_mul, Matrix.sum_apply, Finset.sum_eq_single i']
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [Matrix.sum_apply, Matrix.mul_apply, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hGapp, htm, hrow, Pi.single_eq_same, mul_one, map_mul (incA D), map_mul q.pr, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro i _ hi
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hGapp, Pi.single_eq_of_ne (Ne.symm hi), mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [key]
  refine sum_mem fun i _ => sum_mem fun l _ => ?_
  exact Formalism.IndefR.Fin.latO_smul_mem S T (intVecSub D S.rank) (intVecSub D T.rank) ((q.int_iff _).1 (ht i l)) (hG i l)

end GlobalTheory.SplitUpStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.DiffDual

variable {D : D7}

def TrInt (D : D7) (x : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (x * o) = n

theorem mem_dI_iff (x : D.host.E) : x ∈ dI D ↔ TrInt D x := by
  rw [dI, Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) _ _ _)]
  constructor
  · intro h o
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    rw [← hn]; simp
  · intro h b hb
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨n, hn⟩ := h o
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, hn]; simp

theorem TrInt.mul {x : D.host.E} (h : TrInt D x) (o : 𝓞 D.host.E) : TrInt D (x * o) := fun o' => by
  obtain ⟨n, hn⟩ := h (o * o')
  exact ⟨n, by rw [mul_assoc]; simpa using hn⟩

theorem trInt_coe (o : 𝓞 D.host.E) : TrInt D (o : D.host.E) := fun o' => by
  have hi : IsIntegral ℤ ((o : D.host.E) * o') := o.isIntegral_coe.mul o'.isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
  exact ⟨n, hn.symm⟩

theorem chi_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F}
    (hβ : β ∈ intAf D.host.F) {x : D.host.E} (hx : TrInt D x) : Conductor.chi ψ (β ⊗ₜ[D.host.F] x) = 1 := by
  rw [Conductor.chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hβ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := hx ⟨_, hi⟩
  exact ⟨n, by rw [Algebra.smul_def, mul_comm]; exact hn⟩

theorem chi_mul_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {x : D.host.E} (hx : TrInt D x)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Conductor.chi ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact chi_tmul hψ hβ (hx.mul o)
  | zero => rw [mul_zero]; exact Conductor.chi_zero ψ
  | add y y' _ _ hy hy' => rw [mul_add, Conductor.chi_add, hy, hy', one_mul]
  | neg y _ hy =>
    have := Conductor.chi_add ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * y) (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * -y)
    rwa [← mul_add, add_neg_cancel, mul_zero, Conductor.chi_zero, hy, one_mul, eq_comm] at this

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  rw [psiE, psiE, psiE, map_add (f := _), ψ.map_add_eq_mul]

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  rw [psiE, map_zero, ψ.map_zero_eq_one]

theorem psiE_neg (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) : psiE ψ (-a) = (psiE ψ a)⁻¹ := by
  rw [psiE, psiE, map_neg, ψ.map_neg_eq_inv]

theorem forward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idV (dI D) v) : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  induction hs using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
    intro o ho
    have hinf : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a * o) = 0 := by
      rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_pair, zero_mul]
    rw [Conductor.psiE_eq_chi ψ hinf, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair]
    have e : α ⊗ₜ[D.host.F] a = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * (α ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e, mul_assoc]
    exact chi_mul_int hψ ((mem_dI_iff a).1 ha) (Conductor.mul_mem_int (Conductor.tmul_mem hα 1) ho.2)
  | zero => intro o _; rw [zero_mul, psiE_zero]
  | add x y _ _ hx hy => intro o ho; rw [add_mul, psiE_add, hx o ho, hy o ho, one_mul]
  | neg x _ hx => intro o ho; rw [neg_mul, psiE_neg, hx o ho, inv_one]

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem lift_tmul (α : Af D.host.F) (x : D.host.E) : lift D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem finPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (lift D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.finPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem infPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (lift D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.infPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem eq_lift {s : AE D} (h : infPart D s = 0) : s = lift D (finPart D s) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h, infPart_lift, sub_zero]
  · rw [RingHom.map_sub, finPart_lift, sub_self]

theorem lift_int_mem (v : Pl D) (hε : singleV D.host.F v 1 ∈ intAf D.host.F) {u : Af D.host.F ⊗[D.host.F] D.host.E}
    (hu : u ∈ intAE D) : lift D ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u) ∈ idV (dI D) v := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, o, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf hε hβ, fun w hw => ?_, (o : D.host.E),
      (mem_dI_iff _).2 (trInt_coe o), lift_tmul _ _⟩
    rw [map_mul, Conductor.ev_ne hw, zero_mul]
  | zero => rw [mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg, map_neg]; exact neg_mem hx

theorem backward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idAt D (· = v)) (h : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) : s ∈ idV (dI D) v := by
  have hs1 : infPart D s = 0 := hs.1
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    rw [RingHom.map_mul, hs1, zero_mul]
  have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
    Conductor.idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
  obtain ⟨x, u, hu, e⟩ := Conductor.approx (finPart D s)
  have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
    have := Conductor.idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hx : TrInt D x := fun o => by
    have h1 := h _ (Conductor.lift_mem v o)
    have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
        (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Conductor.psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc,
      mul_comm (finPart D s), hz, e, add_mul, Conductor.chi_add,
      Conductor.chi_int hψ (Conductor.mul_mem_int hu (Conductor.tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
    exact (Conductor.chi_rat hψ _).1 h1
  have hfin : finPart D s = singleV D.host.F v 1 ⊗ₜ[D.host.F] x +
      (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u := by
    rw [← hz, e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [eq_lift hs1, hfin, map_add (f := _)]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hε, fun w hw => Conductor.ev_ne hw, x, (mem_dI_iff x).2 hx,
    lift_tmul _ _⟩) (lift_int_mem v hε hu)

theorem idV_dI_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D),
    ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 :=
  fun _ _ hψ v _ hs => ⟨fun h => forward hψ v h, backward hψ v hs⟩

end GlobalTheory.SeeSaw.DiffDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopLocData

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

def reN {N N' : ℕ} (h : N = N') (F : Frame k N Y) : Frame k N' Y := h ▸ F

theorem exists_o {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁ : SB (Matrix Y Y' k), IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hT a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hT

def mkPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hu : q.UnitAA)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : SB (Matrix Y Y' k)) (e : WO S T →₀ ℂ)
    (he : (ofSplit q).IsCombAt ψ FS FT e Φ.1) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') : LocPl ψ S T M M' :=
  ⟨k, q, hu, Y, Y', FS, FT, Φ, e, he, Classical.choose (exists_o hψ q FS FT hS hT),
    (Classical.choose_spec (exists_o hψ q FS FT hS hT)).1, (Classical.choose_spec (exists_o hψ q FS FT hS hT)).2⟩

end Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {v : VCom f.c}

theorem isCombAt_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k)
    (ψ : AddChar (AF D.host.F) ℂ) (FT : Frame k D.sp.X'.rank Y) (Ξ : Matrix Y Y' k → ℂ) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y') (e : WO (Yc D (s + 1)) D.sp.X' →₀ ℂ)
      (e' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), HEq e' e → (ofSplit q).IsCombAt ψ F FT e Ξ →
      (ofSplit q).IsCombAt ψ (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) FT e' Ξ := by
  rintro s j rfl F e e' he h
  cases he
  exact h

theorem intIn_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y' : Type} [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y'), IntIn q (Yc D (s + 1)) F (N (s + 1)) →
      IntIn q (Yc D (j + 1)) (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) (N (j + 1)) := by
  rintro s j rfl F h
  exact h

end GlobalTheory.TopLocData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FlatComm

variable {D : D7}

theorem besselAnisotropicEmbedding_fixes_basePoint {σ : ℕ} (B : BesLev D σ) (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ x0 B = x0 B := by
  have h1 : mt B.V (embA B.d B.o h) ⬝ B.d.jX = B.d.jX := B.d.wittDecomp_anisotropicEmbedding_inclX _
  have h2 : mt B.V (embA B.d B.o h) *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) := by
    have e1 : mt B.V (embA B.d B.o h) ⬝ B.d.j0 = B.d.j0 ⬝ mt B.V₀ (B.o.emb (h, 1)) := B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
    have e2 := B.o.emb_jB h 1
    rw [mt_one, Matrix.mul_one] at e2
    rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, Matrix.mul_assoc]
    exact congrArg (fun M => (B.d.j0 ⬝ M) *ᵥ ratV B.ζ) e2
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun h2 k
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · have := congrFun (congrFun h1 k) i
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_castSucc]
    exact this

theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have hv : Continuous (fun u : UX D ρ => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hs : Continuous fun u : UX D ρ => upSum u.1.1 := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact hv.matrix_elem i j
    · exact continuous_const
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp (ht.comp hs)

theorem sFinite_of_haar {G : Type} [MeasurableSpace G] [Group G] [TopologicalSpace G] (hl : LocallyCompactSpace G)
    (hs : SecondCountableTopology G) (μ : Measure G) (hμ : μ.IsHaarMeasure) : SFinite μ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  exact instSFiniteOfSigmaFinite


set_option maxHeartbeats 600000 in
theorem flatFB_om : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀) (h : GA D B.A), flatFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flatFB s Ψ) := by
  intro D hD ψ σ J B s Ψ hΨ g h
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D (σ + 1)
  haveI : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := sFinite_of_haar k1 k2 _ s.vU.unit.1
  have hstd := s.weil.std
  set p : GA D J.W × GA D B.V := (J.d.emb0 g, embA B.d B.o h) with hp
  let F : (WO J.W B.V → ℂ) → UX D (σ + 1) → WO J.W₀ B.V₀ → ℂ := fun Φ u w =>
    flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) 0 Φ w u
  have hF : ∀ Φ u, F Φ u = star (psiUni ψ u.1) •
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (x0 B ⬝ u.1.1) 0 := fun Φ u => by
    rw [← hx0]; rfl
  have hflat : ∀ Φ, flatFB s Φ = fun w => ∫ u, F Φ u w ∂s.vU.ν := fun Φ => by
    simp only [F, hx0]; rfl
  have key : ∀ u, s.om₀ (g, B.o.emb (h, 1)) (F Ψ u) = F (s.om p Ψ) u := fun u => by
    have e := GlobalTheory.Unf.FB.evalAt_zero_equivariant D hD ψ σ J B s Ψ hΨ g 1 (one_mem _) h (x0 B ⬝ u.1.1)
    rw [one_mul, ← map_inv, ← Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
    rw [hF, hF, map_smul, ← e]
  have hv : Continuous (fun u : UX D (σ + 1) => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hc : ∀ q, Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => F (s.om q Ψ) r.1 r.2 := fun q => by
    have c := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2
    have c2 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ =>
        (q, (rat x : Mx D B.V.rank (σ + 1)) ⬝ r.1.1.1, (0 : Mx D J.W₀.rank σ), r.2) :=
      continuous_const.prodMk ((continuous_const.matrix_mul (hv.comp continuous_fst)).prodMk
        (continuous_const.prodMk continuous_snd))
    have c3 := c.comp c2
    have c4 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => star (psiUni ψ r.1.1) :=
      ((continuous_psiUni hstd.1.1 _).comp continuous_fst).star
    have c5 := c4.mul c3
    simp only [Function.comp_def] at c5
    exact c5
  have h1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  obtain ⟨M, hM, hb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil s.vU x hx.1 Ψ hΨ
    {1, p} (Set.toFinite _).isCompact
  have hth : ∀ u, IsThetaFunO ψ J.W₀ B.V₀ (F Ψ u) := fun u => by
    obtain ⟨mS, mT⟩ := GlobalTheory.MixValues.mixed_values D ψ hstd
    rw [hF]
    exact GlobalTheory.OrientedHeis.theta_smul _ (mT _ _ _ _ B.d _ _ s.vT.covol _ (mS _ _ _ _ J.d _ _ s.vS.covol _ hΨ _) _)
  have main := GlobalTheory.CommInt.om_integral_comm D ψ J.W₀ B.V₀ _ _ s.om₀ s.weil₀ (UX D (σ + 1)) s.vU.ν (F Ψ) (g, B.o.emb (h, 1)) M hth
    (by have := hc 1; rwa [h1] at this) (by simp only [key]; exact hc p) hM
    (fun u w => ⟨by have := hb 1 (by simp) 0 w u; rwa [h1] at this, by rw [key]; exact hb p (by simp) 0 w u⟩)
    (GlobalTheory.Unf.Flat.flatLaw D ψ hstd J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT s.vU x hx.1 0 Ψ hΨ).2
  rw [hflat, hflat]
  funext w
  rw [main w]
  simp only [key]

end GlobalTheory.Unf.FlatComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | exact GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep <;> assumption)
end

