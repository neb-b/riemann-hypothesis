module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

theorem isLocallyNoetherian_of_proj {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) : IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k (X := X)) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

theorem isProjOver_red {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) (Z : Closeds X) :
    letI := algebraΓAlong k (redι Z)
    IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
  letI := algebraΓAlong k (redι Z)
  rw [← comp_strHom (g := redι Z) fun _ => rfl]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp

theorem dim_closure_add_one_le {T : Type*} [TopologicalSpace T] [QuasiSober T] {x y : T}
    (hyx : y ⤳ x) {U : Set T} (hU : IsOpen U) (hy : y ∈ U) (hx : x ∉ U) :
    topologicalKrullDim (closure ({x} : Set T)) + 1 ≤ topologicalKrullDim (closure ({y} : Set T)) := by
  refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz => ⟨y, subset_closure rfl, fun h => ?_, hyx.trans (specializes_iff_mem_closure.2 hz)⟩
  exact hx ((specializes_iff_mem_closure.2 h).mem_open hU hy)

theorem withBot_le_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | (apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le ..)

theorem withBot_lt_of_add_one_lt {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 < ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | (apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ ..)

def sumOptionEquiv (e r : ℕ) : Fin e ⊕ Option (Fin r) ≃ Option (Fin e ⊕ Fin r) where
  toFun
    | .inl i => some (.inl i)
    | .inr none => none
    | .inr (some b) => some (.inr b)
  invFun
    | none => .inr none
    | some (.inl i) => .inl i
    | some (.inr b) => .inr (some b)
  left_inv := by rintro (i | _ | b) <;> rfl
  right_inv := by rintro (_ | i | b) <;> rfl

def frontEquiv (e r : ℕ) : Fin e ⊕ Fin (r + 1) ≃ Fin (e + r + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) (finSuccEquiv r)).trans (sumOptionEquiv e r)).trans
    ((Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv (e + r)).symm)

theorem cons_comp_frontEquiv {X : Scheme.{0}} {e r : ℕ} (P : Fin e → LB X) (B : Fin (r + 1) → LB X) :
    (Fin.cons (B 0) (Sum.elim P (fun a => B a.succ) ∘ finSumFinEquiv.symm) : Fin (e + r + 1) → LB X) ∘
      frontEquiv e r = Sum.elim P B := by
  funext x
  rcases x with i | a
  · simp [frontEquiv, sumOptionEquiv]
  · refine Fin.cases ?_ (fun b => ?_) a
    · simp [frontEquiv, sumOptionEquiv]
    · simp [frontEquiv, sumOptionEquiv]

end GlobalTheory.PullVanish

namespace GlobalTheory.PullVanish

theorem redι_genericPoint {X : Scheme.{0}} (w : X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal (⟨closure {w}, isClosed_closure⟩ : Closeds X)).subscheme] :
    redι (⟨closure {w}, isClosed_closure⟩ : Closeds X) (genericPoint _) = w := by
  set ι := redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have hr := range_redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have h₁ : w ⤳ ι (genericPoint _) :=
    specializes_iff_mem_closure.2 (by
      have : ι (genericPoint _) ∈ Set.range ι := ⟨_, rfl⟩
      rw [hr] at this; exact this)
  obtain ⟨y, hy⟩ : w ∈ Set.range ι := by rw [hr]; exact subset_closure rfl
  have h₂ : ι (genericPoint _) ⤳ w := by
    have := (genericPoint_specializes y).map ι.continuous
    rwa [hy] at this
  exact (h₁.antisymm h₂).eq.symm

theorem interNum_pull_eq_zero : ∀ (κ : Type) [Field κ] (e r : ℕ) (Z W : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z ≤ (e + r : ℕ) → ∀ g : Z ⟶ W, topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) < (r : ℕ) → ∀ (P : Fin e → LB Z), (∀ i, (P i).IsLB) → ∀ (A : Fin r → LB W), (∀ i, (A i).IsLB) → interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) = 0 := by
  intro κ _ e r
  induction r with
  | zero =>
    intro Z W _ _ _ _ g hg
    exfalso
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) := by
      haveI : Nonempty (IrreducibleCloseds (closure ({g (genericPoint Z)} : Set W))) :=
        ⟨⟨closure {⟨g (genericPoint Z), subset_closure rfl⟩}, isIrreducible_singleton.closure,
          isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    rw [Nat.cast_zero] at hg
    exact absurd hg (not_lt.2 h0)
  | succ r ih =>
    intro Z W _ _ hp hd g hg P hP A hA
    have := isLocallyNoetherian_of_proj hp
    obtain ⟨i₀, hi₀⟩ : ∃ i, g (genericPoint Z) ∈ (A 0).U i := by
      have : g (genericPoint Z) ∈ (⨆ i, (A 0).U i : W.Opens) := by
        rw [(hA 0).cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    set M : LB Z := (A 0).pull g with hMdef
    have hM : M.IsLB := pull_isLB (hA 0) g
    let j₀ : M.ι := fun _ => i₀
    have hmem : ∀ x : Z, x ∈ M.U j₀ ↔ g x ∈ (A 0).U i₀ := fun x =>
      ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
    have hη : genericPoint Z ∈ M.U j₀ := (hmem _).2 hi₀
    have hs := isRatSec_frameRat hM j₀ hη
    set Q : Fin (e + r) → LB Z := Sum.elim P (fun a : Fin r => (A a.succ).pull g) ∘ finSumFinEquiv.symm with hQdef
    have hQ' : ∀ x, (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).IsLB := by
      rintro (i | a)
      · exact hP i
      · exact pull_isLB (hA _) g
    have hQ : ∀ i, (Q i).IsLB := fun i => hQ' _
    have key : interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) =
        interNum κ (structureModule Z) (Fin.cons M Q : Fin (e + r + 1) → LB Z) := by
      rw [← interNum_comp_equiv κ _ (isLB_cons hM hQ) (frontEquiv e r)]
      exact congrArg _ (cons_comp_frontEquiv P (fun a => (A a).pull g)).symm
    rw [key, GlobalTheory.T.rational_section_cycle_formula_projective κ Z hp (e + r) hd M hM Q hQ _ hs]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : (divOfRatSec hM hs).mult w = 0
    · rw [hw, zero_mul]
    have hwU : w ∉ M.U j₀ := fun h => hw (by
      rw [((presents_divOfRatSec hM hs).isEqn j₀ w h).mult_eq, frameRat_self hM j₀ hη, Units.val_one]
      exact (unitAt_one w).ord_eq_zero)
    suffices h : interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds Z) Q = 0 by rw [h, mul_zero]
    set C : Closeds Z := ⟨closure {w}, isClosed_closure⟩ with hC
    haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
      isIntegral_red isIrreducible_singleton.closure
    letI := algebraΓAlong κ (redι C)
    have hιw : redι C (genericPoint _) = w := redι_genericPoint w
    rw [interNumRed_def, interNumSub_def,
      interNumOn_eq_interNum_pull (k := κ) (f := redι C) (fun _ => rfl) hQ]
    have e1 : interNum κ (structureModule _) (fun i => (Q i).pull (redι C)) =
        interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) :=
      by
        set_option maxHeartbeats 12000000 in
          exact interNum_comp_equiv κ _ (fun x => pull_isLB (hQ' x) (redι C)) finSumFinEquiv.symm
    have e2 : interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) =
        interNum κ (structureModule _)
          (Sum.elim (fun i => (P i).pull (redι C)) fun a : Fin r => (A a.succ).pull (redι C ≫ g)) := by
      refine interNum_congr_cls κ _ (fun x => pull_isLB (hQ' x) (redι C)) ?_ ?_
      · rintro (i | a)
        · exact pull_isLB (hP i) _
        · exact pull_isLB (hA _) _
      · rintro (i | a)
        · rfl
        · simp only [Sum.elim_inr]
          rw [CechPic.cls_pull (pull_isLB (hA _) g), CechPic.cls_pull (hA _) g,
            CechPic.cls_pull (hA _) (redι C ≫ g), CechPic.pull_comp]
    rw [e1, e2]
    refine ih _ W (isProjOver_red hp C) ?_ (redι C ≫ g) ?_ _ (fun i => pull_isLB (hP i) _) _
      (fun a => hA _)
    · rw [topologicalKrullDim_red]
      have h1 := dim_closure_add_one_le (genericPoint_specializes w) (M.U j₀).isOpen hη hwU
      have h2 : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = topologicalKrullDim Z := by
        rw [(genericPoint_spec Z).def]
        exact (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
      exact withBot_le_of_add_one_le (h1.trans (h2.trans_le hd))
    · rw [Scheme.Hom.comp_apply, hιw]
      have h1 := dim_closure_add_one_le ((genericPoint_specializes w).map g.continuous)
        ((A 0).U i₀).isOpen hi₀ (fun h => hwU ((hmem w).2 h))
      exact withBot_lt_of_add_one_lt (lt_of_le_of_lt h1 hg)

end GlobalTheory.PullVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntries
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.PowersCompact

theorem ball_isCompact_isOpen {E : Type} [Field E] [NumberField E] (w : Pl E) (m : ℤ) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} ∧
      IsOpen {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact WithZero.exp_ne_zero hc.symm
  have hO : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    Valued.isOpen_valuationSubring _
  have hC : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have e : {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} =
      (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc0)) ⁻¹' (w.adicCompletionIntegers E) := by
    ext x
    change _ ↔ Valued.v (c⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hc, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    exact Iff.rfl
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 hC, (Homeomorph.isOpen_preimage _).2 hO⟩

theorem exists_le_exp {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    ∃ m : ℤ, Valued.v x ≤ WithZero.exp m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).ge⟩

theorem isCompact_closure_zpowers_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (hH : IsClosed (H : Set (GLw n w))) (s : H) :
    IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j,
      Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp m := by
  let B : ℤ → Set (w.adicCompletion E) := fun m => {x | Valued.v x ≤ WithZero.exp m}
  constructor
  · intro hK
    have key : ∀ p : Fin n × Fin n, ∃ m : ℤ, ∀ u ∈ closure (Subgroup.zpowers s : Set H),
        Valued.v (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) ≤
          WithZero.exp m := by
      intro p
      have hc : Continuous fun u : H =>
          (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_elem p.1 p.2
      obtain ⟨m, hm⟩ := (hK.image hc).elim_directed_cover B
        (fun m => (ball_isCompact_isOpen w m).2)
        (by
          intro x _
          obtain ⟨m, hm⟩ := exists_le_exp w x
          exact Set.mem_iUnion.2 ⟨m, hm⟩)
        (by
          intro a b
          refine ⟨max a b, ?_, ?_⟩ <;> intro x hx <;>
            exact le_trans hx (WithZero.exp_le_exp.2 (by omega)))
      exact ⟨m, fun u hu => hm ⟨u, hu, rfl⟩⟩
    choose m hm using key
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    refine ⟨M, fun k i j => ?_⟩
    have h1 := hm (i, j) (s ^ k) (subset_closure (Subgroup.zpow_mem_zpowers s k))
    exact le_trans h1 (WithZero.exp_le_exp.2 (hM ⟨(i, j), rfl⟩))
  · rintro ⟨m, hm⟩
    let Bm : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := {A | ∀ i j, A i j ∈ B m}
    have hBm : IsCompact Bm := by
      have : Bm = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => B m)) := by
        ext A
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (ball_isCompact_isOpen w m).1
    let f : H → Matrix (Fin n) (Fin n) (w.adicCompletion E) ×
        (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ :=
      Units.embedProduct _ ∘ Subtype.val
    have hf : Topology.IsClosedEmbedding f :=
      Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
    let K := Bm ×ˢ (MulOpposite.op '' Bm)
    have hKc : IsCompact K := hBm.prod (hBm.image MulOpposite.continuous_op)
    have hC : IsCompact (f ⁻¹' K) := hf.isCompact_preimage hKc
    have hsub : (Subgroup.zpowers s : Set H) ⊆ f ⁻¹' K := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨fun i j => hm k i j, ⟨(((s ^ k : H) : GLw n w)⁻¹ : GLw n w), fun i j => ?_, rfl⟩⟩
      have h2 := hm (-k) i j
      rw [_root_.zpow_neg] at h2
      change Valued.v (_ : w.adicCompletion E) ≤ WithZero.exp m
      simpa using h2
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.PowersCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacAtOfReads
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add (f := _), conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      ext i j
      have h1 := congrFun (congrFun hw' i) j
      have h2 := congrFun (congrFun ((WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply, map_add, h1, h2, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorProof

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

def WeilUnique (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f

def WeilChange (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT νS νT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 →
    ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h)

variable {D : D7}

theorem isHeckeChar_mul_inv {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem isDetRoot_one (V : HSp D) : IsDetRoot V 1 1 := by
  unfold IsDetRoot
  rw [map_one, Units.val_one, Units.val_one, Matrix.det_one, map_one, one_mul]

theorem weil_ratio (hU : WeilUnique D) (hC : WeilChange D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (ho : IsWeilDatumO ψ S T χS χT om) (ho' : IsWeilDatumO ψ S T χS' χT' om') {g : GA D S} {h : GA D T}
    {x y : (AE D)ˣ} (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = ((((χT' x * (χT x)⁻¹)⁻¹ * (χS' y * (χS y)⁻¹) : Circle) : ℂ)) • om (g, h) f := by
  obtain ⟨o, h1, h2⟩ := hC ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (isHeckeChar_mul_inv ho'.hecS ho.hecS) (isHeckeChar_mul_inv ho'.hecT ho.hecT)
    (resEta_parity (resEta_mul ho'.resS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul ho'.resT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  rw [hU ψ ho.std S T χS' χT' om' o ho' h1 _ f hf, h2 g h x y hx hy]
  rfl

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  have := hn p hp
  simp [nrm2] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem frame_ratio (hU : WeilUnique D) (hC : WeilChange D) (hω : R.thP_ωP) (i : Fin D.R.m) (t t' : T0)
    {h : GA D (Wc D i)} {x : (AE D)ˣ} (hx : IsDetRoot (Wc D i) h x) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) :
    ((R.xi t x : Circle) : ℂ) • R.ωP i t' (1, h) f = ((R.xi t' x : Circle) : ℂ) • R.ωP i t (1, h) f := by
  rw [weil_ratio hU hC (hω i t) (hω i t') (isDetRoot_one _) hx hf, smul_smul, ← Circle.coe_mul]
  congr 2
  show R.xi t x * (_ * (R.mu0 _ x * R.xi t' x * (R.mu0 _ x * R.xi t x)⁻¹)) = _
  rw [map_one, map_one, mul_inv_cancel, inv_one, one_mul, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
    mul_comm (R.xi t' x), mul_inv_cancel_left]

end GlobalTheory.TwistFactorProof

end
end

