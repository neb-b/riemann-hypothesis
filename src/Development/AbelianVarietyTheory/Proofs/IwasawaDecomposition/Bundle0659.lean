module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanMarkedFormUniqueInCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem exists_starSubdivision : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := _root_.GlobalTheory.PolFan.StarKey.exists_starFun_strict E H q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := _root_.GlobalTheory.PolFan.starFun_linearOn E H q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell H.bar (starFun H.bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf H.bar q ψ w (starFun H.bar ψ w K D) := _root_.GlobalTheory.PolFan.StarCells.isStarOf_of_clauses E H q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun H.bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth H.bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun H.bar ψ w K D, _root_.GlobalTheory.PolFan.StarFan.isPolyFan_star E H q ψ w _ hψ hW hstar hint hpos,
    isTwInv_starFun H htψ (_root_.GlobalTheory.PolFan.isTwInv_starDepth E H ψ w htψ htw) K D, _root_.GlobalTheory.PolFan.subordinate_of_isStarOf _ H.bar q ψ w _ hstar, hstar⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClass
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTopDim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem relIdeal_isHomogeneous (H : Host E) (Dw : Datum H) :
    (relIdeal H Dw).IsHomogeneous
      (weightedHomogeneousSubmodule ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ)) := by
  apply Ideal.homogeneous_span
  rintro x ((⟨τ, rfl⟩ | ⟨τ, k, -, rfl⟩) | ⟨τ, k, -, rfl⟩)
  · refine ⟨0, ?_⟩
    refine sub_mem ?_ ?_
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_X ℝ Prod.snd (τ, 0)
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_one ℝ Prod.snd
  · refine ⟨k, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_X ℝ Prod.snd (τ, k)
  · refine ⟨k, Submodule.sum_mem _ fun a ha => ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    have ha' : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ (k - a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (conjEmb τ.1, k - a))
    convert h using 1
    simp only [zero_add]
    omega

theorem pointPoly_isWeightedHomogeneous (H : Host E) (Dw : Datum H) :
    IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  have h : ∀ τ ∈ (Finset.univ : Finset (GlobalTheory.AllWt.Psi H)), IsWeightedHomogeneous Prod.snd
      ((C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)) (Dw.p * Dw.q) := by
    intro τ _
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    have h1 := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ Dw.mult τ.1)).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, Dw.mult τ.1))).pow (Dw.p + Dw.q - Dw.mult τ.1)
    convert h1 using 1
    simp only [hm, zero_add, Nat.add_sub_cancel_left]
    ring
  have h2 := IsWeightedHomogeneous.prod Finset.univ _ _ h
  rw [pointPoly]
  convert h2 using 1
  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem mem_of_forall_dual {V : Type} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V) (v : V)
    (h : ∀ f : Module.Dual ℝ (V ⧸ S), f (S.mkQ v) = 0) : v ∈ S := by
  have := (Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ v)).1 h
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

theorem top_eq_smul_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
    IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) →
      ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  intro E _ _ _ H Dw Q hQ
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.GrassTop.span_point E H Dw Q
  set D := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with hD
  let N : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) := Submodule.span ℝ
    {f | ∃ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ D ∧ f = monomial d 1}
  let S := (relIdeal H Dw).restrictScalars ℝ ⊔ N
  have hS : Q - C β * pointPoly H Dw ∈ S := by
    apply mem_of_forall_dual
    intro f
    let Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ := f ∘ₗ S.mkQ
    have hker : ∀ x ∈ S, Θ x = 0 := fun x hx => by
      simp [Θ, (Submodule.Quotient.mk_eq_zero _).2 hx]
    have hrel : ∀ x ∈ relIdeal H Dw, Θ x = 0 := fun x hx =>
      hker x (Submodule.mem_sup_left (by simpa using hx))
    have hadm : GlobalTheory.Schubert.admitted H Dw Θ := by
      refine ⟨fun τ k hk P => hrel _ ?_, fun τ P => hrel _ ?_, fun τ k hk P => hrel _ ?_,
        fun d hd => hker _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩))⟩
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr ⟨τ, k, hk, rfl⟩))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl ⟨τ, rfl⟩)))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨τ, k, hk, rfl⟩)))
    show Θ (Q - C β * pointPoly H Dw) = 0
    rw [map_sub, hβ Θ hadm, C_mul', map_smul, smul_eq_mul, sub_self]
  obtain ⟨r, hr, n, hn, hrn⟩ := Submodule.mem_sup.1 hS
  have hn0 : ∀ n ∈ N, weightedHomogeneousComponent Prod.snd D n = 0 := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine weightedHomogeneousComponent_eq_zero' _ _ fun d' hd' => ?_
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hd'
      subst hd'
      rw [Finsupp.weight_apply]
      intro h
      apply hd
      rw [← h]
      exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hhom : IsWeightedHomogeneous Prod.snd (Q - C β * pointPoly H Dw) D := by
    have h1 : Q ∈ weightedHomogeneousSubmodule ℝ Prod.snd D := (mem_weightedHomogeneousSubmodule _ _ _ _).2 hQ
    have h2 : pointPoly H Dw ∈ weightedHomogeneousSubmodule ℝ Prod.snd D :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).2 (pointPoly_isWeightedHomogeneous H Dw)
    rw [← mem_weightedHomogeneousSubmodule, C_mul']
    exact sub_mem h1 (Submodule.smul_mem _ β h2)
  refine ⟨β, ?_⟩
  rw [← hhom.weightedHomogeneousComponent_same, ← hrn, map_add (f := _), hn0 n hn, add_zero]
  exact weightedHomogeneousComponent_mem_of_mem ℝ Prod.snd (relIdeal_isHomogeneous H Dw) (by simpa using hr) D

end GlobalTheory.GrassTopDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem orbMark_coord_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    _root_.GlobalTheory.PolFan.OrbMark.exists_pieces_match E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := _root_.GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq H.bar (δ j) (h.mem j) (hprim j)
    have hd1 := (_root_.GlobalTheory.PrimRay.eq_of_toReal_eq_smul (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem exists_markFun {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) :
    ∃ w : InvFun O, ∀ n B, w.toFun n B = markVal bar ψ lab i n B := by
  classical
  refine ⟨{ toFun := markVal bar ψ lab i, inv := ?_, zero := ?_ }, fun _ _ => rfl⟩
  · intro n m r hr B
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    unfold markVal
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, fun a b => h.choose_spec _ _⟩
      rw [dite_eq_left h, dite_eq_left h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec a b
        have h2 := h.choose_spec (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ r s hrs]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h3⟩
        exact h ⟨pull s β, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dite_eq_right h, dite_eq_right h']
  · intro B
    unfold markVal
    split_ifs with h h2
    · exfalso
      have := h2.2.2.2.1
      rw [InvFun.evalZ, lab.eval_of_subsingleton] at this
      exact absurd this (by positivity)
    · rfl
    · rfl


open Classical in
theorem evalZ_markFun {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ} {w : InvFun O}
    (hw : ∀ n B, w.toFun n B = markVal bar ψ lab i n B) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (β : LinearMap.BilinForm ℤ X) :
    w.evalZ β = if IsMarked bar ψ lab i X β then 1 else 0 := by
  classical
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' O X
  obtain ⟨u, hu⟩ := Module.projective_lifting_property t LinearMap.id ht
  have htu : ∀ a, t (u a) = a := fun a => LinearMap.congr_fun hu a
  rw [InvFun.evalZ, w.eval_eq ht, hw]
  have e := markVal_int (bar := bar) (ψ := ψ) (lab := lab) (i := i) n (pull t β)
  simp only [pull_apply] at e
  rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ t u htu]

theorem exists_markFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro E _ _ _ H q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := exists_markFun H.bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X) => evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → IsMarked H.bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact _root_.GlobalTheory.PolFan.Mark.markVal_twist E H ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      _root_.GlobalTheory.PolFan.Mark.eq_of_isMarked_of_inRCone E H q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.polFan_exists_marked_form_in_cell E H q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStOneOfInt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeUniformisationEqModelStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClass_density_hodge_uniformisation_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : (U.X k).Ψ => Dw.p) (∏ τ : (U.X k).Ψ, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p)) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v := by
  first | exact @GlobalTheory.UnifDensTransport.chernTop_pointPoly_transport | exact GlobalTheory.UnifDensTransport.chernTop_pointPoly_transport | (intros; apply GlobalTheory.UnifDensTransport.chernTop_pointPoly_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChange
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open Filter Topology GlobalTheory.GoodMetric
open scoped ComplexOrder


set_option maxHeartbeats 800000 in
theorem GlobalTheory.UnifDens.chernTop_unif_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv ch hch A hA
  have hholo := _root_.GlobalTheory.UnifHolo.unif_continuousOn_analyticAt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hM := _root_.GlobalTheory.LieBase.isMetricOn_lieGram E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hL
  have hyO : ψ (GlobalTheory.UnifDens.flatL h v) ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
    rw [← _root_.GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ]
    exact ⟨_, hv, rfl⟩
  set y := ψ (GlobalTheory.UnifDens.flatL h v) with hydef
  let K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))
  have hφ : AnalyticAt ℂ φ v :=
    (hholo.2 _ hv ch hch).comp (show AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v from (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v)
  have hy'' : ch.e.symm (ch.e y) = y := ch.e.left_inv hch
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v) := by
    intro τ a b
    have hsm := hM.smooth y hyO A hA τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.2
    have hn : ∀ {g : CxPts X.str (σ.comp e.toRingHom) → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt g z) →
        ContDiffAt ℝ 2 (g ∘ ch.e.symm) (ch.e y) := by
      intro g hg
      have hs : ch.e.target ∩ ch.e.symm ⁻¹' {z | CInfAt g z} ∈ 𝓝 (ch.e y) := by
        refine Filter.inter_mem (ch.e.open_target.mem_nhds (ch.e.map_source hch)) ?_
        exact (ch.e.continuousAt_symm (ch.e.map_source hch)).preimage_mem_nhds (hy''.symm ▸ hg)
      exact ((contDiffOn_chart (fun z hz => hz) ch).contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (φ v) τ).det := by
    intro τ
    have hp := hM.posDef y hyO A hA τ
    show IsUnit (lieGram e U hj f₀ A₀ A (ch.e.symm (ch.e y)) τ).det
    rw [hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp (pointPoly H Dw) K φ v hφ hK2 hKu
  have hcont : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hholo.1.continuousAt (GlobalTheory.PoincareLower.isOpen_domFlat.mem_nhds hv)).comp
      (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  have hg : (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) =ᶠ[𝓝 v] fun w => K (φ w) := by
    filter_upwards [hcont.preimage_mem_nhds (ch.e.open_source.mem_nhds hch)] with w hw
    simp only [K, φ, ch.e.left_inv hw]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr _ hg, key]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOverStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.served_place_no_chain_place_or_type_prime_over : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  first | exact @GlobalTheory.ServedPlace.places_prime | exact GlobalTheory.ServedPlace.places_prime | (intros; apply GlobalTheory.ServedPlace.places_prime <;> assumption)
end

