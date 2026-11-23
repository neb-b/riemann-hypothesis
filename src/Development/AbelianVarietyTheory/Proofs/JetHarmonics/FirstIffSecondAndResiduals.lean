module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RepCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_actLat (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (v' : Fin n → E) :
    v' ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v' := by
  simp [UnitaryAdjointCongruence.actLat]






theorem mul_adj {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) : γ * UnitaryAdjointCongruence.adjM γ = 1 :=
  mul_eq_one_comm.1 h

theorem form_adj (γ : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * γ.mulVec w j =
      ∑ j, IsCMField.complexConj E ((UnitaryAdjointCongruence.adjM γ).mulVec v j) * w j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, UnitaryAdjointCongruence.adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (UnitaryAdjointCongruence.actLat γ Λ).Unimod := by
  intro v
  have e : v ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ (UnitaryAdjointCongruence.adjM γ).mulVec v ∈ Λ.La := by
    rw [mem_actLat]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    · intro hv
      exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, mul_adj h, Matrix.one_mulVec]⟩
  rw [e, hΛ]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := (mem_actLat _ _ _).1 hw
    rw [form_adj]
    exact hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ((mem_actLat _ _ _).2 ⟨w, hw, rfl⟩)

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Letters

variable (c : Coeff l) {n : ℕ}

theorem push_mem {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) :
    UnitaryAdjointCongruence.pushLet c γ P ∈ harmL c (UnitaryAdjointCongruence.actLat γ Λ) a := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  refine ⟨⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n γ P h h1, (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).1 h2,
    (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).2 h3⟩, ?_⟩
  have : symO (Dw := Dw) c Λ ≤ (symO c (UnitaryAdjointCongruence.actLat γ Λ)).comap (UnitaryAdjointCongruence.pushLet c γ).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      exact (algHom_C (UnitaryAdjointCongruence.pushLet c γ) (o : c.F)).symm
    · exact Subring.subset_closure (Or.inr ⟨σ, i, _, (mem_actLat _ _ _).2 ⟨b, hb, rfl⟩, UnitaryAdjointCongruence.pushLet_letB c γ σ i b⟩)
  exact this h4

end Letters

section Values

variable (Xo : Moduli Dw l) (c : Coeff l)

structure FrameLaws : Prop where
  cover : ChartCoverF Xo c
  test : AllTest Xo c
  bc : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

theorem frameLaws : FrameLaws Xo c :=
  have hB := GlobalTheory.allSixLaws.1.secBaseChange
  ⟨GlobalTheory.Frames.chartCoverF_of_secBaseChange hB E H Dw l Xo c, GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c,
    fun S T _ _ _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y⟩

instance (K : Type) [Field K] (p : TRing K) : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

variable {Xo c} {nab : NabV Xo c} {n : ℕ}

end Values

section Clauses

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ}




end Clauses

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

end Cover

section Main

variable [StarRing (𝓞 E)] (Dw) (n : ℕ)

variable {Dw n}

end Main

end GlobalTheory.RepCompare
