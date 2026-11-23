module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameAt
variable {D : D7}

theorem mem_congGrp (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have key : ∀ i j, (Ideal.Quotient.mk I) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  constructor
  · intro h i j
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one] at this
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key]
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key] at this
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
    exact this

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_mul (g h : GA D S) : Formalism.L2.Theta.mt S (g * h) = Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h1 := p.pr_sec (p.pr 1)
  rw [p.sec_pr, mul_one, map_one] at h1
  exact h1

theorem gl_map (β : Frame p S n) (g : GL n k) :
    (Formalism.L2.Theta.mt S (β.gl g)).map p.pr = β.b * g.val * β.b' := β.gl_mat g

theorem gl_inj (β : Frame p S n) : Function.Injective β.gl := by
  intro g g' h
  have h1 := congrArg (fun x => β.b' * (Formalism.L2.Theta.mt S x).map p.pr * β.b) h
  simp only [gl_map] at h1
  have e1 : ∀ x : Matrix n n k, β.b' * (β.b * x * β.b') * β.b = x := by
    intro x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, β.b'b, Matrix.one_mul, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e1, e1] at h1
  exact Units.ext h1

theorem det_at (β : Frame p S n) (g : GL n k) :
    ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  set a := (Formalism.L2.Theta.mt S (β.gl g)).det
  set c := (Formalism.L2.Theta.mt S (β.gl g⁻¹)).det
  have hee : p.e * p.e = p.e := p.split.1
  have hac : a * c = 1 := by
    simp only [a, c]
    rw [← Matrix.det_mul, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.det_one]
  refine ⟨⟨p.e * a + (1 - p.e), p.e * c + (1 - p.e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · simp only [Units.val_mk, map_add (f := _), map_mul, map_sub, map_one, pr_e p, one_mul, sub_self, add_zero]
    simp only [a]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, gl_map, Matrix.mul_assoc, Matrix.det_comm' β.bb' β.b'b, Matrix.mul_assoc, β.b'b,
      Matrix.mul_one]
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grpAt_iff (β : Frame p S n) (h : GA D S) : h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hL := (_root_.GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1
  unfold grpAt
  rw [mem_congGrp]
  constructor
  · intro hh
    have hsupp : SuppAt p.e S h := by
      intro i j
      rw [hsum]
      exact (hL _).1 (hh i j)
    let M := (Formalism.L2.Theta.mt S h).map p.pr
    let M' := (Formalism.L2.Theta.mt S h⁻¹).map p.pr
    have hMM : M * M' = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM'M : M' * M = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : ∀ X Y : Matrix (Fin S.rank) (Fin S.rank) k,
        β.b' * X * β.b * (β.b' * Y * β.b) = β.b' * (X * Y) * β.b := by
      intro X Y
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
    let g : GL n k := ⟨β.b' * M * β.b, β.b' * M' * β.b, by rw [e2, hMM, Matrix.mul_one, β.b'b],
      by rw [e2, hM'M, Matrix.mul_one, β.b'b]⟩
    refine ⟨g, _root_.GlobalTheory.UnitSplit.eq_of_split_part D S p.e h (β.gl g) p.split hsupp (β.gl_supp g) ?_⟩
    intro i j
    rw [← p.sec_pr, ← p.sec_pr]
    congr 1
    have := congrArg (fun X => X i j) (gl_map β g)
    simp only [Matrix.map_apply] at this
    rw [this]
    show M i j = (β.b * (β.b' * M * β.b) * β.b') i j
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨g, rfl⟩ i j
    rw [(hL _)]
    have := β.gl_supp g i j
    rw [hsum] at this
    exact this
end

theorem frame_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  intro D k _ _ _ _ p S n _ _ β
  refine ⟨mem_grpAt_iff β, gl_inj β, _root_.GlobalTheory.FrameCont.continuous_gl D k p S n β, _root_.GlobalTheory.FinPl.FrameLat.exists_lat D k p S n β, ?_, det_at β⟩
  intro L Λ hL hΛ
  first
  | exact _root_.GlobalTheory.FrameGlob.main D k p S n β L Λ hL hΛ
  | exact _root_.GlobalTheory.FrameGlob.main D k p S n β L Λ hL hΛ.toIsLattice

end GlobalTheory.FrameAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundWindowOfTermPairTypeBound
section
namespace GlobalTheory.Core.Deg

theorem vanishingGramBoundWindow_of_termPairTypeBound (hT : GlobalTheory.TypeAsm.TypeP) : VanishingGramTermsBoundWindow := by
  intro Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, H⟩ := hT Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨C₀, H2⟩ := H (Cp + 4) le_rfl
  obtain ⟨C'₀, Cl₀, H3⟩ := H2 (max C₀ (2 * (CH + 1))) (le_max_left _ _)
  obtain ⟨Cl₁, H4⟩ := _root_.GlobalTheory.Core.Deg.pairsDegOfType_holds CH Ch Cp (max C₀ (2 * (CH + 1))) hCH hCh hCp (le_max_right _ _)
  refine ⟨max C'₀ 1, max Cl₀ Cl₁, fun C' Cl hC' hCl D large₂ X Y _ _ u hTies _ h0 hC hAbs => ?_⟩
  have hK2 : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 :=
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 ((le_max_right _ _).trans hC')
  have hType := H3 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans hCl) D large₂ X Y u hTies hK2 hC
  have hPairs := H4 C' Cl Cg cb Cu cT CT C0 D large₂ X Y u ((le_max_right _ _).trans hCl) hK2 hC hType
  exact _root_.GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude C' Cl Cg cb Cu cT CT C0 D large₂ X Y u hK2 hC hAbs hPairs

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslatesStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  first | exact @GlobalTheory.InertFrameLoc.om_mem_span_uPt | exact GlobalTheory.InertFrameLoc.om_mem_span_uPt | (intros; apply GlobalTheory.InertFrameLoc.om_mem_span_uPt <;> assumption)
end
end

