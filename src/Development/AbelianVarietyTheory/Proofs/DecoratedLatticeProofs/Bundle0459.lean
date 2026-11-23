module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LastRow

theorem row_lt_of_smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M : Matrix (Fin n) (Fin n) k) (hb : b * b' = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hfix : g • Q = Q) (s : Fin n) :
    valuation k (M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, Q.fn x ≠ 0 := by
    by_contra h
    exact Q.fn_ne (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨y0, -, s0, hs0, ha0⟩ := (hQ x0.1 (Q.fn x0)).1 ⟨x0.2, rfl⟩
  have hu : residue 𝒪[k] s0 ≠ 0 := by
    intro h
    apply hx0
    rw [ha0, map_mul, h, zero_mul]
  let yE : Fin n → 𝒪[k] := Pi.single s 1
  have hyE : ∀ r, (yE r : k) = (Pi.single s 1 : Fin n → k) r := by
    intro r
    simp only [yE, Pi.single_apply]
    split_ifs <;> rfl
  have h1 : Q.HasVal (b' *ᵥ Pi.single s 1) (residue 𝒪[k] (s0 * yE r₀)) := by
    refine (hQ _ _).2 ⟨yE, fun r => ?_, s0, hs0, rfl⟩
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, hyE]
  have h2 : Q.HasVal (g • (b' *ᵥ (Pi.single s 1 : Fin n → k))) (residue 𝒪[k] (s0 * yE r₀)) := by
    rw [← hfix, GlobalTheory.LatPair.Pair.smul_hasVal, inv_smul_smul]
    exact h1
  obtain ⟨y1, hy1, s1, hs1, ha1⟩ := (hQ _ _).1 h2
  obtain rfl : s1 = s0 := Subtype.ext (hs1.trans hs0.symm)
  have hM : (y1 r₀ : k) = M r₀ s := by
    rw [hy1]
    change (b *ᵥ (g.val *ᵥ (b' *ᵥ (Pi.single s 1 : Fin n → k)))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg, Matrix.mulVec_single_one]
    rfl
  have h3 : residue 𝒪[k] (y1 r₀ - yE r₀) = 0 := by
    rw [map_mul, map_mul] at ha1
    rw [map_sub, mul_left_cancel₀ hu ha1, sub_self]
  have h4 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3))
  have h5 : ((y1 r₀ - yE r₀ : 𝒪[k]) : k) = M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s := by
    rw [AddSubgroupClass.coe_sub, hM, hyE, Pi.single_apply, Matrix.one_apply]
  rw [← h5]
  exact h4


set_option maxHeartbeats 1000000 in
theorem exists_gl {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {V : HSp D} (β : GlobalTheory.FinPl.Frame p V (Fin V.rank)) (κ : GA D V) :
    ∃ g : GL (Fin V.rank) k, (mt V κ).map p.pr = β.b * g.val * β.b' := by
  have hm : ∀ x y : GA D V, x * y = 1 → (mt V x).map p.pr * (mt V y).map p.pr = 1 := by
    intro x y h
    have e : mt V x * mt V y = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, h, map_one, Units.val_one]
    rw [← Matrix.map_mul, e]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ A A' : Matrix (Fin V.rank) (Fin V.rank) k, A * A' = 1 → (β.b' * A * β.b) * (β.b' * A' * β.b) = 1 := by
    intro A A' h
    calc (β.b' * A * β.b) * (β.b' * A' * β.b) = β.b' * (A * ((β.b * β.b') * A')) * β.b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [β.bb', Matrix.one_mul, h, Matrix.mul_one, β.b'b]
  refine ⟨⟨β.b' * (mt V κ).map p.pr * β.b, β.b' * (mt V κ⁻¹).map p.pr * β.b, hc _ _ (hm _ _ (mul_inv_cancel κ)),
    hc _ _ (hm _ _ (inv_mul_cancel κ))⟩, ?_⟩
  calc (mt V κ).map p.pr = (β.b * β.b') * (mt V κ).map p.pr * (β.b * β.b') := by rw [β.bb', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]


set_option maxHeartbeats 2000000 in
theorem entry_cong (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (T : ℕ)
    (t t' : 𝓞 D.host.E) (h1 : (t' : D.host.E) = star (t : D.host.E)) (h2 : t * t' = (T : 𝓞 D.host.E)) (h3 : IsCoprime t t')
    (h4 : t ∈ P.asIdeal) (h5 : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h6 : (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (r s : Fin n)
    (hi : Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E p.v)
    (hl : valuation k (((mt V κ).map p.pr) ((finCongr hn).symm r) ((finCongr hn).symm s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) k) ((finCongr hn).symm r) ((finCongr hn).symm s)) < 1) :
    ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  subst hn
  let y : AE D := mt V κ r s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s
  have hy : Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s := by
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h7 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← hy]
  refine GlobalTheory.LocMod.SplitUnif.eq_mul_of_val_lt_one D k p P hP T t t' h1 h2 h3 h4 h5 h6 y ?_ ?_
  · rw [hy]
    refine Subring.sub_mem _ hi ?_
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [y]
    rw [map_sub, h7]
    exact hl

end GlobalTheory.FamTrace.LastRow


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.RedAt

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq

theorem val_lt_of_pr {y : D.host.E} (hy : valuation K (q.pr (incA D y)) < 1) : PP.valuation D.host.E y < 1 := by
  have val_lt_one_iff (x : 𝓞 D.host.E) :
      valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
    by_cases hx : x = 0
    · subst hx; simp
    have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    rw [hq.2 x hx, ← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
  have val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
    have h := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
      (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
    simpa using h
  by_cases hle : PP.valuation D.host.E y ≤ 1
  · obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hle
    have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
      le_antisymm (val_le_one _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff _).1 h'))
    have hr : r ∈ PP.asIdeal := by
      refine (val_lt_one_iff r).1 ?_
      rw [show ((r : 𝓞 D.host.E) : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd,
        mul_one]
      exact hy
    have hdv : PP.valuation D.host.E ((d : 𝓞 D.host.E) : D.host.E) = 1 :=
      le_antisymm (PP.valuation_le_one _) (not_lt.1 fun h' => d.2 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 h'))
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).2 hr
    rw [← e, map_mul] at h1
    rwa [show algebraMap (𝓞 D.host.E) D.host.E (d : 𝓞 D.host.E) = ((d : 𝓞 D.host.E) : D.host.E) from rfl, hdv, mul_one] at h1
  · exfalso
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hle (by simp)
    have h1 : PP.valuation D.host.E y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hle)
    have h2 := GlobalTheory.SeeSaw.LevChi.val_rat_lt q hq h1
    have h3 : q.pr (incA D y) * q.pr (incA D y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
    have h4 := congrArg (valuation K) h3
    rw [map_mul, map_one] at h4
    have h5 : valuation K (q.pr (incA D y)) * valuation K (q.pr (incA D y⁻¹)) < 1 :=
      (mul_le_of_le_one_right' h2.le).trans_lt hy
    exact (ne_of_lt h5) h4

theorem hasRes_of_pr {z : AE D} (c : 𝓞 D.host.E) (hz : valuation K (q.pr z - q.pr (incA D (c : D.host.E))) < 1) :
    GlobalTheory.Mem.Col2.HasRes PP (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z)) (Ideal.Quotient.mk PP.asIdeal c) := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : Valued.v (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) < 1 := by
    rw [← GlobalTheory.Mem.Col2.adAt_inclE D.host.F, ← map_sub, e, add_sub_cancel_left]
    exact valued_nat_mul_lt hr hN'
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    refine GlobalTheory.SeeSaw.LevChi.val_pr_lt q hq ?_
    have e2 : toEAf D (z - incA D y) = toEAf D z - Formalism.UG.inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y := by
      rw [RingHom.map_sub]
      rfl
    rw [e2, map_sub, GlobalTheory.Mem.Col2.adAt_inclE]
    exact h1
  have h3 : valuation K (q.pr (incA D (y - (c : D.host.E)))) < 1 := by
    have e3 : q.pr (incA D (y - (c : D.host.E))) = (q.pr z - q.pr (incA D (c : D.host.E))) - q.pr (z - incA D y) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [e3]
    exact Valuation.map_sub_lt _ hz h2
  have h4 := val_lt_of_pr q hq h3
  refine ⟨c, rfl, ?_⟩
  have e4 : GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
      (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) +
        algebraMap D.host.E (PP.adicCompletion D.host.E) (y - (c : D.host.E)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [e4]
  refine Valuation.map_add_lt _ h1 ?_
  rw [valued_algebraMap]
  exact h4

end Split

end GlobalTheory.FamTrace.RedAt

namespace GlobalTheory.FamTrace.RedAt


end GlobalTheory.FamTrace.RedAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.Rows

open GlobalTheory.FinPl

section Gen

variable {D : D7}

theorem idAt_le {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p) {z : AE D} (hz : z ∈ idAt D P) : z ∈ idAt D Q := by
  simp only [idAt, Submodule.mem_inf, idOff, Submodule.mem_iInf] at hz ⊢
  exact ⟨hz.1, fun w => hz.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem moves_mono {V : HSp D} {g : GA D V} {L : GlobalTheory.FinPl.Lat V} {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p)
    (H : GlobalTheory.FinPl.Moves V g L L Q) : GlobalTheory.FinPl.Moves V g L L P := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D Q := fun i => idAt_le h (hy i)
  rw [MovesSplit.mem_latV_iff_all V L P hy, MovesSplit.mem_latV_iff_all V L P (KOpen.supp_mulVec V P g hy),
    ← MovesSplit.mem_latV_iff_all V L Q hy', ← MovesSplit.mem_latV_iff_all V L Q (KOpen.supp_mulVec V Q g hy')]
  exact H y hy'

theorem st_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : GlobalTheory.FinPl.Lat V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ)
    (g : GA D V) : finE V g ∈ St β ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves V g Λ Λ (· = v) := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg D.host.E Λ
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
  exact forall_congr' fun v => (GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v _).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1000000 in
theorem moves_of_stab (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (t x : GA D V)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (bas : GL Y k)
    (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β ((F.β * bas.val).submatrix id σ))
    (m : GL Y k) (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hs : m ∈ stabLat bas) :
    GlobalTheory.FinPl.Moves V (t⁻¹ * x * t) Λ Λ (· = q.v) := by
  have h1 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', inv_mul_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (mt V t).map q.pr * (mt V t⁻¹).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', mul_inv_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  let F' : GlobalTheory.LocMod.Frame k V.rank Y := ⟨(mt V t⁻¹).map q.pr * F.β, F.γ * (mt V t).map q.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((mt V t).map q.pr), h2, Matrix.one_mul, F.γβ]⟩
  have hM' : MovedTo (ofSplit q) V 1 β ((F'.β * bas.val).submatrix id σ) := by
    intro b hb
    have h3 : (mt V t).map q.pr * b.map q.pr = (F.β * bas.val).submatrix id σ := by
      rw [← Matrix.map_mul]; exact hM b hb
    have h4 : (F'.β * bas.val).submatrix id σ = (mt V t⁻¹).map q.pr * (F.β * bas.val).submatrix id σ := by
      show ((mt V t⁻¹).map q.pr * F.β * bas.val).submatrix id σ = _
      rw [Matrix.mul_assoc]
      rfl
    rw [h4, ← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul, LevRed.mt_one', Matrix.one_mul]
    rfl
  have h0 : GlobalTheory.FinPl.Moves V 1 Λ Λ (· = q.v) := fun y _ => by rw [LevRed.mt_one', Matrix.one_mulVec]
  have hl := LevMoves.isLat_moved q hq V Λ Λ β hβ 1 h0 F' bas σ hM'
  obtain ⟨gl, g1, g2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V _ F'.β F'.γ F'.βγ F'.γβ
  refine (_root_.GlobalTheory.FrameMoves.moves_iff_smul D k q V _ ⟨F'.β, F'.γ, F'.βγ, F'.γβ, gl, g1, g2⟩ Λ _ hΛ hl _).2 ?_
  have h5 : (mt V (t⁻¹ * x * t)).map q.pr = F'.β * m.val * F'.γ := by
    rw [LevRed.mt_mul', LevRed.mt_mul', Matrix.map_mul, Matrix.map_mul, hm]
    simp only [F', Matrix.mul_assoc]
  have h6 := (eq_coordHom_iff V q.pr F'.β F'.γ F'.βγ F'.γβ _ _).1 h5
  exact h6 ▸ LevMoves.smul_latOf hs

end Gen

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1000000 in
theorem red_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (β : GL (Fin V.rank) (Lev.EAf D)) (t x : GA D V) {s : ℕ} (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (F : GlobalTheory.LocMod.Frame k V.rank (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)))
    (e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) 0 ≃ Fin V.rank) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (hM : MovedTo (ofSplit q) V t β ((F.β * ((S.T (Fin D.R.t)).bas 0 (s + 1) (Nat.zero_add _)).val).submatrix id
      fun a => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _) (e.symm a)))
    (hr : D.R.r ≤ V.rank) (m : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)) k)
    (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hst : finE V (t⁻¹ * x * t) ∈ St β) :
    (∃ z : S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin (s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ c : 𝓞 D.host.E,
        Ideal.Quotient.mk PP.asIdeal c = (upperLeftBlock hr (redFn β PP (finE V (t⁻¹ * x * t)))).val a' b' →
        valuation k ((z : GL (Fin D.R.k ⊕ Fin (s + 1)) k).val a b - (ofSplit q).pr (c : D.host.E)) < 1) ↔
      m ∈ ((S.T (Fin D.R.t)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨w, hw⟩ := hst
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨π', hπ, hred, -, -⟩ := _root_.GlobalTheory.FinPl.SplitPt.exists_lift_isRed D _ q PP hq
  have h1 := RedLev.mul_moved (ofSplit q) hπ _ _ _ _ w hw hM
  have h3 := RedLev.conj_eq F ((S.T (Fin D.R.t)).bas 0 _ (Nat.zero_add _)) m
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) _
    ((congrArg (· * _) hm).symm.trans h1)
  have hk : D.R.k + (s + 1) = D.R.r := by
    unfold Ranks.r
    omega
  have hlt : ∀ i : Fin V.rank, i.val < D.R.r := fun i => by
    obtain ⟨i, rfl⟩ := e.surjective i
    rw [he, ← hk]
    rcases i with (i | i) | i
    · exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left i.2 _
    · exact i.1.elim0
  have htri : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) w ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) :=
    Formalism.L2.DIV.mem_blockTri.2 fun i j h => by simp [Formalism.L2.DIV.blk2, hlt] at h
  have hpos : ∀ i, (e (.inl i)).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i := fun i => by
    rw [he]
    rcases i with i | i <;> rfl
  let T := typeFrame S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _))
  let g := (reGL (ixZero _ (Fin D.R.t))).symm (T.conj.symm m)
  have hg : ∀ i j, g.val i j = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w.val (e (.inl i)) (e (.inl j))) :=
    fun i j => by
      have := congrFun (congrFun h3 (e (.inl i))) (e (.inl j))
      simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Matrix.map_apply] at this
      exact this
  have h6 : ∀ i j (c : 𝓞 D.host.E),
      Ideal.Quotient.mk PP.asIdeal c = Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))) →
      valuation k (g.val i j - (ofSplit q).pr (c : D.host.E)) < 1 := fun i j c hc => by
    have h5 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E c) =
        (ofSplit q).pr (c : D.host.E) := hπ (incA D (c : D.host.E))
    rw [hg, ← h5, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, hc, sub_self]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨g', hg', e'⟩ := S.P.exists_of_congr z.2 (M := g.val) fun i j => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))))
      have h4 := hz i j ⟨_, hlt (e (.inl i))⟩ ⟨_, hlt (e (.inl j))⟩ (hpos i) (hpos j) c
        (by rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri]; exact hc)
      have := Valuation.map_sub_lt _ (h6 i j c hc) h4
      rwa [sub_sub_sub_cancel_right] at this
    obtain rfl : g' = g := Units.ext e'
    exact hg'
  · intro hJ
    refine ⟨⟨g, hJ⟩, fun i j a' b' ha hb c hc => h6 i j c ?_⟩
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri, Matrix.submatrix_apply] at hc
    have ea : Fin.castLE hr a' = e (.inl i) := Fin.ext (ha.trans (hpos i).symm)
    have eb : Fin.castLE hr b' = e (.inl j) := Fin.ext (hb.trans (hpos j).symm)
    rw [ea, eb] at hc
    exact hc

end Loc

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}


end Real

end GlobalTheory.FamTrace.Rows

end
end

