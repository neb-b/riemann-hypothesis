module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineLatticeSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftModel

theorem isSelfDualC_lineLat : ∀ (D : D7) (S : HSp D) (ζ : Fin S.rank → D.host.E), IsLineVec S ζ → ∀ (𝔄 : FI D), (∀ d : D.host.E, d ∈ 𝔄 ↔ ∀ c ∈ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ)) → IsSelfDualC S (GlobalTheory.SeeSaw.LiftModel.lineLat S ζ 𝔄) := by
  intro D S ζ hζ 𝔄 h𝔄
  classical
  obtain ⟨h1, hH⟩ := hζ
  haveI : Subsingleton (Fin S.rank) := by rw [h1]; infer_instance
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  have all : ∀ i : Fin S.rank, i = i₀ := fun i => Subsingleton.elim _ _
  set z := ζ i₀ with hz
  set g := S.gram i₀ i₀ with hg
  have eH : star ζ ⬝ᵥ S.gram *ᵥ ζ = star z * (g * z) := by
    simp only [dotProduct, mulVec, Fintype.sum_subsingleton _ i₀, Pi.star_apply]
    rfl
  have z0 : z ≠ 0 := by
    intro h0; apply hH; rw [eH, h0]; simp
  have repr : ∀ y : Fin S.rank → D.host.E, y = (y i₀ / z) • ζ := by
    intro y; funext i; rw [all i]; simp [div_mul_cancel₀ _ z0, ← hz]
  have memΛ : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ ∃ c ∈ 𝔄, c • ζ = y := by
    intro y
    simp [lineLat, Submodule.mem_map, LinearMap.toSpanSingleton_apply]
  have memΛ' : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ y i₀ / z ∈ 𝔄 := by
    intro y
    rw [memΛ]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [← hz, mul_div_cancel_right₀ _ z0] using hc
    · intro h
      exact ⟨_, h, (repr y).symm⟩
  have sum_eq : ∀ c d : D.host.E, ∑ i, ∑ j, star ((c • ζ) i) * S.gram i j * (d • ζ) j =
      star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ) := by
    intro c d
    rw [eH]
    simp only [Fintype.sum_subsingleton _ i₀, Pi.smul_apply, smul_eq_mul, star_mul', ← hz, ← hg]
    ring
  have dual : ∀ y : Fin S.rank → D.host.E, y ∈ lineLat S ζ 𝔄 ↔
      ∀ x ∈ lineLat S ζ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    rw [memΛ', h𝔄]
    constructor
    · intro h x hx
      obtain ⟨c, hc, rfl⟩ := (memΛ x).1 hx
      obtain ⟨b, hb⟩ := h c hc
      refine ⟨b, ?_⟩
      conv_rhs => rw [repr y]
      rw [sum_eq, hb]
    · intro h c hc
      obtain ⟨b, hb⟩ := h (c • ζ) ((memΛ _).2 ⟨c, hc, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb]
      conv_lhs => rw [repr y]
      rw [sum_eq]
  refine ⟨⟨?_, ?_⟩, dual⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔄).map _
  · obtain ⟨c, hc, hc0⟩ : ∃ c ∈ 𝔄, c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1m : (1 : D.host.E) ∈ 𝔄 := by
        rw [h𝔄]
        intro c hc
        exact ⟨0, by simp [hcon c hc]⟩
      exact one_ne_zero (hcon 1 h1m)
    have hcζ : c • ζ ∈ lineLat S ζ 𝔄 := (memΛ _).2 ⟨c, hc, rfl⟩
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SeeSaw.LiftModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.GluedLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add (f := _)]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem valuation_xi_zero_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_intAt p h1.2
  have h4 := pr_mem_of_intAt p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

end GlobalTheory.MiTop.GluedLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem linFirst (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T)
    (hW : IsWeilDatumO ψ S T χS χT om) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (f : WO S T → ℂ) (hO : Over ψ α β LS LT f₀ Ψ f) (g : GL n' k) (h : GL n k) :
    Over ψ α β LS LT f₀ (fun x => (lam p χT⁻¹ ((T.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (lam p χS (-(S.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val))
      (om (α.gl g, β.gl h) f) := by
  obtain ⟨hsS, hsT, hV, hΨ, hth⟩ := hO
  have he : IsSplitIdem D p.e := p.split
  have hec : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
    fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)
  have hle := latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)
  have hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀ := fun u hu hh =>
    hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1)
      fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1
  refine ⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩
  have hTm' := (placeModel_congr hA hle).1 hTm
  have hSB := (sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)
  rw [hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h)
    (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]

theorem idl_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) : idl p a = p.idele a := by
  ext
  rw [idl_val, p.idele_val]
  ring

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem algebraMap_inj (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem idem_calc {R : Type} [CommRing R] (E C s t : R) (he : E * E = E) (hcc : C * C = C) (hc : E * C = 0)
    (hs : E * s = s) (hcs : C * t = t) : (1 - E + s) * (1 - C + t) * (1 - (E + C)) = 1 - (E + C) := by
  have h1 : (1 - E + s) * (1 - C + t) = 1 - E - C + s + t := by
    linear_combination (1 - t - s + s * t) * hc + (E - s) * hcs + (C - C * t) * hs
  have h2 : (1 - E - C + s + t) * (1 - (E + C)) = 1 - (E + C) := by
    linear_combination he + hcc + (2 - s - t) * hc + (C - 1) * hs + (E - 1) * hcs
  rw [h1, h2]

theorem norm_idele_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (ε : AF D.host.F) (hε : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) :
    Algebra.norm (AF D.host.F) (p.idele a : AE D) * (1 - ε) = 1 - ε := by
  apply algebraMap_inj D
  rw [map_mul, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_sub, map_one, ← hε, p.idele_val]
  have he : p.e * p.e = p.e := p.split.1
  have hc : p.e * cA D p.e = 0 := p.split.2.1
  have hcc : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have hcs : cA D p.e * cA D (p.sec a) = cA D (p.sec a) := by rw [← map_mul, hs]
  have hx : cA D (1 - p.e + p.sec a) = 1 - cA D p.e + cA D (p.sec a) := by
    rw [map_add (f := _), map_sub, map_one]
  rw [hx]
  exact idem_calc _ _ _ _ he hcc hc hs hcs

theorem normOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (w : Pl D), w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D w (p.idele a) = 1 := by
  intro D k _ _ _ _ p a w hw
  obtain ⟨ε, ⟨α, rfl, -, hα⟩, hsum⟩ := p.above
  have h := congrArg (fun y => evalV D.host.F w (sndA D.host.F y)) (norm_idele_mul p a _ hsum)
  simp only [map_mul, map_sub, map_one] at h
  have h0 : evalV D.host.F w (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα w hw
  rw [h0, sub_zero, mul_one] at h
  exact Units.ext h

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem norm_idele_chart {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (π : AE D →+* Fv D.host.F p.v)
    (halg : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F p.v (sndA D.host.F y))
    (πe : π p.e = 1) (πce : π (cA D p.e) = 0) (a : kˣ) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = π (p.sec a) := by
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have key : evalV D.host.F p.v (sndA D.host.F (Algebra.norm (AF D.host.F) (p.idele a : AE D))) = π (p.sec a) := by
    rw [← halg, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_mul, p.idele_val]
    have hcs : cA D (p.sec a) = cA D p.e * cA D (p.sec a) := by rw [← map_mul, hs]
    rw [map_add (f := _), map_sub, map_one, map_add (f := _), map_sub, map_one, map_add (f := _), map_sub, map_one, πe, hcs, map_mul, πce, zero_mul]
    ring
  exact key

open GlobalTheory.SplitHecke

theorem chartAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k), ∃ φ : k ≃+* Fv D.host.F p.v, (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) ∧
      ∀ a : kˣ, ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = φ a := by
  intro D k _ _ _ _ p
  obtain ⟨v', π, hsurj, hker, halg, hint⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have he : p.e * p.e = p.e := p.split.1
  have hce : p.e * cA D p.e = 0 := p.split.2.1
  have hs : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have πe : π p.e = 1 := by
    obtain ⟨c, hc⟩ := hsurj 1
    have h0 : π (p.e * c - c) = 0 := (hker _).2 (by rw [mul_sub, ← mul_assoc, he, sub_self])
    rw [map_sub, map_mul, hc, mul_one, sub_eq_zero] at h0
    exact h0
  have πce : π (cA D p.e) = 0 := (hker _).2 hce
  have hv : v' = p.v := by
    obtain ⟨ε, ⟨α, rfl, h1, hα⟩, hsum⟩ := p.above
    by_contra hne
    have h2 := halg (pairA D.host.F 0 α)
    rw [← hsum, map_add (f := _), πe, πce, add_zero] at h2
    have h3 : evalV D.host.F v' (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα v' hne
    rw [h3] at h2
    exact one_ne_zero h2
  subst hv
  let f : k →+* Fv D.host.F p.v :=
    { toFun := fun a => π (p.sec a)
      map_one' := by rw [SplitPt.sec_one, πe]
      map_mul' := fun a b => by rw [SplitPt.sec_mul, map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)] }
  have hsurjf : Function.Surjective f := fun b => by
    obtain ⟨c, rfl⟩ := hsurj b
    refine ⟨p.pr c, ?_⟩
    show π (p.sec (p.pr c)) = π c
    rw [p.sec_pr, map_mul, πe, one_mul]
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, hsurjf⟩, fun a => ?_, fun a => ?_⟩
  · show Valued.v (π (p.sec a)) ≤ 1 ↔ a ∈ 𝒪[k]
    rw [p.int_iff, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← isInt_Ov, ← hint, hs]
  · exact norm_idele_chart p π halg πe πce a

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem absAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F p.v (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele q.unit)) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  intro D k _ _ _ _ p q
  obtain ⟨φ, hφ, hn⟩ := chartAt D k p
  have h1 := _root_.GlobalTheory.adicCompletion_valuation_map_uniformiser D.host.F p.v k φ hφ q.1 q.2
  have h2 := _root_.GlobalTheory.LocalResidue.card_residue_of_ringEquiv D.host.F p.v k φ hφ
  have h3 : (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))).log = -1 := by
    first | rfl | simp [WithZero.log] | exact WithZero.log_coe _
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, hn, GlobalTheory.LatPair.Unif.unit, Units.val_mk0, h1, resCard, h2, h3, zpow_neg_one]

open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem absFin_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p q.unit) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  rw [idl_eq, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, finprod_eq_single _ p.v, absAt D k p q]
  intro w hw
  rw [normOff D k p _ w hw, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  simp

theorem lam_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (χ : (AE D)ˣ →* Circle) (r : ℝ) :
    ((lam p χ r q.unit : ℂˣ) : ℂ) = (((resCard k : ℝ) ^ (-r) : ℝ) : ℂ) * (χ (p.idele q.unit) : ℂ) := by
  rw [lam_val, absFin_unif, idl_eq, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), mul_comm]

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem linExact : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  intro D k _ _ _ _ p q ψ S T χS χT om hW
  refine ⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2),
    fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_, ?_,
    fun n n' _ _ _ _ α β LS LT f₀ Ψ f hO g h => linFirst D k p ψ S T χS χT om hW n n' α β LS LT f₀ Ψ f hO g h⟩
  · rw [lam_unif, MonoidHom.inv_apply, chrPow, zpow_neg, zpow_one, neg_div]
  · rw [lam_unif, chrPow, zpow_one, neg_div, neg_neg]

end GlobalTheory.LinExactAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.LocComp

theorem combAt_o {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (l : GlobalTheory.SeeSaw.LocPl ψ S T M M') {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P l.q.v) : GlobalTheory.FinPl.CombAt P l.o :=
  fun x hx i j => GlobalTheory.LocMod.PinInhab.mem_idAt_of_supp l.q hP (l.o_at x hx i j)

theorem combAt_comp {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {P : GlobalTheory.FinPl.Pl D → Prop} {e e' : WO S T →₀ ℂ} (he : GlobalTheory.FinPl.CombAt P e) (he' : GlobalTheory.FinPl.CombAt P e') :
    ∃ e'', GlobalTheory.FinPl.CombAt P e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f) := by
  have h4 := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.2.2.1
  have hm : ∀ {c : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt P c → GlobalTheory.FinPl.CombAt (fun p => P p ∨ False) c :=
    fun hc x hx i j => by simpa only [or_false] using hc x hx i j
  obtain ⟨e'', h1, h2⟩ := h4 e e' (hm he) (hm he')
  exact ⟨e'', fun x hx i j => by simpa only [or_false] using h1 x hx i j, h2⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  intro D ψ hψ S T M M' _ _ n
  induction n with
  | zero =>
    intro L _ P _
    refine ⟨Finsupp.single 0 1, GlobalTheory.FinPl.OffTest.combAt_single_zero P 1, fun F => ?_⟩
    rw [GlobalTheory.FinPl.OffTest.comb_single_zero]
    simp
  | succ n ih =>
    intro L hinj P hP
    obtain ⟨o₁, h₁, h₁'⟩ := ih (fun i => L i.succ) (fun a b h => Fin.succ_injective _ (hinj h)) P (fun i => hP i.succ)
    obtain ⟨o', h', h''⟩ := combAt_comp hψ (combAt_o (L 0) (hP 0)) h₁
    refine ⟨o', h', fun F => ?_⟩
    rw [h'', h₁', List.finRange_succ, List.foldr_cons, List.foldr_map]

end GlobalTheory.LocComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLatticeExistsScalarBoundAttained
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem lattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  intro k _ _ _ _ n _ L hL hn
  obtain ⟨s, hs⟩ := hL.fg

  have hex : ∃ x ∈ s, ∃ j, x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro x hx
      funext j
      exact hcon x hx j
    have htop := hL.span_eq_top
    rw [hbot] at htop
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    obtain ⟨j⟩ := hn
    have h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k)) := Submodule.mem_top
    rw [← htop, Submodule.mem_bot] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨x0, hx0, j0, hx0j⟩ := hex
  have hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty := ⟨(x0, j0), by simp [hx0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n))
    (fun q : (n → k) × n => valuation k (q.1 q.2)) hne
  have hc : p.1 p.2 ≠ 0 := by
    intro h0
    have := hmax (x0, j0) (by simp [hx0])
    simp only [h0, map_zero] at this
    have h' : valuation k (x0 j0) = 0 := le_antisymm this zero_le'
    exact hx0j ((Valuation.zero_iff _).mp h')
  refine ⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro j
      show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1
      have hle := hmax (y, j) (by simpa using hy)
      simp only at hle
      have hvc : valuation k (p.1 p.2) ≠ 0 := by simpa using hc
      rw [map_mul, map_inv₀]
      calc (valuation k (p.1 p.2))⁻¹ * valuation k (y j)
          ≤ (valuation k (p.1 p.2))⁻¹ * valuation k (p.1 p.2) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    | zero => intro j; simp
    | add y z _ _ hy hz =>
      intro j
      simpa [mul_add] using add_mem (hy j) (hz j)
    | smul a y _ hy =>
      intro j
      have := mul_mem a.2 (hy j)
      convert this using 1
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rw [← hs]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  first | exact @GlobalTheory.LocMod.SplitCoord.coord_int_last | exact GlobalTheory.LocMod.SplitCoord.coord_int_last | (intros; apply GlobalTheory.LocMod.SplitCoord.coord_int_last <;> assumption)
end

