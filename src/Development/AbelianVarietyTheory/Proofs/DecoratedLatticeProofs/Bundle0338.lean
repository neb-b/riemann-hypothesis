module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndicatorVac

theorem splitC (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : IsSplitIdem D (cA D q.e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := q.split
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [GlobalTheory.LatVac.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]

theorem e_eq (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.sec 1 = q.e := by
  have := q.sec_pr 1; rw [map_one, mul_one] at this; exact this

theorem mul_e (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he : e' * e' = e') : q.e * e' = 0 ∨ q.e * e' = q.e := by
  have hp : q.pr e' * q.pr e' = q.pr e' := by rw [← map_mul, he]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h
  · left; rw [← q.sec_pr, h, map_zero]
  · right; rw [← q.sec_pr, h, e_eq]

set_option maxHeartbeats 1600000 in
theorem cases (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he' : IsSplitIdem D e') {m n : ℕ} (u : Mx D m n)
    (hsupp : ∀ i j, (q.e + cA D q.e) * u i j = u i j) (hu : IsHalf e' u) :
    u = 0 ∨ IsHalf q.e u ∨ IsHalf (cA D q.e) u := by
  obtain ⟨h1, h2, -⟩ := he'
  have hc1 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]
  have hA := mul_e D k q e' h1
  have hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e := by
    rcases mul_e D k q (cA D e') hc1 with h | h
    · left; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
    · right; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA] at this
  have hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j := fun i j => by
    rw [mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]
  have hee : q.e * q.e = q.e := q.split.1
  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; ext i j; rw [hu' i j, hA, hB]; simp
  · right; right; intro i j; rw [hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]
  · right; left; intro i j; rw [hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]
  · exfalso
    have hpe : q.pr q.e = 1 := by rw [← e_eq D k q, q.pr_sec]
    have h7 : q.e = 0 := by
      rcases mul_e D k q (cA D e') hc1 with h | h
      · have h5 : cA D q.e * e' = 0 := by
          have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
        have h6 : cA D q.e = 0 := hB.symm.trans h5
        have := congrArg (cA D) h6; rwa [GlobalTheory.LatVac.cA_cA, map_zero] at this
      · calc q.e = q.e * cA D e' := h.symm
          _ = q.e * e' * cA D e' := by rw [hA]
          _ = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [h7, map_zero] at hpe
    exact zero_ne_one hpe

end GlobalTheory.IndicatorVac


open GlobalTheory.IndicatorVac in
theorem GlobalTheory.LocMod.indicator_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT
  have hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    fun u hu => AddSubgroup.closure_mono (fun w hw => by
      obtain ⟨α, h1, _, h3⟩ := hw
      exact ⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu
  have hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v),
      ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1 := fun x hx u hu =>
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (_root_.GlobalTheory.UpMem.up_mem_latO D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)
  constructor
  · intro Tm O hTm hO
    have hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      obtain ⟨x, hx, rfl⟩ := _root_.GlobalTheory.HalfIntUp.exists_int_up D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he
      refine (hTm.trans x O O fun t => ?_).symm
      rw [hO]
      have hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k] := by
        refine ⟨fun h r s => ?_, fun h r s => ?_⟩
        · have := sub_mem (h r s) (hx r s); simpa using this
        · exact add_mem (h r s) (hx r s)
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]
    have hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      refine (hTm.modul u he O O fun t => ?_).symm
      rw [hO]
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [hsy t ht u hu, one_mul]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]
    refine ⟨hTm.theta O, ?_, ?_⟩
    · intro u hu
      obtain ⟨ha, hsupp⟩ := _root_.GlobalTheory.SplitVac.idem_latO D k q S T LS LT u hu
      set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def
      have hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) := sub_mem hu ha
      have hee : q.e * q.e = q.e := q.split.1
      have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
      have haH0 : IsHalf q.e a := fun i j => by
        simp only [ha_def, Matrix.of_apply]; rw [← mul_assoc, hee]
      have hbH0 : IsHalf (cA D q.e) (u - a) := fun i j => by
        have h1 : (u - a) i j = cA D q.e * u i j := by
          simp only [Matrix.sub_apply, ha_def, Matrix.of_apply]
          have := hsupp i j
          linear_combination -this
        rw [h1, ← mul_assoc, hce]
      have haH : IsHalf q.e (a + a) := fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]
      have hbH : IsHalf (cA D q.e) ((u - a) + (u - a)) := fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]
      have h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a)) := by rw [two_nsmul]; abel
      have key := GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)
      rw [hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2] at key
      have hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1 := by
        obtain ⟨x, hx, hxa⟩ := _root_.GlobalTheory.HalfIntUp.exists_int_up D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0
        have h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a)) := by
          rw [symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add (f := _), add_halves,
            RingHom.map_one, one_mul]
        rw [h3]
        have := hsy x hx _ (add_mem hb hb)
        rwa [← hxa] at this
      rw [hph, one_smul] at key
      exact key.symm
    · intro e' he' u hu hue
      rcases cases D k q e' he' u (_root_.GlobalTheory.SplitVac.idem_latO D k q S T LS LT u hu).2 hue with h | h | h
      · subst h; exact GlobalTheory.LatVac.heisO_zero ψ _
      · exact hE u hu h
      · exact hC u hu h
  · intro f hf
    have h78 := _root_.GlobalTheory.LocSympl.halves_at_split D k (ofSplit q) Y Y' S T FS FT ψ ψk hc
    have hth : IsThetaFunO ψ S T f := hf.1
    have hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f := hf.2
    have h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f :=
      fun x hx => hlv.2 q.e q.split _ (_root_.GlobalTheory.UpMem.up_mem_latO D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1
    have h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y →
        (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) →
        heisO ψ S T y f = f := fun y hy hann =>
      hlv.2 (cA D q.e) (splitC D k q) y
        (_root_.GlobalTheory.SplitVacAnnih.annihilator_mem_latO D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy
    obtain ⟨T₁, hT₁, hT₁O⟩ := (_root_.GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2
    exact ⟨T₁, hT₁, fun O hO => hT₁O O hO⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseRowFourierTransformMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

theorem finv_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∀ (C : ℂ) (Φ : Matrix Unit n k → ℂ), Φ ∈ SB (Matrix Unit n k) → GlobalTheory.KappaModel.finv ψk ν C Φ ∈ SB (Matrix n Unit k) := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν C Φ hΦ
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψk hψ hne
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e' : Matrix n Unit k ≃ₜ (n → k) :=
    { toFun := fun x r => x r ()
      invFun := fun y => Matrix.of fun r _ => y r
      left_inv := fun M => by ext i j; rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hf : (fun η : n → k => Φ (Matrix.of fun _ r => η r)) ∈ SB (n → k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc hf
  have eq : finv ψk ν C Φ = fun x => C * (fun y : n → k => ∫ η, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) (e' x) := by
    funext x; rfl
  rw [eq]
  refine ⟨?_, ?_⟩
  · exact (hF.1.comp_continuous e'.continuous).comp (fun z => C * z)
  · exact (hF.2.comp_homeomorph e').mul_left

end GlobalTheory.KappaModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

noncomputable section
namespace GlobalTheory.LocMod

def IsLocFac (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (PP : Formalism.L2.DIV.Pl D.host.E) (c : WO S T →₀ ℂ)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k)
    (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) (Ξk : Matrix Y Y' k → ℂ),
    DenseRange p.pr ∧ Formalism.L2.NTheta.IsIdemAt p.e PP ∧
    (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) ∧
    Ξk ∈ SB (Matrix Y Y' k) ∧ p.IsCombAt ψ FS FT c Ξk ∧ ∀ γ, Ξ γ = Ξk (FT.γ * γ.map p.pr * FS.β)

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsModelCombL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.BiCombStable

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def biCombL (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    (WO A S → WO S A' → ℂ) →ₗ[ℂ] (WO A S → WO S A' → ℂ) where
  toFun := biComb ψ A S A' c c'
  map_add' f g := by
    funext u v
    simp only [biComb, comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u v
    simp only [biComb, comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end GlobalTheory.BiCombStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitPlaceProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  intro D k _ _ _ _ q Y Y' _ _ _ _ S T FS FT ΛS ΛT hS hT
  letI := hS
  letI := hT
  exact GlobalTheory.SplitSBProd.isSBHalf_splitProd D k q Y Y' S T FS FT ΛS ΛT
    inferInstance inferInstance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem isThetaFunO_sliceT :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L),
      IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.SliceModelT.isThetaFunO_sliceT_left o hf y

end GlobalTheory.FinPl.ExtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSplitPlaceSchroedingerModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.LinTheta

theorem infPart_of_isSplitIdem {D : D7} {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, hε, -, -⟩, h3⟩ := he
  have h4 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← h3, mul_add, h1, h2, add_zero]
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    have h6 : fstA D.host.F ε = 0 := by rw [hε]; rfl
    simp [infPart, Algebra.TensorProduct.algebraMap_apply, h6]
  rw [h4, map_mul, h5, mul_zero]

theorem isThetaFunO_placeModel (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Lat S) (ΛT : Lat T)
    (e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsSplitIdem D e) (hf : IsThetaFunO ψ S T f₀)
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (Φ : WO S T → ℂ)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ) : IsThetaFunO ψ S T (Tm Φ) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
  exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance he.1 he.2.1 (infPart_of_isSplitIdem he) hf Tm hTm Φ hΦ

end GlobalTheory.LocMod.LinTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionCompSkewAdjointSimilitude
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaTheta

theorem isThetaFunO_comp_kappa : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L'' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w))) := by
  intro D ψ L S L'' τ hτ f hf
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  set κ : WO S L'' → WO L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  obtain ⟨hadd, hcont, hrat, -, hsym, hparts⟩ :=
    GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (κ w) (κ w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [hsym]
    push_cast
    ring
  let A : WO S L'' →+ WO L S := AddMonoidHom.mk' κ hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun k M h1 h2 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) ⟨γ, rfl⟩
    show f (κ (ratW L'' S γ + w)) = ψ (-(symplOH S L'' (ratW L'' S γ) w)) * f (κ w)
    have e : κ (ratW L'' S γ) = ratW S L γ' := hγ'.symm
    rw [hadd, ← hH, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hparts u).1 h0)) (κ w)
    unfold heisO at e ⊢
    show ψ (symplOH S L'' w u) * f (κ (w + u)) = f (κ w)
    rw [← e, ← hH, hadd]
    rfl
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => (hparts (M t)).2 (h2 t)
    have := hf.smooth k (A.comp M) (hcont.comp h1) h3 (κ w)
    have heq : (fun t => f (κ (w + M t))) = fun t => f (κ w + A (M t)) :=
      funext fun t => congrArg f (hadd w (M t))
    exact (congrArg (ContDiff ℝ _) heq).mpr this

end GlobalTheory.KappaTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

end GlobalTheory.SeeSaw.Resc

end
end

