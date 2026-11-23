module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeil
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.IP

variable {D : D7}

theorem integrable_star_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ := by
  simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hf

theorem memL2_conj_comp (V : HSp D) (μ : Measure (GA D V)) {f : GA D V → ℂ}
    (hf : MemL2Quotient (GQ V) μ f) : MemL2Quotient (GQ V) μ (fun x => conj (f x)) := by
  refine ⟨fun γ hγ g => by simp only [hf.1 γ hγ g], ?_⟩
  have := (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf.2
  convert this using 1
  funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem petersson_star_comp (V : HSp D) (μ : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    petersson V μ (fun x => conj (f₁ x)) (fun x => conj (f₂ x)) = conj (petersson V μ f₁ f₂) := by
  simp only [petersson, pet]
  rw [← integral_conj]
  congr 1; funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem innerProduct_convergent_conj : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  intro hRD hWS hSE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hw ht hK hm hν hf₁ hf₂
  obtain ⟨om, Φ₁, Φ₂, hW, hF₁, hF₂, -, -, hK₁, hK₂, μ, 𝓕, hcov, hc⟩ := hK
  obtain ⟨a, ha, ha'⟩ := _root_.GlobalTheory.Core.Rk.MajFrame.exists_maj_cart D θ A sA hS.2.2.2.1 hS.2.2.2.2.2.2.1
  have hP : Pair ψ θ A B χA χB sA sB t cA a om μ 𝓕 := ⟨hS, ha, ha', hW, hcov⟩
  obtain ⟨hU₁, hU₂, hI, hE⟩ := _root_.GlobalTheory.Core.Rk.IP.innerProduct_convergent hRD hWS hSE D ψ θ A B χA χB sA sB t cA a om μ 𝓕 hP hw ht m ν hm hν
    Φ₁ Φ₂ hF₁ hF₂ f₁ hf₁ f₂ hf₂
  have hcg : ∀ g, c g = conj (wcoef om μ 𝓕 Φ₁ Φ₂ g) := by
    intro g
    have h1 : wcoef om μ 𝓕 Φ₁ Φ₂ g = conj (c g) := by
      have h2 := hc g
      simp only at h2
      rw [h2]; rfl
    rw [h1, Complex.conj_conj]
  have hlift : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K u = fun h => conj (up om m Φ u h) := by
    intro K Φ u hK; funext h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, up, petersson, pet, hK]
    rw [← integral_conj]
    congr 1; funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend]
  have hconv : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) → UpConv om m ν Φ u → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K u := by
    intro K Φ u hK hU
    refine ⟨fun h => ?_, ?_⟩
    · have := integrable_star_comp (hU.1 h)
      convert this using 2 with q
      simp [GlobalTheory.AutomorphicL2Unitary.descend, hK]
    · rw [hlift K Φ u hK]
      exact memL2_conj_comp B ν hU.2
  refine ⟨hconv K₁ Φ₁ f₁ hK₁ hU₁, hconv K₂ Φ₂ f₂ hK₂ hU₂, ?_, ?_⟩
  · have := integrable_star_comp hI
    convert this using 2 with g
    simp [hcg, rcoef]
  · rw [hlift K₁ Φ₁ f₁ hK₁, hlift K₂ Φ₂ f₂ hK₂, petersson_star_comp, hE, map_mul, ← integral_conj]
    simp [hcg, rcoef]

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllCombProof

variable {D : D7}

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem combAt_mono {S T : HSp D} {P Q : Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem over_unique (hψ : IsStdChar D ψ (-1)) {i : ι} {g f' f'' : WO S T → ℂ}
    (h' : Over ψ (α i) (β i) LS LT g (Ψ i) f') (h'' : Over ψ (α i) (β i) LS LT g (Ψ i) f'') : f' = f'' :=
  ((_root_.GlobalTheory.FinPl.overBasic D k (p i) n n' ψ hψ S T (α i) (β i) LS LT h'.1 h'.2.1 g h'.2.2.1).1 (Ψ i) h'.2.2.2.1).unique h' h''

theorem overAll_unique (hψ : IsStdChar D ψ (-1)) (J : List ι) : ∀ f f' f'' : WO S T → ℂ,
    OverAll ψ α β LS LT Ψ J f f' → OverAll ψ α β LS LT Ψ J f f'' → f' = f'' := by
  induction J with
  | nil => intro f f' f'' h' h''; rw [overAll_nil.1 h', overAll_nil.1 h'']
  | cons i J ih =>
    intro f f' f'' h' h''
    obtain ⟨g, hg, h'⟩ := overAll_cons.1 h'
    obtain ⟨g', hg', h''⟩ := overAll_cons.1 h''
    obtain rfl := ih f g g' hg hg'
    exact over_unique hψ h' h''

theorem over_comb (hψ : IsStdChar D ψ (-1)) {i : ι} (hu : (p i).UnitAA) {Q : Pl D → Prop} (hQ : ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) {g f : WO S T → ℂ} (h : Over ψ (α i) (β i) LS LT g (Ψ i) f) :
    Over ψ (α i) (β i) LS LT (comb ψ S T d g) (Ψ i) (comb ψ S T d f) := by
  obtain ⟨c, hc, hcf⟩ := (_root_.GlobalTheory.FinPl.Rebase.rebase D k (p i) n n' ψ hψ hu S T (α i) (β i) LS LS LT LT h.1 h.2.1 h.1 h.2.1).2
    (Ψ i) h.2.2.2.1
  have M := GlobalTheory.DisjComb.main D ψ hψ S T Q (· = (p i).v) (fun x hx hx' => hQ (hx' ▸ hx))
  have hf : f = comb ψ S T c g := over_unique hψ h (hcf g h.2.2.1)
  rw [hf, M.1 d c hd hc g]
  exact hcf _ ((M.2.1 d hd).2 LS LT g h.2.2.1)

theorem overAll_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) {Q : Pl D → Prop} (hQ : ∀ i, ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) (J : List ι) (f : WO S T → ℂ) : ∀ f', OverAll ψ α β LS LT Ψ J f f' →
      OverAll ψ α β LS LT Ψ J (comb ψ S T d f) (comb ψ S T d f') := by
  induction J with
  | nil => intro f' h; rw [overAll_nil.1 h]; exact overAll_nil.2 rfl
  | cons i J ih =>
    intro f' h
    obtain ⟨g, hg, h⟩ := overAll_cons.1 h
    exact overAll_cons.2 ⟨_, ih g hg, over_comb hψ (hu i) (hQ i) hd h⟩

theorem exists_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (hΨ : ∀ i, Ψ i ∈ SB (Matrix n n' k)) (J : List ι) (hJ : J.Nodup) :
    ∃ c : WO S T →₀ ℂ, CombAt (fun x => ∃ i ∈ J, x = (p i).v) c ∧
      ∀ f, (∀ i ∈ J, Vac ψ S T LS LT (· = (p i).v) f) → OverAll ψ α β LS LT Ψ J f (comb ψ S T c f) := by
  induction J with
  | nil =>
    exact ⟨Finsupp.single 0 1, OffTest.combAt_single_zero _ _, fun f _ => overAll_nil.2 (OffTest.comb_single_zero ψ S T f)⟩
  | cons i J ih =>
    obtain ⟨hi, hJ'⟩ := List.nodup_cons.1 hJ
    obtain ⟨c', hc', hf'⟩ := ih hJ'
    obtain ⟨c, hc, hcf⟩ := (_root_.GlobalTheory.FinPl.Rebase.rebase D k (p i) n n' ψ hψ (hu i) S T (α i) (β i) LS LS LT LT hLS hLT hLS hLT).2
      (Ψ i) (hΨ i)
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ∃ j ∈ J, x = (p j).v) (· = (p i).v) (by
      rintro x ⟨j, hj, rfl⟩ hx
      exact hi (hinj hx ▸ hj))
    obtain ⟨c'', hc'', heq⟩ := M.2.2.2.1 c c' (combAt_mono (fun x hx => Or.inr hx) hc)
      (combAt_mono (fun x hx => Or.inl hx) hc')
    refine ⟨c'', combAt_mono ?_ hc'', fun f hf => ?_⟩
    · rintro x (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · exact ⟨i, List.mem_cons_self, rfl⟩
    · rw [heq]
      exact overAll_cons.2 ⟨_, hf' f fun j hj => hf j (List.mem_cons_of_mem _ hj),
        hcf _ ((M.2.1 c' hc').2 LS LT f (hf i List.mem_cons_self))⟩

end GlobalTheory.FinPl.AllCombProof

namespace GlobalTheory.FinPl


open AllCombProof in
theorem allComb : ∀ D : D7, AllComb D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S T α β LS LT hLS hLT Ψ
  refine ⟨fun hΨ => ?_, overAll_unique hψ I, fun d hd f hf => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hf⟩ := exists_comb (α := α) (β := β) hψ hP.unit hP.inj hLS hLT hΨ I hP.nodup
    refine ⟨c, combAt_mono ?_ hc, fun f h => hf f fun i _ => vac_mono ?_ h⟩
    · rintro x ⟨i, -, rfl⟩
      exact (hP.mem _).2 ⟨i, rfl⟩
    · rintro x rfl
      exact (hP.mem _).2 ⟨i, rfl⟩
  · exact ((GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ¬ P x) P fun x hx => hx).2.1 d hd).2 LS LT f hf
  · exact overAll_comb hψ hP.unit (fun i h => h ((hP.mem _).2 ⟨i, rfl⟩)) hd I f

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.DepFrames

theorem gramQ_mul {D : D7} (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u) = uᴴ * gramQ W x * u := by
  simp only [gramQ, conjTranspose_mul, Matrix.mul_assoc]

theorem dep_frames_mean_zero : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∀ j : Fin ρ, ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x = gramQ W x₀ ∧ (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ j
  classical
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  obtain ⟨hLC, hSC, -, -, -, hDisc, hCnt⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have h56 := _root_.GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact D V V₀ ρ d
  haveI : LocallyCompactSpace (flagN d) := h56.1.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : vN.ν.IsHaarMeasure := vN.unit.1
  obtain ⟨hle, hNcl, hNnorm, K, hK, hcov⟩ := h56.2 (Nfix d j) (Or.inr (Or.inr ⟨j, rfl⟩))
  have hT := _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.Unf.sum_term_bound D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  obtain ⟨K0, hK0, hcov0⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨Mb, hMb⟩ := hK0.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ Mb := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov0 n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hMb k hk
  have hbdS : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ∑' x : S, ‖Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ((Mb.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal : NNReal) : ENNReal) := by
    intro S n
    have h1 : ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤ ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := by
      have := hC 1 1 n.1 n.2
      rwa [mul_one] at this
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, ENNReal.coe_mul]
    refine mul_le_mul' ?_ ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans h1)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hThb n)
  let Pj : Matrix (Fin W.rank) (Fin ρ) D.host.E → Prop := fun x => gramQ W x = gramQ W x₀ ∧
    (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
  have huniq : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E,
      (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) →
      ∀ a a' : Fin ρ → D.host.E, a j = 1 → (∀ i, j < i → a i = 0) → x *ᵥ a = 0 →
        a' j = 1 → (∀ i, j < i → a' i = 0) → x *ᵥ a' = 0 → a = a' := by
    intro x hind a a' ha1 ha2 ha3 hb1 hb2 hb3
    refine sub_eq_zero.1 (hind (a - a') (fun i hi => ?_) (by rw [Matrix.mulVec_sub, ha3, hb3, sub_self]))
    rcases hi.lt_or_eq with h | h
    · simp [ha2 i h, hb2 i h]
    · subst h; simp [ha1, hb1]
  have hPu : ∀ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, u * u' = 1 → u' * u = 1 → (∀ i, u i i = 1) →
      (∀ i k, k < i → u i k = 0) → ∀ x, Pj x ↔ Pj (x * u) := by
    intro u u' huu' hu'u hdiag htri x
    have hG := _root_.GlobalTheory.Unf.gramQ_unitri D W ρ x₀ hB u hdiag htri
    refine and_congr ⟨fun h => by rw [gramQ_mul, h, hG], fun h => ?_⟩ ((_root_.GlobalTheory.DepFrame.dependent_frame_first_relation D.host.E W.rank ρ x).2.2 j u hdiag htri)
    rw [gramQ_mul, ← hG] at h
    have h' := congrArg (fun M => u'ᴴ * M * u') h
    have e1 : ∀ M : Matrix (Fin ρ) (Fin ρ) D.host.E, u'ᴴ * (uᴴ * M * u) * u' = M := by
      intro M
      rw [show u'ᴴ * (uᴴ * M * u) * u' = (u * u')ᴴ * M * (u * u') by
        simp only [conjTranspose_mul, Matrix.mul_assoc]]
      rw [huu', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rwa [e1, e1] at h'

  have key : ∀ γ : flagN d, γ.1 ∈ GQ V → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ.1 →
      ∀ (n : flagN d) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E),
        Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) x = Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) (x * u) := by
    intro γ hγ u hu n x
    have hom : om ((γ * n).1, 1) Ψ = om (γ.1, 1) (om (n.1, 1) Ψ) := by
      rw [show (((γ * n : flagN d) : GA D V), (1 : GA D W)) = (γ.1, 1) * (n.1, 1) by
        rw [Prod.mk_mul_mk, one_mul]; rfl, map_mul]
      rfl
    rw [hom, (hT _ (hw.om_pres _ _ hΨ)).2.1 γ.1 hγ γ.2 x (x * u) (by rw [rat_mul, hu]),
      show ((γ * n : flagN d) : GA D V) = γ.1 * n.1 from rfl, hTh.left γ.1 hγ γ.2 n.1 n.2]
  have hfixv : ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i k, k ≤ j → u i k = if i = k then 1 else 0) →
      ∀ c : Fin ρ → D.host.E, (∀ i, j < i → c i = 0) → u *ᵥ c = c := by
    intro u hu c hc
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun k => if i = k then c k else 0) fun k _ => ?_, Finset.sum_ite_eq]
    · simp
    · rcases le_or_gt k j with h | h
      · rw [hu i k h]; split_ifs <;> simp
      · rw [hc k h]; simp
  refine _root_.GlobalTheory.CutSum.integral_tsum_eq_zero (flagN d) vN.ν ((GQ V).subgroupOf (flagN d)) ((Nfix d j).subgroupOf (flagN d)) ?_ ?_ hNnorm
    (hNcl.preimage continuous_subtype_val) ?_ vN.𝓝 vN.unit.2.1 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
    {x // Pj x} (Fin ρ → D.host.E) (fun x => Classical.choose x.2.2.2)
    (fun x n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun x => (hTh.cont.mul (hcont x.1)).measurable)
    ⟨_, fun n => hbdS {x | Pj x} n⟩ ?_ ?_ ?_
  · exact Function.Injective.countable (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · exact DiscreteTopology.of_continuous_injective (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · refine ⟨(fun m : Nfix d j => (⟨⟨m.1, hle m.2⟩, m.2⟩ : (Nfix d j).subgroupOf (flagN d))) '' K,
      hK.image ((continuous_subtype_val.subtype_mk _).subtype_mk _), fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨⟨⟨γ.1, hle γ.2⟩, γ.2⟩, ?_, ⟨⟨k.1, hle k.2⟩, k.2⟩, ⟨k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]; exact Subgroup.mem_subgroupOf.1 hγ
    · have e2 : m.1.1 = γ.1 * k.1 := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e2)
  · intro γ hγ n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, -⟩ := _root_.GlobalTheory.Unf.ratBlock_unitri D V V₀ ρ d γ.1 hγ' γ.2
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    show ∑' i : {x // Pj x}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1 =
      ∑' i : {x // Pj x}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
    rw [← e.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1
  · intro c γ hγ hγM n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, hfix⟩ := _root_.GlobalTheory.Unf.ratBlock_unitri D V V₀ ρ d γ.1 hγ' γ.2
    have hfu := hfixv u (hfix j (Subgroup.mem_subgroupOf.1 hγM))
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    have hκ : ∀ x : {x // Pj x}, Classical.choose (e x).2.2.2 = Classical.choose x.2.2.2 := by
      intro x
      have s1 := Classical.choose_spec (e x).2.2.2
      have s0 := Classical.choose_spec x.2.2.2
      exact huniq _ (e x).2.2.1 _ _ s1.1 s1.2.1 s1.2.2 s0.1 s0.2.1
        (by show (x.1 * u) *ᵥ _ = 0; rw [← Matrix.mulVec_mulVec, hfu _ s0.2.1, s0.2.2])
    let e' := e.subtypeEquiv (p := fun x => Classical.choose x.2.2.2 = c) (q := fun x => Classical.choose x.2.2.2 = c)
      (fun x => by rw [hκ x])
    show ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1.1 =
      ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1
    rw [← e'.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1.1
  · intro c
    by_cases hc : ∃ x : {x // Pj x}, Classical.choose x.2.2.2 = c
    · obtain ⟨x, hx⟩ := hc
      have s0 := Classical.choose_spec x.2.2.2
      rw [hx] at s0
      have hg : gramQ W x₀ *ᵥ c = 0 := by
        rw [← x.2.1, gramQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s0.2.2, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      obtain ⟨v, u, a, hform, htr, huN, ha, hTu⟩ := hTh.dep j c s0.1 s0.2.1 hg
      refine ⟨⟨u, hle huN⟩, huN, a, ha, fun y hy m hm n => ?_⟩
      have sy := Classical.choose_spec y.2.2.2
      rw [hy] at sy
      have hm' : m.1 ∈ Nfix d j := Subgroup.mem_subgroupOf.1 hm
      show Th (m.1 * u * n.1) * term ψ d W vS (om (m.1 * u * n.1, 1) Ψ) y.1 =
        a * (Th (m.1 * n.1) * term ψ d W vS (om (m.1 * n.1, 1) Ψ) y.1)
      rw [hTu m.1 m.2 n.1 n.2, _root_.GlobalTheory.Unf.transv_trivial_after_Nfix D hDesc ψ V V₀ W ρ d χV χW om hw vS Ψ hΨ j c s0.2.1 v u hform htr y.1 sy.2.2
        m.1 hm' n.1, mul_assoc]
    · push_neg at hc
      exact ⟨1, one_mem _, 0, zero_ne_one, fun x hx => absurd hx (hc x)⟩

end GlobalTheory.Unf.DepFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev
variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : Pl D → Prop)
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (↑LS) (↑LT) P ≤ latO S T (↑LS) (↑LT) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, hr⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, hr⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hle hu), fun e he u hu => hf.2.2 e he u (hle hu)⟩

theorem hand_mul_right {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (k : GA D J.W) (a : ℂ) (ha : a ≠ 0)
    (h₁ : s₁.om (1, k) Φ₁ = a⁻¹ • Φ₁) (h₂ : s₂.om (k, 1) Φ₂ = a • Φ₂) (g : GA D B.V) (q₁ : GA D J.W) (q₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (q₁ * k) q₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂ := by
  have e₁ : s₁.om (g, q₁ * k) Φ₁ = a⁻¹ • s₁.om (g, q₁) Φ₁ := by
    rw [show ((g, q₁ * k) : GA D B.V × GA D J.W) = (g, q₁) * (1, k) from by simp, map_mul, Module.End.mul_apply, h₁,
      LinearMap.map_smul]
  have e₂ : s₂.om (q₁ * k, q₂) Φ₂ = a • s₂.om (q₁, q₂) Φ₂ := by
    rw [show ((q₁ * k, q₂) : GA D J.W × GA D B'.V) = (q₁, q₂) * (k, 1) from by simp, map_mul, Module.End.mul_apply, h₂,
      LinearMap.map_smul]
  unfold Chain.hand
  rw [e₁, e₂, (GlobalTheory.HandHom.hand_hom D ψ σ B J B' s₁ s₂ l vL φ).1, inv_mul_cancel₀ ha, one_smul]

theorem integ_lev : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * k) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a _ f _ k hk q₁ q₂
  obtain ⟨b, hb, l₁, l₂, -⟩ := hF.lawG j (by omega) k hk
  have hd : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.1 hF.disjG hp
  have v₁ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ j) (hF.atQ j).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₁)
  have v₂ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ (j + 1)) (hF.atQ (j + 1)).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₂)
  have m₁ := l₁ _ v₁
  have m₂ := l₂ (by omega) _ v₂
  rw [← (ht.sBF j (σ + 1) h).1] at m₁
  rw [← (ht.sFB j σ h).1] at m₂
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun y => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ y (rTrans q₂ f))
    (hand_mul_right (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) k b hb m₁ m₂ g q₁ q₂)

end GlobalTheory.DStepLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PlaceIdemUniq

theorem idemAt_unique_orth : ∀ (D : D7) (a b : AE D) (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt a PP → Formalism.L2.NTheta.IsIdemAt b PP' → (PP = PP' → a = b) ∧ (PP ≠ PP' → a * b = 0) := by
  intro D a b PP PP' ha hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split ha) ha hb
  · exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split ha) ha hb h

end GlobalTheory.PlaceIdemUniq
end

