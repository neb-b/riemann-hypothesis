module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientEqConstMulLowestKTypeCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOneCombSphLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.SphOne

theorem isOneComb_sph_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), L.J = KO k _ → (∀ j, L.lam j = 1) → IsOneComb ψ ν P L 1 (Finsupp.single 1 1) ∧ prX (Cgrp L.J 1) = KO k n := by
  intro k _ _ _ _ _ _ n _ _ c P h1 h2 ψ _ hψ ν hν L hJ hlam
  obtain ⟨J, lam⟩ := L
  dsimp only at hJ hlam
  subst hJ
  have e : lam = 1 := MonoidHom.ext fun j => hlam j
  subst e
  refine ⟨?_, GlobalTheory.QPl.PinTest.prX_KO⟩
  exact GlobalTheory.QPl.PinTest.isOneComb_sph hψ hν h1 h2

end GlobalTheory.QPl.SphOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorSplitPlaceLatticeIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIdemVac

variable {D : D7}

theorem latO_at_le {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (v : Pl D) : latO S T LS LT (· = v) ≤ latO S T LS LT fun _ => True := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun _ h => absurd trivial h, rest⟩

theorem pairA_zero_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem placeIdem_mul_mem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    (Matrix.of fun i j => algebraMap (AF D.host.F) (AE D) ε * u i j : WO S T) ∈ latO S T LS LT (· = v) := by
  obtain ⟨α₀, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α₀ * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul]
      by_cases hwv : w = v
      · subst hwv; rw [h1, one_mul]; exact hα w
      · rw [h0 w hwv, zero_mul]; exact zero_mem _
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      simp only [Matrix.of_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, pairA_zero_mul]
  | zero =>
    convert (latO S T LS LT (· = v)).zero_mem using 1
    ext i j; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
  | neg x _ hx =>
    convert neg_mem hx using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]

theorem splitIdem_mul_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} (LS : Lat S) (LT : Lat T) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    u.map (fun a => q.e * a) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have h := (GlobalTheory.SplitVac.idem_latO D k q S T LS LT _ (placeIdem_mul_mem _ _ hε hu)).1
  convert h using 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← hsum, ← mul_assoc, mul_add, q.split.1, q.split.2.1, add_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def tensorWith (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ Ψ
  map_add' Φ Φ' := by
    funext t
    simp only [Place.tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [Place.tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorWith_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) (Φ : WO S T → ℂ) :
    tensorWith p FS FT Ψ Φ = p.tensorAt FS FT Φ Ψ := rfl

theorem tensorAt_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorAt FS FT (fun t => Φ (t + x)) Ψ = fun t => p.tensorAt FS FT Φ Ψ (t + x) := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, GlobalTheory.LocMod.TOneModel.down_half_zero p FS FT he hx, add_zero,
    sub_add_eq_add_sub]

theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorAt FS FT (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]


open Classical in
theorem tensorAt_halfInd (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Λ Λv : AddSubgroup (WO S T)) (hle : Λv ≤ Λ) (hstab : ∀ t ∈ Λ, t.map (fun a => p.e * a) ∈ Λv) :
    p.tensorAt FS FT ((1 : ℂ) • halfInd e Λ) (Set.indicator {x | p.up FS FT x ∈ Λv} fun _ => 1) =
      (1 : ℂ) • halfInd (e + p.e) Λ := by
  funext t
  simp only [one_smul, Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t, Set.indicator_apply]
  simp only [Set.mem_setOf_eq, GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ Λ ∧ IsHalf e (t - M)) ∧ M ∈ Λv) ↔ (t ∈ Λ ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 (hle h3), fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λv := hstab t h1
      refine ⟨⟨sub_mem h1 (hle h3), fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λv
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

theorem isPlaceModel_tensorLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  intro D ψ S T M M' hM hM' P e he f₀ T' hT'
  set p := ofSplit P.q with hp
  set Ψ : Matrix P.Y P.Y' P.k → ℂ :=
    Set.indicator {x | p.up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1 with hΨ
  have hpe : p.e = P.q.e := rfl
  have he' : e * p.e = 0 := he
  have hΨsb : Ψ ∈ SB (Matrix P.Y P.Y' P.k) := _root_.GlobalTheory.LatIndSB.indicator_latO_mem_SB D ψ S T M M' hM hM' P
  have hsb : ∀ Φ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ →
      IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (p.tensorAt P.FS P.FT Φ Ψ) :=
    fun Φ hΦ => _root_.GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO D ψ S T M M' hM hM' P e he Φ hΦ Ψ hΨsb
  refine ⟨T' ∘ₗ tensorWith p P.FS P.FT Ψ, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ => rfl⟩
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_trans p P.FS P.FT he' Φ Ψ hx]
    exact hT'.trans _ (hsb Φ hΦ) x (GlobalTheory.LocMod.TOneModel.half_sum p he' hx)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_modul p ψ P.FS P.FT he' Φ Ψ hy]
    exact hT'.modul _ (hsb Φ hΦ) y (GlobalTheory.LocMod.TOneModel.half_sum_conj p he' hy)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_halfInd p P.FS P.FT he' _ _ (latO_at_le _ _ P.q.v)
      (fun t ht => splitIdem_mul_mem P.q M M' ht)]
    exact hT'.vac

end GlobalTheory.LatIdemVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀) (h : GA D B.A), flatFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flatFB s Ψ) := by
  first | exact @GlobalTheory.Unf.FlatComm.flatFB_om | exact GlobalTheory.Unf.FlatComm.flatFB_om | (intros; apply GlobalTheory.Unf.FlatComm.flatFB_om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

noncomputable section

namespace GlobalTheory.FockCoefReal

theorem l2_self_eq_setIntegral_norm_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (f : X → ℂ) :
    l2 μ 𝓧 f f = ((∫ w in 𝓧, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = _
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem fockIp_eq_fock {ι : Type} (P Q : MvPolynomial ι ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P Q = Formalism.E.fock P Q := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp, Formalism.E.fock, Formalism.A.mfact, starRingEnd_apply]


set_option maxHeartbeats 1000000 in
theorem fock_coef_real : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W), l2 μ 𝓧 (ω (1, realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w))) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) = Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ * l2 μ 𝓧 f f := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv g hg e e' w w'
  obtain ⟨hf0, hfth, hcartV, hvac⟩ := _root_.GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv
  obtain ⟨hCore, -, hEmb, -, -, hW, hBW, -, hPt, hc, hIo⟩ := hL
  have hm := hCore.models
  have hθ : IsInfFam R.θ := hm.inf
  have hlab := _root_.GlobalTheory.LabAtRealPlace.main D σ s hEmb
  obtain ⟨hHol, hWt, hε⟩ := _root_.GlobalTheory.HolLabel.holShape_signs_first D σ hlab i (R.MW i σ)
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f
  have hpt : ptAt R i σ BW f = ⇑pt := rfl
  have hptTh : ∀ Q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pt Q) := hPt
  have hpq : ∀ τ, pW D i τ + qW D i τ ≤ (Vc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e2 := Formalism.IndefR.FWT.rank_Wc i
    have e3 := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW, qW]
    omega
  have hpW : ∀ τ, pW D i τ ≤ (Wc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW]
    omega
  have hharm := fun τ => _root_.GlobalTheory.MinorHarmonic.laplacian_delta D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  have hkill := _root_.GlobalTheory.FockKillAdapted.killed_of_harmonic_adapted D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) (pW D i) hε BW hBW f hfth hvac (deltaAtEmb D i σ) hharm
  have hee := _root_.GlobalTheory.RawLift.FockPair.coef_one_vector D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) hHol hWt μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hkill
  have hww := _root_.GlobalTheory.CoefSchur.thetaLiftPairing_lowestWeight_schur_polarisation_alt D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hee g hg e e' w w'
  have hip := GlobalTheory.FockIsometry.ipO_pureTensorO D R.ψ R.θ (Vc D i) (Wc D i) hW.std hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW (fun _ => (Vc D i).rank) (pW D i) (fun _ => le_rfl) hpW hcartV
    (fun ρ => GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ) ρ) (hm.BV i) hBW f hfth hvac μ 𝓧 hcv
    (deltaAtEmb D i σ) (deltaAtEmb D i σ)
  have hΔ : l2 μ 𝓧 (pt (deltaAtEmb D i σ)) (pt (deltaAtEmb D i σ)) =
      Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * l2 μ 𝓧 f f := by
    rw [l2_self_eq_setIntegral_norm_sq μ 𝓧 f, ← fockIp_eq_fock]
    exact hip
  rw [hpt, hww, hΔ]
  ring

end GlobalTheory.FockCoefReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastDbl

variable {D : D7}

theorem ker_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (a : ℂ) (C : WO A S → WO S X → ℂ) (h₀ : GA D A)
    (h₁ : GA D S) (h₂ : GA D X) :
    GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ = a * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂ := by
  unfold GlobalTheory.SeeSmallPf.ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (a • C) u v) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : (fun u => (a • C) u v) = a • fun u => C u v := by
      funext u; simp only [Pi.smul_apply]
    rw [e, map_smul]; simp only [Pi.smul_apply]
  rw [e1, map_smul]; simp only [Pi.smul_apply, smul_eq_mul]

theorem biLift_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ (a • C) h₂ = a * biLift oma omX vA vS φ C h₂ := by
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  have e : ∀ h₀ h₁, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ =
      a * (φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂) := fun h₀ h₁ => by rw [ker_smul]; ring
  simp only [e, integral_const_mul]

theorem theta_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (a • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w)) }

theorem sum_fin {G M : Type} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  intro D c v t hc ht hW j h Y hY φ hφ
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X j) := (hc.x j (by omega)).cpt
  have hS : CoCpt (c.X (j + 1)) := (hc.x (j + 1) (by omega)).cpt
  have hτ := (hW.tau j h).2
  obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hc.std
  have hY' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Y ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Y).2 hY
  have hC : ∀ Z : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ Z →
      IsBiTheta c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y) := by
    intro Z hZ
    have hZ' : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Z := hZ
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero (t.sBF j 0 h) hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
      (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF (t.sBF j 0 h) Z) _ hΞ hY'
  refine ⟨fun X hX f hf => GlobalTheory.SeeSmallPf.outer hB hWa hWX (hC X hX) hA hS hc.cpt (c.x j).vol (c.x (j + 1)).vol c.volT
    (c.oT (j + 1 + 1) h) hφ hf, fun G s a X hX => ?_⟩
  have hsum : ∀ (Z : G → WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • Z g) Y =
      ∑ g ∈ s, a g • c.lst j h (v.τ j h) (t.sBF j 0 h) (Z g) Y := by
    intro Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hsm : ∀ (b : ℂ) (Z : WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (b • Z) Y =
      b • c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y := by
    intro b Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Pi.smul_apply, smul_eq_mul]
    ring
  funext h₂
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ g, a g * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) h₂ =
      c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (a g • X g) Y) h₂ := fun g => by
    rw [hsm]; exact (biLift_smul _ _ _ _ _ _ _ _).symm
  simp only [e1]
  rw [sum_fin s, sum_fin s]
  have e2 : (∑ i : Fin s.card, a (s.equivFin.symm i) • c.lst j h (v.τ j h) (t.sBF j 0 h) (X (s.equivFin.symm i)) Y) =
      ∑ i : Fin s.card, c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y :=
    Finset.sum_congr rfl fun i _ => (hsm _ _).symm
  rw [e2]
  exact (GlobalTheory.SeeSmallPf.biLift_sum hB hWa hWX hA hS (c.x j).vol (c.x (j + 1)).vol hφ
    (fun i => c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y)
    (fun i => hC _ (theta_smul _ (hX _))) h₂).symm

end GlobalTheory.LastDbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem finite_levelPlaces_or_tuplePlaces : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Set.Finite {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} := by
  intro D L hT Gi Gl Kc Yd cX ex W h
  haveI : Finite W.P.T := h.fin
  have hU : {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} =
      ((pk W).Pg : Set (Pl D.host.E)) ∪ ⋃ t, ((pk W).Q t : Set (Pl D.host.E)) := by
    ext PP
    simp [QAll]
  rw [hU]
  exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMap_preimage_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  first | exact @GlobalTheory.HaarR.prodR_preimage_KO | exact GlobalTheory.HaarR.prodR_preimage_KO | (intros; apply GlobalTheory.HaarR.prodR_preimage_KO <;> assumption)
end

