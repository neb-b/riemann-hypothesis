module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatRowTestOfExField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.RowClaim

namespace GlobalTheory.Twist

theorem atDat_rowTest_of_exField : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → GlobalTheory.RowEx.ExField → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun hG hC h1 h2 h3 h4 h5 h6 h7 hE => GlobalTheory.Mem.R3.Rw.RowAt.atDat_rowTest hG hC h1 h2 h3 h4 h5 h6 h7 hE

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreLatticeMeetsLineOfZIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ZLineIdeal

open GlobalTheory.SeeSaw

theorem idLat_span_singleton {D : D7} (L : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (ζ : Fin L.rank → D.host.E) :
    idLat I (Submodule.span (𝓞 D.host.E) {ζ}) = LiftModel.lineLat L ζ I := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    refine ⟨c • s, (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem c hs, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
    rw [smul_assoc, smul_comm]
  · rintro _ ⟨s, hs, rfl⟩
    apply Submodule.subset_span
    exact ⟨s, hs, ζ, Submodule.mem_span_singleton_self ζ, by simp⟩

theorem lineLat_smul {D : D7} (L : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (ζ : Fin L.rank → D.host.E) {c : D.host.E} (hc : c ≠ 0) :
    LiftModel.lineLat L (c • ζ) (FractionalIdeal.spanSingleton _ c⁻¹ * I) = LiftModel.lineLat L ζ I := by
  ext y
  simp only [LiftModel.lineLat, Submodule.mem_map, LinearMap.coe_restrictScalars,
    LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe]
  have e : ∀ x : D.host.E, c⁻¹ * x * c = x := fun x => by field_simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hx
    refine ⟨x', hx', ?_⟩
    rw [smul_smul, e]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ * x, (FractionalIdeal.mem_singleton_mul).2 ⟨x, hx, rfl⟩, ?_⟩
    rw [smul_smul, e]

end GlobalTheory.ZLineIdeal


open GlobalTheory.SeeSaw in
theorem GlobalTheory.ZLineIdeal.bessel_core_lattice_meets_line_of_z_ideal : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), GlobalTheory.SeeSaw.LineId (F.oB ρ h) (F.ζ (ρ + 1)) (lat0 F ρ h) (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹)) v := by
  have H0 := @_root_.GlobalTheory.AscFin.GridLat.lattices_grid
  unfold OnStd All at H0 ⊢
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v
  have H := (H0 D hoff T L μ0 hL sc G W M hM F hF).2.1 ρ h
  have hx : ((-D.host.xi0) ^ (ρ + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have hζ : F.ζ (ρ + 1) ≠ 0 := by
    intro e
    have := (F.line (ρ + 1)).2
    rw [e] at this
    simp at this
  have eL : LiftModel.lineLat (negSp F.Lz) (F.ζ (ρ + 1))
      (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹)) =
      idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    rw [GlobalTheory.ZLineIdeal.idLat_span_singleton (negSp F.Lz), hF.ζ (ρ + 1), GlobalTheory.ZLineIdeal.lineLat_smul _ _ _ hx]
  refine LiftModel.lineId_of_split (F.oB ρ h) (F.ζ (ρ + 1)) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) _ _ v
    (LiftModel.lineLatAt_lineLat _ hζ _ v) ?_
  rw [eL]
  exact H.2.2.2 v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWitt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TgtCoreSplit

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem toEAf_pure (e : D.host.E) :
    toEAf D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  unfold toEAf
  rw [RingHom.comp_apply, finPart_pure]
  rfl

theorem rat_mulVec_pure {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (α : Af D.host.F) (t : Fin n → D.host.E) :
    rat M *ᵥ (fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] t i) =
      fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (M *ᵥ t) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, MonoAt d L L₀ v)
    {t : Fin S.rank → D.host.E} (ht : t ∈ L) : (d.i₀ * d.q0) *ᵥ t ∈ L := by
  have hy : (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i) ∈ latV S L (fun _ => True) :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, fun v hv => (hv trivial).elim, 1, rfl, t, ht, by
      funext i; rw [one_mul]⟩
  have h2 := GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hL (fun v _ => hm v)
    (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ (fun v _ => hm v) hy)
  have e : d.j0 *ᵥ (d.p0 *ᵥ (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i)) =
      fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((d.i₀ * d.q0) *ᵥ t) i := by
    rw [Matrix.mulVec_mulVec, show d.j0 * d.p0 = rat (d.i₀ * d.q0) by rw [rat_mul]; rfl]
    exact rat_mulVec_pure _ _ _
  rw [e] at h2
  have h3 := (GlobalTheory.Core.Mi.LatMatch.TraceX.latV_iff_hatL S L _ _ (GlobalTheory.FinPlLoc.latV_idAt h2)).1 h2
  simp only [toEAf_pure] at h3
  exact (GlobalTheory.Mem.Col2.PtUniq.mem_iff_hatL (F := D.host.F) hL _).2 h3

theorem mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : rat M * u ∈ latO S T LS (LT : Set _) P := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply]
    generalize (∑ k, star (s k) * S.gram k j) = c
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') :
    M * x ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hy z hz)
  · rw [Matrix.mul_add]; exact add_mem ha hb

theorem mul_mem_hatMx {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin m) (Fin m) D.host.E) (hM : ∀ x ∈ N, M * x ∈ N) {u : Mx D m n} (hu : u ∈ hatMx N) :
    rat M * u ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.TgtCoreSplit


open GlobalTheory.TgtCoreSplit in
theorem GlobalTheory.AscFin.latRow_bessel_core_split : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h w hw
  have hI := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W M hM F hF
  have hm : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((hI.2.1 ρ h).2.1 v).2
  have hL1 : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * ρ + 1) 0) ⟨by omega, Nat.zero_le _⟩).sd.1
  have hL0 : Submodule.IsLattice D.host.E (G.Λ (.core (2 * ρ + 1))) :=
    (node_isV G hL (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega)).sd.1
  have hP : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) *ᵥ t ∈ G.Λ (.grid (2 * ρ + 1) 0) :=
    fun t ht => proj_mem _ hL1 hL0 hm ht
  have e : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 * w)) =
      rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, rat_mul]
    show (F.dJ ρ h).j0 * ((F.dJ ρ h).p0 * w) * (F.dB ρ h).p0 = (F.dJ ρ h).j0 * (F.dJ ρ h).p0 * (w * (F.dB ρ h).p0)
    simp only [Matrix.mul_assoc]
  have hw' : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T))) := hw
  rw [e]
  show (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T)))
  refine ⟨mul_mem_latO _ hP hw'.1, fun a ha => ?_⟩
  rw [← Matrix.mul_smul]
  exact mul_mem_hatMx _ _ (fun x hx => mul_mem_smul_homLat _ _ hP hx) (hw'.2 a ha)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWitt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem tmul_mul_rat {m n k : ℕ} (c : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (π : Matrix (Fin n) (Fin k) D.host.E) :
    (Matrix.of fun i j => c ⊗ₜ[D.host.F] x i j : Mx D m n) * rat π = Matrix.of fun i j => c ⊗ₜ[D.host.F] (x * π) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (c ⊗ₜ[D.host.F] x i l) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π l j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_rat_mem_hatMx {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (π : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ M, x * π ∈ M) {w : Mx D m n} (hw : w ∈ hatMx M) :
    w ⬝ rat π ∈ hatMx M := by
  let g : Mx D m n →+ Mx D m n :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : hatMx M ≤ (hatMx M).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    show (_ : Mx D m n) ⬝ rat π ∈ hatMx M
    rw [tmul_mul_rat]
    exact AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, rfl⟩
  exact hle hw

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (LS : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (π : Matrix (Fin n) (Fin n) D.host.E)
    (hπ : ∀ y ∈ LS, π *ᵥ y ∈ LS) : ∀ x ∈ I • homLat LS LT, x * π ∈ I • homLat LS LT := by
  let f : Matrix (Fin m) (Fin n) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin m) (Fin n) D.host.E :=
    { toFun := (· * π), map_add' := fun a b => Matrix.add_mul a b π, map_smul' := fun r a => Matrix.smul_mul r a π }
  have hH : (homLat LS LT).map f ≤ homLat LS LT := by
    rintro _ ⟨x, hx, rfl⟩ y hy
    show (x * π) *ᵥ y ∈ LT
    rw [← Matrix.mulVec_mulVec]
    exact hx _ (hπ y hy)
  intro x hx
  have h1 : f x ∈ (I • homLat LS LT).map f := ⟨x, hx, rfl⟩
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hH h1

theorem mul_rat_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : GlobalTheory.FinPl.Pl D → Prop) (π π' : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hadj : S.gram * π = π'ᴴ * S.gram)
    (hπ' : ∀ s ∈ LS, π' *ᵥ s ∈ LS) {u : Mx D T.rank S.rank} (hu : u ∈ latO S T LS LT P) :
    u ⬝ rat π ∈ latO S T LS LT P := by
  let g : Mx D T.rank S.rank →+ Mx D T.rank S.rank :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : latO S T LS LT P ≤ (latO S T LS LT P).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    show (_ : Mx D T.rank S.rank) ⬝ rat π ∈ latO S T LS LT P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, π' *ᵥ s, hπ' s hs, t, ht, ?_⟩
    have e := tmul_mul_rat (pairA D.host.F 0 α) (Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j) π
    simp only [Matrix.of_apply] at e
    rw [e]
    ext i j
    simp only [Matrix.of_apply]
    congr 1
    have e1 : ∀ v : Fin S.rank → D.host.E, ∀ l, ∑ k, star (v k) * S.gram k l = (star v ᵥ* S.gram) l := fun v l => rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, e1]
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← hadj, ← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact hle hu

end GlobalTheory.AscFin.SrcSplit

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D,
      (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) (s : Fin S.rank → D.host.E) (hs : s ∈ L) :
    (d.e * d.qX) *ᵥ s ∈ L ∧ (d.e' * d.qY) *ᵥ s ∈ L := by
  have key : ∀ v, (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] s i) ∈ latV S L (· = v) := fun v =>
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s, hs,
      by funext k; rw [one_mul]⟩
  have split : ∀ (c : AF D.host.F) {k : ℕ} (e : Matrix (Fin S.rank) (Fin k) D.host.E)
      (q : Matrix (Fin k) (Fin S.rank) D.host.E),
      (fun i => c ⊗ₜ[D.host.F] ((e * q) *ᵥ s) i) =
        ∑ i, GlobalTheory.FinPl.colMul (rat e) i ((rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i)) i) := by
    intro c k e q
    rw [← rat_mulVec_tmul, rat_mul, ← Matrix.mulVec_mulVec]
    generalize rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i) = w
    funext l
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).1 i
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).2.1 i

theorem mem_of_proj {m : ℕ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A : AddSubgroup (Mx D m S.rank))
    (hA : ∀ w ∈ A, w ⬝ rat (d.e * d.qX) ∈ A ∧ w ⬝ rat (d.e' * d.qY) ∈ A) (u : Mx D m S.rank) (hu : u ∈ A) :
    u ⬝ d.jX ⬝ d.pX ∈ A ∧ u ⬝ d.jY ⬝ d.pY ∈ A ∧ u ⬝ d.j0 ⬝ d.p0 ∈ A := by
  have eX : d.jX ⬝ d.pX = rat (d.e * d.qX) := by rw [rat_mul]; rfl
  have eY : d.jY ⬝ d.pY = rat (d.e' * d.qY) := by rw [rat_mul]; rfl
  have e0 : d.j0 ⬝ d.p0 = 1 - d.jX ⬝ d.pX - d.jY ⬝ d.pY := by
    rw [← d.sum_eq_one]; abel
  obtain ⟨hX, hY⟩ := hA u hu
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, eX]; exact hX
  · rw [Matrix.mul_assoc, eY]; exact hY
  · rw [Matrix.mul_assoc, e0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, eX, eY]
    exact sub_mem (sub_mem hu hX) hY

theorem adj_X {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e * d.qX) = (d.e' * d.qY)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e * (d.e'ᴴ * S.gram)) = (d.e' * (d.eᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem adj_Y {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e' * d.qY) = (d.e * d.qX)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e' * (d.eᴴ * S.gram)) = (d.e * (d.e'ᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

end GlobalTheory.AscFin.SrcSplit


open GlobalTheory.AscFin.SrcSplit in
theorem GlobalTheory.AscFin.srcSplit_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hLμ sc G W M hM F hF ρ h u hu
  obtain ⟨-, H2, -⟩ := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hLμ sc G W M hM F hF
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((H2 ρ h).2.1 v).1
  have hin : Node.InRange D.R.m (.grid (2 * ρ + 2) 0) := ⟨h, Nat.zero_le _⟩
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV hin (fun j hj => by injection hj with h1; omega)).sd
  have hP := proj_mem (F.dB ρ h) (_root_.GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all hsd) hmono
  have memR : ∀ w : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, w ∈ latRow G (2 * ρ + 1) → ∀ π π' : Matrix (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E,
      (negSp (G.V (.grid (2 * ρ + 2) 0))).gram * π = π'ᴴ * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π' *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      w ⬝ rat π ∈ latRow G (2 * ρ + 1) := by
    intro w hw π π' hadj hπ' hπ
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨mul_rat_mem_latO (negSp (G.V (.grid (2 * ρ + 2) 0))) _ _ _ _ π π' hadj hπ' hw1, fun e he => ?_⟩
    rw [← Matrix.smul_mul]
    exact mul_rat_mem_hatMx _ π (mul_mem_smul_homLat _ _ _ π hπ) (hw2 e he)
  exact mem_of_proj (F.dB ρ h) (latRow G (2 * ρ + 1))
    (fun w hw => ⟨memR w hw _ _ (adj_X (F.dB ρ h)) (fun s hs => (hP s hs).2) (fun s hs => (hP s hs).1),
      memR w hw _ _ (adj_Y (F.dB ρ h)) (fun s hs => (hP s hs).1) (fun s hs => (hP s hs).2)⟩) u hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  first | exact @GlobalTheory.FlipTop.isSBHalf_topFn | exact GlobalTheory.FlipTop.isSBHalf_topFn | (intros; apply GlobalTheory.FlipTop.isSBHalf_topFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  first | exact @GlobalTheory.ColLatDict.mem_latO_iff_intM | exact GlobalTheory.ColLatDict.mem_latO_iff_intM | (intros; apply GlobalTheory.ColLatDict.mem_latO_iff_intM <;> assumption)
end

