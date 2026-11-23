module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalisedStandardWeylOfLiftMem
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.DelStd

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  omega

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Fin.pos a
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, hn, dif_pos] at *
  omega

theorem linInd_map {σ P : Type} [Fintype P] (K : Type) [Field K] [CharZero K] (b : P → MvPolynomial σ ℤ)
    (hb : LinearIndependent ℤ b) : LinearIndependent K fun i => MvPolynomial.map (Int.castRingHom K) (b i) := by
  classical
  let e := Fintype.equivFin P
  have h1 : LinearIndependent ℤ (b ∘ e.symm) := hb.comp _ e.symm.injective
  have h1' := h1.map' (MvPolynomial.basisMonomials σ ℤ).repr.toLinearMap (LinearEquiv.ker _)
  have h2 := GlobalTheory.LatBC.linInd_mapRange (O := ℤ) (K := K) (P := σ →₀ ℕ) (Int.castRingHom K) (fun _ _ h => Int.cast_injective h) h1'
  have h3 := h2.comp e e.injective
  refine LinearIndependent.of_comp (MvPolynomial.basisMonomials σ K).repr.toLinearMap ?_
  convert h3 using 1
  funext i
  ext m
  have hZ : ∀ f : MvPolynomial σ ℤ, (MvPolynomial.basisMonomials σ ℤ).repr f m = AddMonoidAlgebra.coeff f m := fun _ => rfl
  have hK : ∀ f : MvPolynomial σ K, (MvPolynomial.basisMonomials σ K).repr f m = AddMonoidAlgebra.coeff f m := fun _ => rfl
  simp [hZ, hK, MvPolynomial.coeff_map]

theorem detPol_ne_zero (C : Type) [Field C] (n : ℕ) : detPol C n ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) C

theorem map_detPol {R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (n : ℕ) :
    MvPolynomial.map f (detPol R n) = detPol C n := by
  unfold detPol
  rw [RingHom.map_det]
  congr 1
  ext a s : 2
  simp

theorem linInd_det {P : Type} {C : Type} [Field C] {n : ℕ} (k : ℕ) (b : P → MvPolynomial (Fin n × Fin n) C)
    (hb : LinearIndependent C b) : LinearIndependent C fun i => detPol C n ^ k * b i := by
  have := hb.map' (LinearMap.mulLeft C (detPol C n ^ k)) (LinearMap.ker_eq_bot.2
    (mul_right_injective₀ (pow_ne_zero k (detPol_ne_zero C n))))
  exact this

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_sum {C : Type} [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {P : ι → Type} [∀ τ, Fintype (P τ)]
    (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) C) (a : ∀ τ, P τ → C) :
    (ten fun τ => ∑ j, a τ j • u τ j) = ∑ i : ∀ τ, P τ, (∏ τ, a τ (i τ)) • ten fun τ => u τ (i τ) := by
  unfold ten
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_smul]

theorem map_map_int {σ R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (b : MvPolynomial σ ℤ) :
    MvPolynomial.map f (MvPolynomial.map (Int.castRingHom R) b) = MvPolynomial.map (Int.castRingHom C) b := by
  rw [MvPolynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom C)]

theorem latD_coords {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (lamW : ι → ℕ → ℕ) (F : Frame l ι n)
    (hF : ∀ x : F.O, ‖F.emb x‖ ≤ 1) {P : ι → Type} [∀ τ, Fintype (P τ)] (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l))
    (hu : ∀ τ, ∀ x0 ∈ weyl F.O n n le_rfl (res n (lamW τ)), ∃ a : P τ → F.O,
      MvPolynomial.map F.emb x0 = ∑ j, F.emb (a j) • u τ j)
    {z : NablaT (PadicAlgCl l) n lamW} (hz : z ∈ F.latD lamW) :
    ∃ r : (∀ τ, P τ) → PadicAlgCl l, (∀ i, ‖r i‖ ≤ 1) ∧
      mulMap (PadicAlgCl l) n lamW z = ∑ i, r i • ten fun τ => u τ (i τ) := by
  unfold Frame.latD at hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, x, hx, rfl⟩ := hy
    choose x0 hx0 hx1 using hx
    choose a ha using fun τ => hu τ (x0 τ) (hx0 τ)
    refine ⟨fun i => F.emb c * ∏ τ, F.emb (a τ (i τ)), fun i => ?_, ?_⟩
    · beta_reduce
      rw [← map_prod, ← map_mul]; exact hF _
    · rw [map_smul, mulMap_tprod]
      have : (fun τ => (x τ : MvPolynomial (Fin n × Fin n) (PadicAlgCl l))) = fun τ => ∑ j, F.emb (a τ j) • u τ j := by
        funext τ; rw [← hx1, ha]
      rw [this, ten_sum u fun τ j => F.emb (a τ j), Finset.smul_sum]
      simp only [smul_smul]
  | zero => exact ⟨0, fun i => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨s, hs, hy⟩ := hy
    refine ⟨r + s, fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr i) (hs i)), ?_⟩
    rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_smul]
  | neg x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    refine ⟨-r, fun i => by simpa using hr i, ?_⟩
    rw [map_neg, hx, ← Finset.sum_neg_distrib]
    simp only [Pi.neg_apply, neg_smul]

theorem smul_mem_locP {K M : Type} [Field K] [NumberField K] [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) M) (x : M) (a : K) (s t : 𝓞 K)
    (hs : s ∉ w.asIdeal) (hst : (s : K) * a = t) (hx : x ∈ L) : a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  refine ⟨s, hs, ?_⟩
  have h1 : s • a • x = t • x := by
    rw [← algebraMap_smul K s, ← algebraMap_smul K t, smul_smul]
    exact congrArg (· • _) hst
  rw [h1]
  exact L.smul_mem _ hx

theorem mem_localization_standardWeylLattice : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → (∀ x : F.O, ‖F.emb x‖ ≤ 1) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, Φ v ∈ F.latD lamW → (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ l _ w e0 ι _ _ n lam lamW c F Φ hw hF hS hΦ v hv
  classical
  choose P fP b hb hspan hdual using fun τ => _root_.GlobalTheory.WeylBasis.exists_weyl_basis n (lam τ).natW (natW_anti (lam τ))

  let bK : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) K := fun τ i => MvPolynomial.map (Int.castRingHom K) (b τ i)
  let u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l) := fun τ i =>
    detPol (PadicAlgCl l) n ^ lamW τ (n - 1) * MvPolynomial.map (Int.castRingHom (PadicAlgCl l)) (b τ i)
  have hKspan := (tensorBasis K K ι n n P (fun τ => nablaSq K n (lam τ)) bK (fun τ => linInd_map K _ (hb τ))
    (fun τ => (hdual τ K).symm)).2
  have huind := (tensorBasis (PadicAlgCl l) (PadicAlgCl l) ι n n P _ u
    (fun τ => linInd_det _ _ (linInd_map (PadicAlgCl l) _ (hb τ))) (fun τ => rfl)).1
  have hbK : ∀ τ i, bK τ i ∈ nablaSq K n (lam τ) := fun τ i => by
    unfold nablaSq
    rw [hdual τ K]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i : ∀ τ, P τ, (ten fun τ => bK τ (i τ)) ∈ VV K lam := fun i =>
    Submodule.subset_span ⟨_, fun τ => hbK τ (i τ), rfl⟩
  have hv0 : (v : Pol K ι n) ∈ Submodule.span K (Set.range fun i : ∀ τ, P τ => ten fun τ => bK τ (i τ)) := by
    have h2 : (v : Pol K ι n) ∈ tensorLat K K fun τ => nablaSq K n (lam τ) := v.2
    rw [← hKspan] at h2
    exact h2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv0
  have hveq : v = ∑ i, a i • (⟨_, hmem i⟩ : VV K lam) := by
    apply Subtype.ext
    rw [← ha]
    simp
  have hΦi : ∀ i, mulMap (PadicAlgCl l) n lamW (Φ ⟨_, hmem i⟩) = ten fun τ => u τ (i τ) := fun i => by
    obtain ⟨y, hy, hyΦ⟩ := hΦ (fun τ => bK τ (i τ)) ⟨_, hmem i⟩ (fun τ => hbK τ (i τ)) rfl
    rw [hyΦ, mulMap_tprod]
    congr 1
    funext τ
    rw [hy, liftPol, map_map_int]
  have hΦv : mulMap (PadicAlgCl l) n lamW (Φ v) = ∑ i, e0 (a i) • ten fun τ => u τ (i τ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hveq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, hΦi]
  obtain ⟨r, hr, hrv⟩ := latD_coords lamW F hF u (fun τ x0 hx0 => by
    rw [res_eq hS τ, _root_.GlobalTheory.WeylShift.mem_weyl_add] at hx0
    obtain ⟨g, hg, rfl⟩ := hx0
    rw [hspan τ F.O] at hg
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F.O).1 hg
    refine ⟨d, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_pow, map_detPol, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [u, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_map_int]
    ring) hv
  have hra : ∀ i, e0 (a i) = r i :=
    (Fintype.linearIndependent_iffₛ.1 huind) (fun i => e0 (a i)) r (hΦv.symm.trans hrv)
  rw [← ha]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨s, hs, t, hst⟩ := (_root_.GlobalTheory.FrameRead.norm_le_one_iff_integral_at K l w e0 hw (a i)).1 (hra i ▸ hr i)
  refine smul_mem_locP w _ _ _ s t hs hst (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
  refine ⟨MvPolynomial.map (Int.castRingHom (𝓞 K)) (b τ (i τ)), ?_, ?_⟩
  · unfold delSq
    rw [hspan τ (𝓞 K)]
    exact Submodule.subset_span ⟨_, rfl⟩
  · exact map_map_int (algebraMap (𝓞 K) K) _

end GlobalTheory.FrameRead.DelStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumNegHomEqStandardPairFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

namespace GlobalTheory.BotMove.Fst

private theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

private theorem placeModel_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) (c : ℂ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) (c • Tm) := by
  have hs : ∀ x (F : WO S T → ℂ), heisO ψ S T x (c • F) = c • heisO ψ S T x F := fun x F => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.trans Φ hΦ x hx]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.modul Φ hΦ y hy]
  · rw [LinearMap.smul_apply, h.vac]

private theorem thetaAt_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ Φ f : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ (c⁻¹ • f) := by
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := h
  refine ⟨⟨c⁻¹ • T₀, ?_⟩, fun T' hT' => ?_⟩
  · have := placeModel_smul hT₀ c⁻¹
    rwa [inv_smul_smul₀ hc] at this
  · have e1 : f = (c • T') Φ := hall _ (placeModel_smul hT' c)
    show c⁻¹ • f = T' Φ
    rw [e1, LinearMap.smul_apply, inv_smul_smul₀ hc]

private theorem thetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ')
    (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : GlobalTheory.FinPl.Moves S b Λ M (fun _ => True))
    (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' (fun _ => True)) {e : AE D} {Φ f₀ f : WO S T → ℂ} (hee : e * e = e)
    (hinf : infPart D e = 0) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀)
      (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

private theorem frMapO_move {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : GA D S) (h : GA D T) (x : WO S T) :
    frMapO S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have e1 : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((Lev.finE T h)⁻¹).val := by
    rw [← map_inv]; rfl
  have e2 : (Formalism.L2.Theta.mt S g).map (toEAf D) = (Lev.finE S g).val := rfl
  rw [frMapO, frMapO, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, e1, e2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem stdFst_move {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) :
    stdFst ν e I S T (Lev.finE S g * βS) (Lev.finE T h * βT) = fun x => stdFst ν e I S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  funext x
  unfold stdFst
  rw [frMapO_move, GlobalTheory.SchrMove.isHalf_actO_iff g⁻¹ h⁻¹ x]

end GlobalTheory.BotMove.Fst

theorem _root_.GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) (latO (neg A) WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac
    (stdFst (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA _ hW g _ g' _ h _ mA _ mW t₀ r r' hr hv _ t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hY.idem t)
  have mA' : GlobalTheory.FinPl.Moves (neg A) ((ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mA
  have h1 := GlobalTheory.BotMove.Fst.thetaAt_move (S := neg A) (hY.weil t) (GlobalTheory.BotMove.Fst.selfDual_neg hY.rigA.1)
    (GlobalTheory.BotMove.Fst.selfDual_neg hA) hY.rigW.1 hW mA' mW ho.idem ho.infPart_eq hY.isVac.2.theta (hY.fst t)
  have e1 : ∀ F, (Y.ω t).toSgn true ((ofSgn true A).symm g, h) F = Y.ω t (g, h) F := fun F => rfl
  rw [e1, e1, hv t] at h1
  have h2 := GlobalTheory.BotMove.Fst.thetaAt_smul (hr t).1 h1
  have e2 := GlobalTheory.BotMove.Fst.stdFst_move (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β g h
  show IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (Y.e t) (latO (neg A) WW ΛA ΛW fun _ => True) 1 (Y.ω t₀ (g, h) Y.vac)
    (stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW (Lev.finE A g * Y.rA.β) (Lev.finE WW h * Y.rW.β))
    ((r t)⁻¹ • Y.ω t (g, h) (Y.f t))
  rw [e2]
  exact h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumHomEqVacuumMovedLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem _root_.GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac' := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW _ hΛA' hΛW g _ g' hg' h hh _ mA' mW t₀ r r' _ _ _
  have hW : IsWeilDatumO ψ A' WW _ _ (Y.ω' t₀) := hY.weil' t₀
  have hvac : IsVacO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ Y.vac' := hY.isVac'
  have hθ : IsInfFam θ := hvac.2.inf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hY.rigA'.1 hΛA' hY.rigW.1 hΛW mA' mW
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hΛA' hY.rigA'.1 hΛW hY.rigW.1 (GlobalTheory.VacMove.moves_inv mA')
    (GlobalTheory.VacMove.moves_inv mW)
  show IsVacO ψ θ A' WW Y.rA'.s Y.rW.s ΛA' ΛW (Y.ω' t₀ (g', h) Y.vac')
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ A' WW _ _ (Y.ω' t₀) hW hθ Y.rA'.s Y.rA'.s Y.rW.s Y.rW.s _ _ _ _ g' h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨_, (key' u).1 hu, ?_⟩, ?_⟩) Y.vac' hvac
  · have e := GlobalTheory.WeilVacMove.actO_inv_actO g'⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at e
    exact e.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    exact (key u₀).1 hu₀
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponent
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt.PtExist

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) :=
  GlobalTheory.DefPt.Model.nonempty_ptData_all

end GlobalTheory.DefPt.PtExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvectionStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictLower_mem_closure_transvection' : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.one_add_strictLower_mem_closure_transvection | exact GlobalTheory.one_add_strictLower_mem_closure_transvection | (intros; apply GlobalTheory.one_add_strictLower_mem_closure_transvection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvectionStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictUpper_mem_closure_transvection : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.UpperTransvection.upper_mem_closure | exact GlobalTheory.UpperTransvection.upper_mem_closure | (intros; apply GlobalTheory.UpperTransvection.upper_mem_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosedStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandardStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral_standard : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  first | exact @GlobalTheory.TwistClassScalar.twist_class_scalar | exact GlobalTheory.TwistClassScalar.twist_class_scalar | (intros; apply GlobalTheory.TwistClassScalar.twist_class_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroupStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_up_to_target_group : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k₁ a₁ → IsTransp p r i v ψ γ k k₂ a₂ → k₁ = k₂ ∧ a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  first | exact @GlobalTheory.ShareOn.IsTransp.uniq | exact GlobalTheory.ShareOn.IsTransp.uniq | (intros; apply GlobalTheory.ShareOn.IsTransp.uniq <;> assumption)
end

