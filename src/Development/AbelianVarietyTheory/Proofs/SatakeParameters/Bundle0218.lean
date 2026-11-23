module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section
open Module

namespace GlobalTheory.NormBC

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem isUnit_of_isUnit_norm {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Free B A]
    [Module.Finite B A] {z : A} (h : IsUnit (Algebra.norm B z)) : IsUnit z := by
  rw [Algebra.norm_apply] at h
  have hu : IsUnit (LinearMap.mul B A z) := (LinearMap.isUnit_iff_isUnit_det _).2 h
  obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
  exact IsUnit.of_mul_eq_one y (by simpa using hy)

end GlobalTheory.NormBC

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def toAlg (L : FinExt l) : Bst P ⊗[ℚ_[l]] (Fin 1 → ↥L.1) ≃ₗ[Bst P] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Bst P) (Bst P))
    (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1)

theorem toAlg_comm (L : FinExt l) (z : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toAlg P L (TensorProduct.comm ℚ_[l] (Fin 1 → ↥L.1) (Bst P) z) = toA P L z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_zero]
  | tmul v b => rfl
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']

theorem linearIndependent_toA {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (b : Basis (Fin d) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) :
    LinearIndependent ↥(MaximalUnramifiedExtension l)
      (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
  have h := b.linearIndependent.map' (((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ
    GlobalTheory.PstRank.toB P ρ) (LinearMap.ker_eq_bot.mpr ((toAlg P L).injective.comp (GlobalTheory.PstRank.toB_injective P ρ)))
  have hf : (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) =
      ⇑(((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) ∘ ⇑b :=
    funext fun i => (toAlg_comm P L _).symm
  rw [hf]
  exact h

end GlobalTheory.Pst.UnitLetter

namespace GlobalTheory.Pst.UnitLetter

open GlobalTheory.NormBC

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_common_fixed {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (hy : ∀ i, y i ∈ Dpst P ρ) :
    ∃ K' : FinExt l, ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' → stRep P ρ g (y i) = y i := by
  suffices h : ∀ s : Finset (Fin d), ∃ K' : FinExt l, ∀ i ∈ s, ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g (y i) = y i by
    obtain ⟨K', hK'⟩ := h Finset.univ
    exact ⟨K', fun i => hK' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨K, by simp⟩
  | insert j s hj ih =>
    obtain ⟨K₁, h₁⟩ := ih
    obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (hy j)
    refine ⟨supExt K₁ K₂, fun i hi g hg => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    · exact h₁ i hi g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)

end GlobalTheory.Pst.UnitLetter


set_option maxHeartbeats 1000000 in
open GlobalTheory.Pst.UnitLetter GlobalTheory.NormBC in
theorem GlobalTheory.Pst.UnitLetter.exists_unit_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  intro l _ P AI hT K L ρm χ hm hpst
  haveI := L.2
  obtain ⟨hdom, hfrac, hline⟩ := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hfd, hrank⟩ := (isPst_iff P ρm).mp hpst
  set d := finrank ℚ_[l] ↥L.1 with hddef
  have hd : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) = d := by
    rw [hrank]; exact (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1).finrank_eq
  let bD := Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) hd
  let y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρm).symm (bD i) : ↥(Dpst P ρm)).1
  have hyD : ∀ i, y i ∈ Dpst P ρm := fun i => ((toUr P ρm).symm (bD i)).2

  obtain ⟨K', hK'⟩ := exists_common_fixed P ρm y hyD
  let w : Fin d → Bst P ⊗[ℚ_[l]] ↥L.1 := fun i => toA P L (y i)
  let G := {g : ↥(GK K) // (g : GQ l) ∈ GK K'}
  let σ : G → (Bst P ⊗[ℚ_[l]] ↥L.1) →+ (Bst P ⊗[ℚ_[l]] ↥L.1) := fun g => AddMonoidHom.mk' (fun z =>
      Algebra.TensorProduct.map (actSt P ((g.1 : ↥(GK K)) : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) z *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g.1)) (fun a b => by simp [map_add (f := _), add_mul])
  have hσ : ∀ (g : G) (b : Bst P) (z : Bst P ⊗[ℚ_[l]] ↥L.1),
      σ g (b • z) = actSt P ((g.1 : ↥(GK K)) : GQ l) b • σ g z := by
    intro g b z
    simp only [σ, AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, mul_assoc]
    congr 1
  have hreg : ∀ b b' : Bst P, b ≠ 0 → (∀ g : G, b * actSt P ((g.1 : ↥(GK K)) : GQ l) b' =
      actSt P ((g.1 : ↥(GK K)) : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b := by
    intro b b' hb h
    obtain ⟨c, -, hc⟩ := hfrac (supExt K K') b b' hb fun g =>
      h ⟨⟨g, GK_le (K' := supExt K K') le_sup_left g.2⟩, GK_le (K' := supExt K K') le_sup_right g.2⟩
    exact ⟨c, hc⟩
  have hv : ∀ (g : G) i, σ g (w i) = w i := by
    intro g i
    simp only [σ, w, AddMonoidHom.mk'_apply]
    rw [← toA_stRep ρm χ hm, hK' i g.1 g.2]
  have hK : LinearIndependent ↥(MaximalUnramifiedExtension l) w := linearIndependent_toA P ρm bD
  have hB : LinearIndependent (Bst P) w := by
    have := GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P)
      (W := Bst P ⊗[ℚ_[l]] ↥L.1)
      (G := G) (fun g => actSt P ((g.1 : ↥(GK K)) : GQ l)) σ hσ hreg w hv Finset.univ
      (hK.linearIndepOn _)
    rw [Finset.coe_univ] at this
    exact linearIndepOn_univ_iff.mp this
  have hfin : finrank (Bst P) (Bst P ⊗[ℚ_[l]] ↥L.1) = d := Module.finrank_baseChange
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero (k := ↥(MaximalUnramifiedExtension l)) w (GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent hfin w hB)
  let ys := ∑ i, mulV P ↥L.1 (Fin 1 → ↥L.1) (a i) (y i)
  have hys : ys ∈ Dpst P ρm := Submodule.sum_mem _ fun i _ => mulV_mem_Dpst P ρm (a i) (y i) (hyD i)
  have hysA : toA P L ys = ∑ i, algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (a i) • w i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ys, map_sum, toA_mulV, w]
  have hn : Algebra.norm (Bst P) (toA P L ys) ≠ 0 := by rw [hysA]; exact ha
  obtain ⟨K₂, hK₂⟩ := (mem_Dpst P ρm).mp hys
  have hχ : ∀ g : ↥(GK K), χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g * g⁻¹) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by rw [mul_inv_cancel, map_one]; rfl
    rw [map_mul, Module.End.mul_apply, hm g, h0, zero_smul] at h1
    exact zero_ne_one (congrFun h1 0)
  have hunit : IsUnit (Algebra.norm (Bst P) (toA P L ys)) := by
    refine hline (supExt K K₂) _ hn fun g => ?_
    let g0 : ↥(GK K) := ⟨g, GK_le (K' := supExt K K₂) le_sup_left g.2⟩
    have hfix := hK₂ g0 (GK_le (K' := supExt K K₂) le_sup_right g.2)
    have h1 : Algebra.norm (Bst P) (toA P L (stRep P ρm g0 ys)) = Algebra.norm (Bst P) (toA P L ys) := by
      rw [hfix]
    rw [toA_stRep ρm χ hm, map_mul, GlobalTheory.T.norm_tensorProduct_map_id_right, norm_one_tmul] at h1
    have hν : Algebra.norm ℚ_[l] (χ g0) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hχ g0)
    refine ⟨(Algebra.norm ℚ_[l] (χ g0))⁻¹, ?_⟩
    change actSt P ((g0 : ↥(GK K)) : GQ l) _ = _
    conv_rhs => rw [← h1]
    rw [mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, mul_one]
  obtain ⟨v, hv'⟩ := (isUnit_of_isUnit_norm hunit).exists_right_inv
  refine ⟨ys, hys, (toA P L).symm v, ?_⟩
  apply (toA P L).injective
  rw [toA_mulB, LinearEquiv.apply_symm_apply, toA_tmul, mul_comm, hv']
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJEpsPos
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem famJ_CLw_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by
  rw [← Fm.params_K x hx i]
  rfl

theorem famJ_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem famJ_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_ez 0 i]
  exact (Fm.L 0 i).sc.ez_pos

theorem fam_joints : ∀ {eps : ℝ} (Fm : FamP eps) (C₂ : ℝ), (∀ D : D7, LocalSituation.adm7 D) →
    (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) →
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (HW : HWOf (Fm.D x i).loc),
      LJ.ConclusionJa (Fm.D x i) → RecS.JointB (Fm.L x i) HW C₂ ∧ RecS.JointCD (Fm.L x i) HW := by
  intro eps Fm C₂ h7 hF
  obtain ⟨xB, hB⟩ := GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale eps Fm.ez C₂ (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  obtain ⟨xC, hC⟩ := GlobalTheory.T.inertPrimeWordConditions_of_large_scale eps Fm.ez (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  refine ⟨max xB xC, fun x hx h1 i HW hJ => ⟨?_, ?_⟩⟩
  · refine hB _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_left _ _).trans hx
  · refine hC _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_right _ _).trans hx

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.FinTypSpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n π s τ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → ℂ)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ π.S
  let Wd : Submodule ℂ (GAf L n → ℂ) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ π.S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨T.2.2, T.2.1⟩ le_rfl

  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => π.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases π.irr Wd hWdS hstab with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · intro f hf
    rw [← h0] at hf
    exact hWdle hf

end GlobalTheory.FinTypSpanLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsLast
section
namespace GlobalTheory.TransportLemma

theorem transport {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (T : V ≃+ V)
    {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S)
    (h₁ : ∀ x : V, (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁)
    (h₂ : ∀ x : V, (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) := by
  obtain ⟨hmem, hinj, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (h₂ s).mpr (hmem s hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h : (T : V → V) (s - t) ∈ M₁ := by
      rw [map_sub]; exact hxy
    rw [hinj s hs t ht ((h₁ _).mp h)]
  · intro y hy
    have hy' : T.symm y ∈ Λ₂ := (h₂ _).mp (by simpa using hy)
    obtain ⟨s, hs, hd⟩ := hcov _ hy'
    refine ⟨(T : V → V) s, Finset.mem_image_of_mem _ hs, ?_⟩
    have h : (T : V → V) (T.symm y - s) ∈ M₁ := (h₁ _).mpr hd
    rw [map_sub] at h
    simpa using h

theorem main : ∀ {V : Type} [inst : AddCommGroup V] [Module ℂ V] [inst_2 : DecidableEq V] (T : V ≃+ V) {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}, Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S → (∀ (x : V), (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁) → (∀ (x : V), (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) → Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) :=
  @transport

end GlobalTheory.TransportLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.isoTyp a.ρ S ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → a.W), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial σ.V := by
    haveI := σ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  unfold NG.isoTyp
  refine sSup_le ?_
  rintro S' ⟨hS'irr, Φ, hΦ⟩
  let Good : (σ.V →ₗ[ℂ] (GAf L n → a.W)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ S'
  let Wd : Submodule ℂ (GAf L n → a.W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS' : Wd ≤ S' := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨fun u => hS'irr.1.le (T.2.2 u), T.2.1⟩ le_rfl

  have htr : ∀ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS'irr.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂

  let T1 : σ.V →ₗ[ℂ] (GAf L n → a.W) := S'.subtype ∘ₗ Φ.toLinearMap ∘ₗ LinearMap.codRestrict S T0 hT0S
  have hT1 : Good T1 := by
    refine ⟨fun x hx u => ?_, fun u => (Φ _).2⟩
    exact hΦ x ⟨T0 u, hT0S u⟩ ⟨T0 _, hT0S _⟩ (hT0eq x hx u)
  have hrc := hS'irr.2.2 Wd ⟨hWdS'.trans hS'irr.1.le, hstab⟩ hWdS'
  rcases hrc with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : σ.V)
    have hmem : T1 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T1, hT1⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    apply hu
    apply hT0inj
    have h2 : Φ (LinearMap.codRestrict S T0 hT0S u) = 0 := Subtype.ext hmem
    rw [map_zero]
    have h3 := Φ.injective (h2.trans Φ.map_zero.symm)
    exact congrArg Subtype.val h3
  · rw [← h0]; exact hWdle

end GlobalTheory.SpanLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockSupp

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro hBZ hGL _ hDZ k _ _ _ _ r t χ π v hχs hχt hv hbv
  obtain ⟨s, d, σ, hsupp⟩ := _root_.GlobalTheory.CuspSupportExist.main hBZ hGL k (r + t) π
  obtain ⟨e, x, hx, hxe⟩ := _root_.GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec hDZ k r t χ π v hχt hv hbv
  refine ⟨s, d, σ, hsupp, ?_⟩
  have h := _root_.GlobalTheory.JacSuppCount.card_le_ncard_unrTwist hBZ hGL k (r + t) s (t + 1) χ π d σ _ e (Finset.univ.map (Fin.succEmb t)) x hχs hsupp
    (by intro j hj; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; rfl) hx
    (by intro j hj g hg; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; exact hxe i g hg)
  simpa using h

end GlobalTheory.BlockSupp
end

