module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LambdaPrimeBasisRowTypePosAtReference
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.LamPos

theorem lambdaPrime_basis_row_type_pos_at_reference : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, ∀ j ∈ Finset.Icc 1 D.R.m, 0 < D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH hL hI σ j hj
  obtain ⟨cOf, -, h2, -⟩ := hL
  obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
  have hi : j - 1 < D.R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin D.R.m) : ℕ) + 1 = j := by simp only; omega
  have key := h2 ⟨j - 1, hi⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hI σ ⟨j - 1, hi⟩)
  rw [Y.tup0, hj'] at key
  rw [key]
  exact hH.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.R3.LamPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.JwLift

theorem mem_dual_iff {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h y x := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]

theorem jwIdx_eq_jw : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hHZ : (lZ0 D A P0 ψ0 Zs i t)ᴴ * lH D A P0 ψ0 i t * lZ0 D A P0 ψ0 Zs i t = (A.side P0 ψ0 Zs).HT i t) (hsp : Submodule.span D.what₂.LL (↑((A.side P0 ψ0 Zs).Tl i t) : Set (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL)) = ⊤) (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))) (w : D.what₂.places.Pl), Idx.jwIdx D (tup t) ((i : ℕ) + 1) w = Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hHZ hsp hT w
  set HT := (A.side P0 ψ0 Zs).HT i t with hHTdef
  set Tl := (A.side P0 ψ0 Zs).Tl i t with hTldef
  let Z : Matrix (Fin (lDim D A P0 ψ0 i t)) (Fin ((A.side P0 ψ0 Zs).dZ i t)) D.what₂.LL := lZ0 D A P0 ψ0 Zs i t
  let Pr : Matrix (Fin ((A.side P0 ψ0 Zs).dZ i t)) (Fin (lDim D A P0 ψ0 i t)) D.what₂.LL := lPrj D A P0 ψ0 Zs i t
  have hP1 : Pr * Z = 1 := hP.1
  have hHZ' : Zᴴ * lH D A P0 ψ0 i t * Z = HT := hHZ
  have hT' : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Tl.map ((Matrix.mulVecLin Z).restrictScalars (𝓞 D.what₂.LL))).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := hT
  let f : (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    (eMt i t).toLinearMap ∘ₗ Matrix.mulVecLin Z
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Z *ᵥ x = Z *ᵥ y := (eMt i t).injective hxy
    have h2 : Pr *ᵥ (Z *ᵥ x) = Pr *ᵥ (Z *ᵥ y) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hTL : Idx.TjL D (tup t) ((i : ℕ) + 1) = Tl.map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    rw [hT', ← Submodule.map_comp]
    rfl
  have hTV : Idx.TjV D (tup t) ((i : ℕ) + 1) = LinearMap.range f := by
    unfold Idx.TjV
    rw [hTL, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top]
  have hin : ∀ y z, inner ℂ (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f y)) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f z)) =
      D.what₂.embLL (Formalism.DivisionValues.hform HT y z) := by
    intro y z
    have := hF.inner (Z *ᵥ y) (Z *ᵥ z)
    have e1 : Formalism.DivisionValues.hform (lH D A P0 ψ0 i t) (Z *ᵥ y) (Z *ᵥ z) = Formalism.DivisionValues.hform HT y z := by
      rw [GlobalTheory.Mem.LiftForms.hform_dot HT, ← hHZ']
      exact GlobalTheory.Mem.LiftForms.hform_mulVec _ Z Z y z
    rw [← e1]
    exact this
  have hDual : Idx.TjDual D (tup t) ((i : ℕ) + 1) =
      (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform HT) Tl).map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [hTV] at hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨z, (mem_dual_iff _ _ _).2 fun y hy => ?_, rfl⟩
      obtain ⟨c, hc⟩ := hx2 (f y) (by rw [hTL]; exact ⟨y, hy, rfl⟩)
      rw [hin] at hc
      exact ⟨c, (D.what₂.embLL.injective hc).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨by rw [hTV]; exact ⟨z, rfl⟩, ?_⟩
      rintro a ha
      rw [hTL] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨c, hc⟩ := (mem_dual_iff _ _ _).1 hz y hy
      refine ⟨c, ?_⟩
      change _ = D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c)
      rw [hc]
      exact hin y z
  unfold Idx.jwIdx Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx
  rw [hTL, hDual]
  exact Formalism.BasicNotions.SkeletonIndexLemmas.lidx_map (D.plEq w) f hf _ _

end GlobalTheory.Mem.JwLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.LiftForms

theorem TjL_eq_map_matLat : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ
  classical
  set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef
  have hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) := fun x => rfl
  have hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) =
      Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) := by
    rw [hZ, span_range_mulVec]
    rfl

  have hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) =
      J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro w hw
      rw [hspan] at hw
      have hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤
          (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner,
          hform_orth hP, sub_self]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

  have hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y =
      D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y) := by
    have h := LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
        ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap)
      (fun k => by
        show D.what₂.thetaP (tup t) ((i : ℕ) + 1) (J (Pi.single k 1)) =
          D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J (Pi.single k 1)))
        rw [hproj]
        exact hθ _)
    intro y
    exact LinearMap.congr_fun h y
  have hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) := by
    intro w hw
    rw [LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]
  have hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1) := by
    have h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ := by
      rw [LinearMap.orthogonal_ker]
      rfl
    rw [h1]
    apply le_antisymm
    · have := Submodule.orthogonal_le hle1
      rwa [Submodule.orthogonal_orthogonal] at this
    · exact inf_le_left
  have hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)
  have h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj]
    exact hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ)
      (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))

  have h6 : Submodule.span (𝓞 D.what₂.LL)
      {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro u hu
      obtain ⟨c, hc⟩ := hu
      refine ⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩
      rw [hJ, LinearEquiv.apply_symm_apply, hc]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hL.2 x).1 hx
      have hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) =
          ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
          D.what₂.jMt (tup t) ((i : ℕ) + 1) y =
            ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
        refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
            D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
        · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
        · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv
          refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
          refine ⟨fun u => if u = v then 1 else 0, ?_⟩
          rw [hy, Finset.sum_eq_single v]
          · simp
          · intro u _ hu
            simp [hu]
          · intro h; exact absurd hv h
      obtain ⟨y, hy, hyx⟩ := key
      have hxy : y = eMt i t x := jMt_injective _ _ (hyx.trans hc'.symm)
      change eMt i t x ∈ _
      rw [← hxy]
      exact hy

  let π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ
      (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (eMt i t).surjective x
    rw [h4', ← hJ, hproj, hπe]
    rfl
  have hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end GlobalTheory.Mem.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

theorem end_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W) (a b : ℂ) (x : W) :
    L (a • b • x) = (a * b) • L x := by
  rw [map_smul, map_smul, smul_smul]


set_option maxHeartbeats 16000000 in
theorem ext_mem_levSubV_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ
  intro k hk g
  have hkG : k ∈ GfC (Vc D i) := hk.1
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hk.2.1
  have hH : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).H := hk.2.2
  have hq : (finHom (Vc D i)).rangeRestrict k ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) k) ∈
      Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
    rw [← finE_eq]
    exact ⟨hpar, Subgroup.mem_top _⟩
  set κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩ with hκdef
  have hred' : R.eG ((R.B.L i t).act_tie.red κ) = Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) :=
    hred i t κ
  have hu : (R.B.L i t).act_tie.red κ ∈ F.P0 := by
    have h2 : R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) ∈ F.P0 := hH
    rw [← hred', MulEquiv.symm_apply_apply] at h2
    exact h2
  have hlaw := hΦ κ hu ((finHom (Vc D i)).rangeRestrict g)
  have hchi : levChi _ (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) •
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hH' : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := hH
    have hP : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hH⟩ : F.P0) =
        ⟨(R.B.L i t).act_tie.red κ, hu⟩ := Subtype.ext (by
          show R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) = (R.B.L i t).act_tie.red κ
          rw [← hred', MulEquiv.symm_apply_apply])
    have hw := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have he := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hH'
    have hw2 : Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) =
        (R.levR F false).conj.chi ⟨_, hH'⟩ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) :=
      hw.trans (congrArg (fun u => u * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k)) he)
    show ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) = _
    rw [hw2, Units.val_mul, mul_comm, smul_eq_mul]
    congr 1
    · show (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨R.eG.symm _, hH⟩))⁻¹ : ℂˣ) : ℂ) = _
      rw [hP]
      rfl
  have e1 := Formalism.IndefR.Eqv.Act.coefExt_mul (R.cV i) (hcV i) Φ g k hkG
  have e3 : (R.cV i).ext Φ g = (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) := rfl
  rewrite [e1, hchi, hlaw, e3, smul_eq_mul]
  exact @end_smul_smul _ _ _ _ _ _ _

end GlobalTheory.LiftSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyAStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  first | exact @GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | exact GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | (intros; apply GlobalTheory.linearIndependent_completion_of_irreducible_minpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocStageInhabited
section
open Formalism Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem locStage_inhabited : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecompositionStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_differ_by_decomposition : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  first | exact @GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | exact GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | (intros; apply GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapOpOfKForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.GoodProj

theorem rowForm_rE {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ}
    (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (x : Fin (rDim D A P ψ t) → D.what₂.LL) :
    rowForm A P ψ t ((rE D A P ψ t).mulVec x) =
      (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) (rowForm A P ψ t x) := by
  have hc := (idempotent_spec _ A.v0 ok.conj G A.X ok.irr).2
  have h1 := (level_operator_spec _ A.v0 ok.conj (A.fam.R t).S ((ok.what₂ t).hpos A.v0) G (A.fam.R t).r (ok.what₂ t).act
    (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ (idemOf A.X) (hc _).symm).1
  unfold rowForm rE
  change _ = (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec, map_sum]
  rw [CSD.gaOp]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec _ (A.fam.R t).S G (A.fam.R t).r g _))

end GlobalTheory.Mem.R3.GoodProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopBridge

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem rangeRestrict_mem_Q_iff (κ : GA D V) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L := by
  have e1 : Lev.finE V κ = Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 := Lev.finE_eq V κ
  constructor
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := h
    rw [e1]
    exact h1.1
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := by
      rw [mem_lev]
      exact ⟨e1 ▸ h, Subgroup.mem_top _⟩
    exact h1

theorem mem_levelSubgroup_withP_iff (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ GfC V) :
    κ ∈ levS V β (Lev.withP L P) ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (Lev.finE V κ) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨hκ, h⟩⟩

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem levChi_flagL_eq_ch {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    Lev.levChi V β (Lev.flagL L) κ = (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) := by
  have e2 : (levEnv V β L).ch ⟨_, hq⟩ = levFn β (Lev.flagL L) (Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1) := rfl
  unfold Lev.levChi
  rw [e2, Lev.finE_eq]
  rfl

end GlobalTheory.TopBridge


open GlobalTheory.TopBridge in
theorem GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hr b t κ hκ
  have hQ : ∀ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      (R.B.R t).act_tie.red ⟨_, hq⟩ = R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)) := fun hq =>
    R.eG.eq_symm_apply.2 ((hr t ⟨_, hq⟩).trans (congrArg (rTup R.βX (R.datXt t)) (Lev.finE_eq D.sp.X' κ).symm))
  have hH : ∀ x, x ∈ (R.levR F b).H ↔ R.eG.symm x ∈ (F.lvl b).P := fun x => Iff.rfl
  have hS := mem_levelSubgroup_withP_iff D.sp.X' R.βX (R.datXt t) (R.levR F b) hκ
  refine ⟨hS.trans ?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have hq := (rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).2 h1
      exact ⟨hq, (hQ hq).symm ▸ (hH _).1 h2⟩
    · rintro ⟨hq, hp⟩
      exact ⟨(rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).1 hq, (hH _).2 (hQ hq ▸ hp)⟩
  · intro hq hp
    have hP : rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ) ∈ (R.levR F b).H := (hH _).2 (hQ hq ▸ hp)
    refine (levelCharacter_withLevel_of_mem D.sp.X' R.βX (R.datXt t) hP).trans ?_
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) (levChi_flagL_eq_ch _ _ _ hq) ?_)
    have e : (⟨_, hp⟩ : (F.lvl b).P) = ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ :=
      Subtype.ext (hQ hq)
    have key : (((R.levR F b).chi ⟨_, hP⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl b).ψ ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
      rfl
    exact key.trans (congrArg (fun p => D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL)) e.symm)
end
end

