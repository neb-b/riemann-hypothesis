module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesTer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VanishNConj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.PrincipalCongruenceMemLevel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
section
namespace Formalism.L2.SG.Pf.Cnt

theorem alpha_discriminant_holds : AlphaDisc :=
  Formalism.L2.SG.Pf.G5.alphaDisc_of_discOnto
    (Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of_uDModel Formalism.L2.SG.Pf.Cnt.unitary_discriminant_model)

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InWLeft
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem h_symm (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem h_fe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [h_symm, X.ef b a]
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem inW_pW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  unfold pW
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, h_fe, X.ff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_zero]
  constructor
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem decomp (y : (VS D).V) :
    y = ∑ c, (VS D).hT (X.fY c) y • X.eX c + ∑ c, (VS D).hT (X.eX c) y • X.fY c + pW X y := by
  unfold pW
  abel

theorem inW_left {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT w (X.eX a) = 0 ∧ (VS D).hT w (X.fY a) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h_symm, (hw a).1, star_zero]
  · rw [h_symm, (hw a).2, star_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalGluingHolds
section
namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem local_gluing_holds : GlueLoc :=
  glueLoc_of_fibCount fibre_counting_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibT
section
namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem thetaEx_holds : ThetaEx := by
  intro D
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB D.host, ?_⟩
  rw [Formalism.BasicNotions.Examples₂.conj_half, Formalism.BasicNotions.Examples₂.conj_bE]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
section
namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DictLatF : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 → LatQ X (Xq X n) (xq X n) (Mq X n)

def DictLatB : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → LatQ X (Xq X n) (xq X n) (Mq X n) → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0

theorem dictLat_of (hF : DictLatF) (hB : DictLatB) : DictLat :=
  fun X u n hn => ⟨hF X u n hn, hB X u n hn⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibPl
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pl

variable {D : D7} (X : HidaSetting D)

theorem umat_rv {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hRL : RatLink X x n) (v : InfinitePlace X.B.I.F)
    (y : (VS D).V) : uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (n y)) := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

theorem inv_map_emb {m : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix (Fin m) (Fin m) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have h1 : (A.map f).det = f A.det := (f.map_det A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
  rw [Matrix.inv_def, Matrix.inv_def, h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i j
  simp [Matrix.smul_apply]

theorem hJ_span_ef (v : InfinitePlace X.B.I.F) (α β : Fin D.R.rS → D.host.E) (w : Fin X.B.I.n → ℂ)
    (he : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0)
    (hf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd (∑ c, α c • X.eX c + ∑ c, β c • X.fY c))) w = 0 := by
  rw [Formalism.L2.SG.NormCut.crd_add', Formalism.L2.SG.NormCut.crd_sum', Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  rw [rv_add, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum,
    Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l, Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left,
    Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left]
  simp only [he, hf, mul_zero, Finset.sum_const_zero, add_zero]

end Pl

section Main

theorem dictionary_place_holds : DictPlace := by
  intro D X u x n hRL hNF
  set ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => embS D (X.pl v) with hψ
  have hxM : ∀ v, LsNc5.xMat X v x.1 = (Xq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.xMat, LsNc5.fV, LsNc5.eV, Matrix.map_apply]
    rw [show X.eR a = X.crd (X.eX a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have haM : ∀ v, LsNc5.aMat X v x.1 = (Aq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.aMat, LsNc5.fV, Matrix.map_apply]
    rw [show X.fR a = X.crd (X.fY a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have hmM : ∀ v, LsNc5.mMat X v x.1 = (Mq X n).map (ψ v) := fun v => by
    unfold LsNc5.mMat Mq
    rw [hxM, haM, inv_map_emb, Matrix.map_mul]

  have hrow : ∀ v b (w : Fin X.B.I.n → ℂ), (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0) →
      (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) →
      hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (x.1 v) *ᵥ w) = hJ (X.B.I.ε v) (rv X.B.I v (X.crd (xq X n b))) w := by
    intro v b w he hf
    have h1 := Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.hJ_inv_r (X.B.I.ε v) (x.1 v)⁻¹ (LsNc5.fV X v b) w
    rw [inv_inv] at h1
    rw [h1]
    have h2 : uMat (x.1 v)⁻¹ *ᵥ LsNc5.fV X v b = rv X.B.I v (X.crd (n.symm (X.fY b))) :=
      umat_rv X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hRL) v (X.fY b)
    rw [h2]
    have hy : n.symm (X.fY b) = xq X n b + (∑ c, (VS D).hT (X.fY c) (n.symm (X.fY b)) • X.eX c +
        ∑ c, (VS D).hT (X.eX c) (n.symm (X.fY b)) • X.fY c) := by
      simp only [xq, pW]; abel
    have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
      unfold rv
      rw [← Matrix.mulVec_add]
      congr 1
      ext i
      simp
    rw [hy, Formalism.L2.SG.NormCut.crd_add', rv_add, Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l,
      hJ_span_ef X v _ _ w he hf, add_zero]
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show LsNc5.xMat X v x.1 p.1.1 p.1.2 = embS D (X.pl v) (Xq X n p.1.1 p.1.2)
    rw [hxM]; rfl
  · funext v j
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v x.1 b ⟨j.val, h⟩ else LsNc5.yVec X u v x.1 b) =
      rowV X u (xq X n b) v j
    unfold rowV
    split_ifs with h
    · exact hrow v b _ (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).1) (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).2)
    · refine hrow v b _ (fun c => ?_) (fun c => ?_)
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).1, map_zero]
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).2, map_zero]
  · funext v
    show (LsNc5.mMat X v x.1 p.1.1 p.1.2 - star (LsNc5.mMat X v x.1 p.1.2 p.1.1)) / 2 =
      (embS D (X.pl v) (Mq X n p.1.1 p.1.2) - star (embS D (X.pl v) (Mq X n p.1.2 p.1.1))) / 2
    rw [hmM]; rfl
  · funext v
    show (LsNc5.mMat X v x.1 a a).im = (embS D (X.pl v) (Mq X n a a)).im
    rw [hmM]; rfl

end Main

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf
open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_base_lattice_iff_adelic {D : D7} (X : HidaSetting D) (y : (VS D).V) :
    y ∈ (VS D).L0 ↔ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [Formalism.L2.SG.Pf.LatDict.mem_hermitianStandardLattice_iff_pairing_integral X y]
  exact ⟨fun h => Formalism.L2.SG.Pf.Level.incl_mem_Lf X _ h,
    fun h => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.mem_L_of_inclE_mem X.B.I _ h⟩

theorem noratC_holds : NOratC := by
  intro D X u s
  constructor
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hγK : γ.2 ∈ X.B.I.Kset := by
      have h1 : (X.xu u)⁻¹ * γ.2 * X.xu u ∈ X.B.I.Kset := hK2.2.1 _ hk
      have e : γ.2 = X.xu u * ((X.xu u)⁻¹ * γ.2 * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e]
      exact unitaryCongruence.K_mul X.B.I (unitaryCongruence.K_mul X.B.I (X.xu_K u) h1) (unitaryCongruence.K_inv X.B.I (X.xu_K u))
    obtain ⟨M, hM, hinf, hfin⟩ := hG
    refine ⟨γ, matEC X M, ⟨M, hM, hinf, hfin, matE_crdC X M⟩, rfl, ?_⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (γ.1 v) *ᵥ rvHom X.B.I v y = rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [rvHom_apply, rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (γ.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hN v
    refine ⟨⟨matE_isomC X M hM, ?_⟩, ?_, ?_⟩
    · have key : ∀ y, matEC X M y ∈ (VS D).L0 ↔ y ∈ (VS D).L0 := by
        intro y
        rw [mem_base_lattice_iff_adelic, mem_base_lattice_iff_adelic, matE_inclC, ← hfin]
        exact (Formalism.L2.SG.Pf.UnipB.kset_apply X hγK _).symm
      show Formalism.HermitianLatticesTheory.gmap (matEC X M) (VS D).L0 = (VS D).L0
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (key z).2 hz
      · intro hy
        refine ⟨(matEC X M).symm y, (key _).1 (by simpa using hy), ?_⟩
        simp
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _), add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3
  · rintro ⟨x, n, hx, rfl, hn⟩
    have hNf := nLamNfin_holds D X u _ x n hx hn
    have hlat : ∀ y : (VS D).V, y ∈ (VS D).L0 ↔
        X.B.I.fmat (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
      intro y
      rw [mem_base_lattice_iff_adelic]
      simp only [OneMemClass.coe_one, one_mul]
      exact Formalism.L2.SG.Pf.UnipB.kset_apply X (unitaryCongruence.K_inv X.B.I (X.xu_K u)) _
    have hc := (Formalism.L2.SG.Pf.VanishNConj.core X u (Formalism.L2.SG.Pf.unipotent_in_level X u) 1 hlat hn hx).1
    simp only [OneMemClass.coe_one, one_mul] at hc
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, hNf, hc⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjRowPars
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.NcReal.JX.FR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowParseval_holds : RowParseval := by
  intro D X u x y hx hy v
  set a := rv X.B.I v (X.crd x) with ha
  set b := rv X.B.I v (X.crd y) with hb
  have hbe : ∀ c, hJ (X.B.I.ε v) (eV X v c) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).1]; simp
  have hbf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).2]; simp
  have hdec := decomp (nX X) (ProductExactness.Tw_pos u) (fX_ee X v) (LsNc5.fr_ff X v) (LsNc5.fr_ef X v) (fX_ww X u v) (fX_ew X u v)
    (LsNc5.fr_fw X u v) (LsNc5.fr_ez X u v) (LsNc5.fr_fz X u v) (LsNc5.frame_z_z_eq_neg_t X u v) (LsNc5.fr_zw X u v) b hbe hbf
  have hab : hJ (X.B.I.ε v) a b = ∑ c, hJ (X.B.I.ε v) a (X.wfr u v c) * star (hJ (X.B.I.ε v) b (X.wfr u v c)) +
      hJ (X.B.I.ε v) a (LsNc5.zV X u v) * star (hJ (X.B.I.ε v) b (LsNc5.zV X u v)) * (-(1 / ((Tw u : ℝ) : ℂ))) := by
    conv_lhs => rw [hdec]
    rw [fr_add_r, fr_sum_r, fr_smul_r]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [fr_smul_r, hJ_swap (X.B.I.ε v) (X.wfr u v c) b, star_star]
      ring
    · rw [hJ_swap (X.B.I.ε v) (LsNc5.zV X u v) b, star_star]
      ring
  rw [← Formalism.L2.SG.Pf.hJ_crd, ← ha, ← hb, hab, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (Fin.castSucc j).val < D.R.k := j.isLt
    simp only [rowV, gC, dif_pos hj, if_pos hj, mul_one]
    rfl
  · have hl : ¬ (Fin.last D.R.k).val < D.R.k := by simp
    simp only [rowV, gC, dif_neg hl, if_neg hl]
    rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TraceReHolds
section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem traceRe_holds : TraceRe := by
  intro D X t
  have h1 : ∀ v, X.B.I.φ v (X.ιE.symm t) = embS D (X.pl v) t := fun v => by
    rw [X.φ_eq, RingEquiv.apply_symm_apply]
  simp only [h1]
  rw [Formalism.MainNotions.BlockEstimateWords.trace_tau D t, Finset.sum_div,
    Equiv.sum_comp X.pl (fun τ => ((embS D τ) t).re)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

