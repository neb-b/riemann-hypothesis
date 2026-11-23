module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
section
noncomputable section
namespace GlobalTheory.StdFrameCounterexample
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latC (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map ((V.frame.equivFun.toLinearMap).restrictScalars (𝓞 D.host.E))

theorem mem_latC (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ latC V ↔ x ∈ L0c D V := by
  show _ ↔ ∑ i, x i • V.frame i ∈ V.L0
  rw [← V.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply x⟩

theorem latC_coe (V : HSp D) : (latC V : Set _) = L0c D V := Set.ext (mem_latC V)

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = latC V := by
  have hfg : (latC V).FG := Submodule.FG.map _ V.standardTuple_isLattice.fg
  have hsp : Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have h : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra hn
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt hn
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change a • e x ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          have hh := V.herm.eq (e x) y
          simpa [hxy] using hh.symm
        simp [map_smul, hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (latC V : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top]
    exact LinearMap.range_eq_top.2 V.frame.equivFun.surjective
  have hc := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (latC V) hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← hc x, latC_coe]
  have h1 : Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)) = 1 := by
    rw [Subgroup.coe_inv, Subgroup.coe_one, inv_one, Units.val_one]
  show Matrix.mulVec (Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E))) _ ∈
    latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [h1, Matrix.one_mulVec]
  rfl

theorem vstd_iff (i : Fin D.R.m) : VStd D i ↔ (Vc D i).gram = 1 ∧
    ∀ x : Fin (Vc D i).rank → D.host.E, ∑ a, x a • (Vc D i).frame a ∈ (Vc D i).L0 ↔ ∀ a, IsIntegral ℤ (x a) := by
  unfold VStd
  rw [hLat_one]
  refine and_congr_right fun _ => ?_
  rw [Submodule.ext_iff]
  refine forall_congr' fun x => ?_
  rw [mem_latC]
  refine iff_congr Iff.rfl ?_
  rw [Submodule.mem_pi]
  refine forall_congr' fun a => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]; exact y.2
  · intro h
    exact ⟨⟨x a, h⟩, rfl⟩

end GlobalTheory.StdFrameCounterexample
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.PlaceExOfSurjective
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.PlaceValues

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γE, -, hE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨γE, hE.symm⟩

set_option maxHeartbeats 2000000 in
theorem ext_val (V : HSp D) (C : Bridge.CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hm : Bridge.CoefMapTie V C c0 rho) {pair nab del} (hc : Bridge.CoefTie V C P lam c0 pair nab del)
    (f : S.Cl → S.V) (g : Bridge.Gf V) : ∃ k v, P.ext f g = ((χ k : ℂˣ) : ℂ) • c0 v := by
  obtain ⟨e, -, hcoef, -⟩ := hc
  obtain ⟨γE, hγE⟩ := exists_ratMat V (P.decG g)
  refine ⟨P.decK g, rho γE (e (f (P.decC g))), ?_⟩
  rw [hm.1 _ _ hγE, ← hcoef]
  rfl

end GlobalTheory.PlaceValues
end
end

