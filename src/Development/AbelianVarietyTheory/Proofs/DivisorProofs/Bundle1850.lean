module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfSemilinear
section
set_option autoImplicit false

noncomputable section

open Module

namespace GlobalTheory.ShareOn.Alg

theorem finrank_eig_eq {LL G W : Type} [Field LL] [Group G] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤)
    (ρV : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))) (ρ : Representation ℂ G W)
    (hρ : ∀ g v, ρ g (f v) = f (ρV g v)) (H : Subgroup G) [Finite H] (μ : H →* LLˣ) :
    finrank ℂ (GlobalTheory.BadCount.eig ρ H ((Units.map σ.toMonoidHom).comp μ)) =
      finrank LL (⨅ h : H, LinearMap.ker (ρV h - ((μ h : LLˣ) : LL) • LinearMap.id) : Submodule LL (Fin n → LL)) := by
  classical
  letI : Algebra LL ℂ := σ.toAlgebra
  letI : Module LL W := Module.compHom W σ
  haveI : IsScalarTower LL ℂ W := ⟨fun a b w => by
    show (σ a * b) • w = σ a • (b • w)
    rw [mul_smul]⟩
  have hsum : ∀ v : Fin n → LL, f v = ∑ k, σ (v k) • f (Pi.single k 1) := by
    intro v
    conv_lhs => rw [show v = ∑ k, v k • Pi.single k (1 : LL) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    rw [hsum v]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b : Basis (Fin n) ℂ W := Basis.mk hli hsp'
  let f' : (Fin n → LL) →ₗ[LL] W :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun a v => by
        show f (a • v) = σ a • f v
        rw [map_smulₛₗ] }
  have hf' : f' = Fintype.linearCombination LL b := by
    apply LinearMap.ext
    intro v
    rw [Fintype.linearCombination_apply]
    show f v = _
    rw [hsum v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Basis.mk_apply]
    rfl
  have hbc : IsBaseChange ℂ f' := hf' ▸ IsBaseChange.of_fintype_basis LL b
  have key := (_root_.GlobalTheory.BadCount.finrank_iInf_ker_baseChange LL ℂ (Fin n → LL) W H f' hbc
    (fun h => ρV h - ((μ h : LLˣ) : LL) • LinearMap.id)
    (fun h => ρ h - ((σ (μ h : LLˣ)) : ℂ) • LinearMap.id) (fun h v => by
      show ρ h (f v) - σ ((μ h : LLˣ) : LL) • f v = f (ρV h v - ((μ h : LLˣ) : LL) • v)
      rw [map_sub, map_smulₛₗ, hρ])).1
  exact key

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn.Alg

theorem top_le_span_single {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hsp : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  classical
  rw [← hsp]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ∑ k, v k • Pi.single k (1 : LL) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hv, map_sum]
  exact Submodule.sum_mem _ fun k _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_eq_of_semilinear {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤) : finrank ℂ W = n := by
  rw [finrank_eq_card_basis (Basis.mk hli (top_le_span_single σ f hsp)), Fintype.card_fin]

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem halfUnip_bot (p : PtAt ex Csz) : HalfUnip p ⊥ := by
  refine ⟨0, fun g hg v => ?_⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  intro a b
  simp only [map_one, Pi.one_apply, Units.val_one]
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by rw [h, Matrix.one_apply_eq]⟩

theorem shareW_of_modelAt (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hM : ModelAt p i T)
    (hH : HalfUnip p p.P.P0)
    (hs : ∀ p0 : ℕ, p0 ≤ D.R.r → 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T)
    (he : (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / T ≤ y)) :
    ShareW p i y := by
  obtain ⟨C, hC, _, M, ka, ρ, σ, f, hpull, hρ, hli, hsp, hlev, hcard, hcase⟩ := hM
  let H : Subgroup p.P.Gp := p.P.P0
  let μ : H →* D.what₂.LLˣ := ((p.R.toRealDat.FW i).chi.comp H.subtype) * (p.P.ψ0)⁻¹
  let lam : H →* ℂˣ := (Units.map σ.toMonoidHom).comp μ
  have hty : spType p.R.toRealDat p.F.lv2 i = ⨅ h : H, LinearMap.ker ((p.R.toRealDat.FW i).ρ h -
      ((μ h : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id) := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hdim : finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hty]
    exact Alg.finrank_eig_eq σ f hli hsp (p.R.toRealDat.FW i).ρ ρ hρ H μ
  have hn : finrank ℂ (M.cusp ka) = p.R.toRealDat.nW i := Alg.finrank_eq_of_semilinear σ f hli hsp
  have key : (1 - y) * (finrank ℂ (M.cusp ka) : ℝ) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
    rcases hcase with hdef | ⟨h0, hr, harch⟩
    · have hd := (_root_.GlobalTheory.ShareOn.Definite.share_definite _ _ _ _ M hdef ka ρ hpull).2 H (hlev H hH)
      rw [← Nat.cast_mul, hd.2 lam]
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
    · have hsO : sOf M ≤ T := by
        have := hs M.p0 hr.le
        unfold sOf TwoLevels.dimX
        rw [hcard]
        exact this
      have hR := _root_.GlobalTheory.ShareRanks.ranks _ _ _ _ M (hlev ⊥ (halfUnip_bot p)) h0 hr ka T harch hsO
      have hS := (_root_.GlobalTheory.ShareEig.share_eig _ _ _ _ M ka ρ hpull _ _ hR H (hlev H hH) lam).2
      have hY : ((M.dimY : ℝ) * (M.dimY + 6) / T) ≤ y := by
        unfold TwoLevels.dimY
        rw [hcard]
        exact he
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
  unfold ShareW
  rw [← hdim, ← hn]
  exact key

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders

end GlobalTheory.ShareOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedParts
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple

theorem exists_irred_le_orbSpan {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K))
    (y : V) (hy : y ≠ 0) :
    ∃ U : Submodule ℂ V, U ≠ ⊥ ∧ U ≤ (orbSpan ρ y).toSubmodule ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) := by
  classical
  set O := orbSpan ρ y with hO
  let ρO := O.toRepresentation
  have hρO : ∀ g (w : O.toSubmodule), (ρO g w : V) = ρ g w := fun _ _ => rfl
  let BO : O.toSubmodule →ₗ⋆[ℂ] O.toSubmodule →ₗ[ℂ] ℂ := (B.comp O.toSubmodule.subtype).compl₂ O.toSubmodule.subtype
  have hBO : ∀ u w : O.toSubmodule, BO u w = B u w := fun _ _ => rfl
  have hsmO : ∀ w : O.toSubmodule, IsOpen {k : H | ρO k w = w} := by
    intro w
    convert hsm w.1 using 1
    ext k
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← hρO, h], fun h => Subtype.ext (by rw [hρO, h])⟩
  have hfdO : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρO K) := by
    intro K hK
    haveI := hfd K hK
    have hle : (GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype ≤ GlobalTheory.PRep.fixed ρ K := by
      rintro _ ⟨w, hw, rfl⟩ k
      have h1 := hw k
      show ρ k w.1 = ((1 : K →* ℂˣ) k : ℂ) • w.1
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
      rw [← hρO, h1]
    haveI : FiniteDimensional ℂ ((GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ O.toSubmodule.injective_subtype _).symm
  have hy0 : (⟨y, mem_orbSpan ρ y⟩ : O.toSubmodule) ≠ 0 := fun h => hy (congrArg Subtype.val h)
  obtain ⟨U', P, hU0, hUst, hUirr, -, -, -⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection H O.toSubmodule ρO BO
      (fun u w => hh u w) (fun v => hp v) (fun v h => Subtype.ext (hd v h)) (fun g u w => hi g u w)
      hK0 hsmO hfdO _ hy0
  refine ⟨U'.map O.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ U'.map O.toSubmodule.subtype := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρO g u, hUst g u hu, rfl⟩
  · intro N hNU hN
    let N' : Submodule ℂ O.toSubmodule := N.comap O.toSubmodule.subtype
    have hN'U : N' ≤ U' := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNU hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', ρO g u ∈ N' := fun g u hu => hN g u.1 hu
    have hNe : N'.map O.toSubmodule.subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNU.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple GlobalTheory.DefU GlobalTheory.FrameAut.VecProj

theorem mem_iSup_of_form (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u) (hp : ∀ v, 0 ≤ (B v v).re)
    (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W)
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n))))
    (f : W →ₗ[ℂ] (UA E n → ℂ)) (hfa : ∀ u, IsAutFormU (f u)) (hfe : ∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u))
    (hfK : ∀ u, f u ∈ fixed (RF E n) K) :
    ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧
      (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  classical
  set T : Submodule ℂ (UA E n → ℂ) := ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
    ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)),
    π ⊓ fixed (RF E n) K with hT
  let Y : Submodule ℂ (forms ρ) :=
    { carrier := {g | ∀ u, g.1 u ∈ T}
      add_mem' := fun ha hb u => by
        rw [Submodule.coe_add, LinearMap.add_apply]; exact add_mem (ha u) (hb u)
      zero_mem' := fun u => by simp
      smul_mem' := fun c g hg u => by
        rw [Submodule.coe_smul, LinearMap.smul_apply]; exact T.smul_mem c (hg u) }
  let X := GlobalTheory.PRep.fixed (rep ρ) K
  haveI : FiniteDimensional ℂ X := rep_fd ρ K hK
  haveI : FiniteDimensional ℂ (X ⊓ Y : Submodule ℂ (forms ρ)) := Submodule.finiteDimensional_of_le inf_le_left
  let Bf := form B ρ
  have hBh := form_herm B hh ρ
  have hBp := form_nonneg B hp ρ
  have hBd := form_def B hh hp hd ρ
  have hBi := form_inv B hi ρ
  have memX : ∀ g : forms ρ, (∀ k ∈ K, rep ρ k g = g) → g ∈ X := by
    intro g hg k
    show rep ρ k g = ((1 : K →* ℂˣ) k : ℂ) • g
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hg k k.2
  have ofX : ∀ g ∈ X, ∀ k ∈ K, rep ρ k g = g := by
    intro g hg k hk
    have h1 := hg ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  let ff : forms ρ := ⟨f, hfA⟩
  have hffX : ff ∈ X := by
    refine memX ff fun k hk => Subtype.ext (LinearMap.ext fun u => ?_)
    have h1 := hfK u ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  suffices hY : ff ∈ Y from hY
  by_contra hffY
  obtain ⟨m, hm, hmo⟩ := exists_orth_proj Bf hBd (X ⊓ Y) ff
  obtain ⟨y, hy⟩ : ∃ y, y = ff - m := ⟨_, rfl⟩
  have hyX : y ∈ X := hy ▸ sub_mem hffX (Submodule.mem_inf.1 hm).1
  have hy0 : y ≠ 0 := by
    intro h
    apply hffY
    rw [hy, sub_eq_zero] at h
    rw [h]
    exact (Submodule.mem_inf.1 hm).2
  obtain ⟨U, hU0, hUO, hUst, hUirr⟩ := exists_irred_le_orbSpan (rep ρ) Bf hBh hBp hBd hBi (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n)
    (rep_smooth ρ) (rep_fd ρ) y hy0
  have hadm := GlobalTheory.AdmissibleProjection.hadm_of (rep ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ)
  let Z : Subrepresentation (rep ρ) := ⟨U, fun g _ hv => hUst g _ hv⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.AdmissibleProjection.exists_proj (rep ρ) Bf hBd hBi hadm Z
  obtain ⟨z, hz⟩ : ∃ z, z = P y := ⟨_, rfl⟩
  have hzU : z ∈ U := hz ▸ hP1 y
  have hzX : z ∈ X := memX z fun k hk => by rw [hz, ← hP3, ofX y hyX k hk]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hU0
    have hyo : ∀ w ∈ Z.toSubmodule, Bf w y = 0 := by
      intro w hw
      have := hP2 y w hw
      rwa [← hz, h0, sub_zero] at this
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hle : (orbSpan (rep ρ) y).toSubmodule ≤ LinearMap.ker (Bf w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable (rep ρ) Bf hBi Z y hyo g w hw
    exact hBd _ (hle (hUO hw))

  let M : Submodule ℂ (W →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU (E := E) (n := n), ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU (E := E) (n := n), ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W ρ hsp M hM0 hMf hMk hMirr
  have hzY : z ∈ Y := by
    intro u
    have hmemπ : z.1 u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} :=
      Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, u, rfl⟩
    have hfixu : z.1 u ∈ fixed (RF E n) K := by
      intro k
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      have h1 := congrArg (fun g : forms ρ => g.1 u) (ofX z hzX k k.2)
      exact h1
    have hidx : IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
        ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
          ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u) :=
      ⟨hπ, z.1, fun h => hz0 (Subtype.ext h), fun v => Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, v, rfl⟩, z.2.2⟩
    exact (le_iSup₂ (f := fun (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
      ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)) =>
      π ⊓ fixed (RF E n) K) _ hidx) ⟨hmemπ, hfixu⟩
  have hzm : Bf z y = 0 := hy ▸ hmo z ⟨hzX, hzY⟩
  have hzz : Bf z z = 0 := by
    have h2 := hP2 y z hzU
    rw [← hz, map_sub, hzm, zero_sub, neg_eq_zero] at h2
    exact h2
  exact hz0 (hBd z hzz)

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.DefU

theorem mem_iSup_fixed_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  intro E _ _ _ n W _ _ _ ρ hsp K hK f hfa hfe hfK
  obtain ⟨B, hh, hp, hd, hi⟩ := _root_.GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  exact mem_iSup_of_form E n B hh hp hd hi W ρ hsp K hK f hfa hfe hfK

end GlobalTheory.FrameAut.VecSemis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermForm
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGram

theorem form_eq_hermForm {K : Type} [Field K] {n g m : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Wc : Fin n → Fin g → ℂ)
    (hform : ∀ i j, h.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (Wc j) (Wc i))
    (v : Fin m → Fin n → K) (i j : Fin m) :
    h.form σ (v i) (v j) = Real.pi * hermForm Hm (∑ k, σ (v j k) • Wc k) (∑ k, σ (v i k) • Wc k) := by
  have hsum : ∀ a : Fin n → K, a = ∑ k, a k • Pi.single k (1 : K) := fun a => by
    ext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum (v i), hsum (v j)]
  rw [GlobalTheory.HermFamFrame.form_sum_left]
  simp_rw [GlobalTheory.HermFamFrame.form_sum_right, hform]
  simp only [hermForm, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul, dotProduct_sum,
    sum_dotProduct, smul_dotProduct, dotProduct_smul, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

theorem gram_det_re_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → (h.gram σ v).det.re = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL K _ _ _ y B t₀ m1 m2 F h hH ρ v hv σ hσ φ hφ z hz k w W Wu hzx C hC
  obtain ⟨Q, ψ, v', u, Hm, χ, Wc, hfib, hAH, hvec, hform⟩ := hH σ
  obtain ⟨T, m, u', χ', hA', hw'⟩ := _root_.GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb E H Dw l Xo c r _ _ hL.pos k w W Wu ρ z hzx C hC
  obtain ⟨f, hf, hLB, hq⟩ := _root_.GlobalTheory.PtDeg.fibre_iso_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ v hv σ φ hφ z hz Q ψ v' hfib (fun i => (hvec i).1) T m
  choose w' hw'1 hw'2 using hw'
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hfib.2.1 (hvec i).1 (F.basis.1 i)
  obtain ⟨Lm, hL1, hL2⟩ := _root_.GlobalTheory.LieGramLift.exists_lift Q T.pol W.g u Hm χ u' Wu.Hm χ' hAH hA' f hf hLB F.P₀.g v' Wc
    (fun i => ⟨htan i, (hvec i).2⟩) (Dw.mult ρ) (fun i k => σ (v i k)) w' _ hw'2
    (fun i q hq' => hq i q hq' (w' i) (hw'1 i))
  congr 2
  ext i j
  simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  rw [form_eq_hermForm h σ Hm Wc hform v i j, ← hL1, hL2, hL2]

end GlobalTheory.LieGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := _root_.GlobalTheory.HoweR.fock_lie_wts_comm P Q R S
  obtain ⟨hStab, hAdm⟩ := _root_.GlobalTheory.HoweR.coinv_stab_adm P Q R S x
  obtain ⟨α, β, hq⟩ := _root_.GlobalTheory.HoweR.SecondQuad.qop_mem_coinv P Q R S x
  obtain ⟨α', β', hqt⟩ := _root_.GlobalTheory.HoweR.QuadT.negT_fockAct2_quad P Q R S x
  refine ⟨⟨hLie, hWt, _root_.GlobalTheory.HoweR.fock_locU P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, _root_.GlobalTheory.HoweR.coinv_cycMod P Q R S x⟩

end GlobalTheory.HoweR
end

