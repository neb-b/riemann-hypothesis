module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowBasisFromReferenceTupleQuotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.RowBasis

theorem exists_basis_semi {E W : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W] {N : ℕ}
    (s : ℂ →+* ℂ) (hs : ∀ z, s (s z) = z) (g : (Fin N → ℂ) → W)
    (gadd : ∀ z z', g (z + z') = g z + g z') (gsmul : ∀ (a : ℂ) z, g (a • z) = s a • g z)
    (ginj : ∀ z, g z = 0 → z = 0) (jE : E →ₗ[ℂ] W) (hj : Function.Injective jE)
    (hmem : ∀ z, ∃ w, jE w = g z) (hsurj : ∀ w, ∃ z, jE w = g z) :
    ∃ c : Module.Basis (Fin N) ℂ E, ∀ z, jE (∑ i, s (z i) • c i) = g z := by
  choose c0 hc0 using fun i : Fin N => hmem (Pi.single i 1)
  let gA : (Fin N → ℂ) →+ W := AddMonoidHom.mk' g gadd
  have gsum : ∀ z, g z = ∑ i, s (z i) • g (Pi.single i 1) := by
    intro z
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc g z = gA (∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := by rw [← hz]; rfl
      _ = ∑ i, gA (z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := map_sum gA _ _
      _ = ∑ i, s (z i) • g (Pi.single i 1) := Finset.sum_congr rfl fun i _ => gsmul _ _
  have key : ∀ z, jE (∑ i, s (z i) • c0 i) = g z := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gsum z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hc0 i]
  have hli : LinearIndependent ℂ c0 := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 : g (fun k => s (a k)) = 0 := by
      rw [← key]
      simp only [hs, ha, map_zero]
    have h1 := congrFun (ginj _ h0) i
    have h2 : s (s (a i)) = s 0 := congrArg s h1
    rwa [hs, map_zero] at h2
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range c0) := by
    intro w _
    obtain ⟨z, hz⟩ := hsurj w
    have hw : w = ∑ i, s (z i) • c0 i := hj (by rw [key, hz])
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, fun z => ?_⟩
  simp only [Module.Basis.mk_apply]
  exact key z

end GlobalTheory.Mem.R3.Rw.RowBasis

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 2000000 in
theorem rrT_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (E : Hs) (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0), Function.Injective jE → LinearMap.range jE = (y.C F.lv2).EEc b → ∃ n c Xo, RrT F y b jE n c Xo := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH y b E jE hinj hrange
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr b := (hCx.what₂ b).1
  have hW : (lv (F.fc (R.toCx3 F).zs) b).WF := hCx.wf b
  have hp : (R.toCx3 F).H4pos := hCx.h4pos
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (y.C F.lv2).EEc b = (R.EEat (R.toRealDat.levR F.lv2 b)).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hEEl : (R.toCx3 F).EEl b =
      Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e) := rfl
  set s : Bool := twAt D.what₂.embLL A3.A.v0 with hs
  let g : (Fin ((R.toCx3 F).data F.cr b).D → ℂ) → (y.C F.lv2).Amb 0 := fun z =>
    PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)))
  have gadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    have h := map_add ((R.toCx3 F).iC F.cr b A3.A.μ0) z z'
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_add R.HE.e _ _)).trans (map_add _ _ _))
  have gsmul : ∀ (a : ℂ) z, g (a • z) = Formalism.IndefR.Links.cj s a • g z := by
    intro a z
    have h := map_smul ((R.toCx3 F).iC F.cr b A3.A.μ0) a z
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_smul R.HE.e (Formalism.IndefR.Links.cj s a) _)).trans (map_smul _ _ _))
  have ginj : ∀ z, g z = 0 → z = 0 := by
    intro z hz
    have h1 : R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)) = 0 :=
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).map_eq_zero_iff.1 hz
    have h3 : Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z) = 0 :=
      hE.1 (h1.trans (map_zero R.HE.e).symm)
    have h4 : (R.toCx3 F).iC F.cr b A3.A.μ0 z = 0 := h3
    exact h2.1 (h4.trans (map_zero _).symm)
  have hmem : ∀ z, ∃ w, jE w = g z := by
    intro z
    have h1 : (R.toCx3 F).iC F.cr b A3.A.μ0 z ∈ (R.toCx3 F).EEl b := by
      rw [← h2.2.2]; exact LinearMap.mem_range_self _ z
    rw [hEEl] at h1
    have h5 : g z ∈ (y.C F.lv2).EEc b := by
      rw [hEEc]
      exact ⟨_, h1, rfl⟩
    rw [← hrange] at h5
    exact h5
  have hsurj : ∀ w, ∃ z, jE w = g z := by
    intro w
    have h1 : jE w ∈ (y.C F.lv2).EEc b := hrange ▸ LinearMap.mem_range_self jE w
    rw [hEEc] at h1
    obtain ⟨u, hu, hwu⟩ := h1
    have hu' : u ∈ LinearMap.range R.HE.e := by
      rw [hE.2.1]
      exact GlobalTheory.Mem.Th.EEat_le_triv R.toRealDat _ hu
    obtain ⟨h, rfl⟩ := hu'
    have hh : Tw.mk s h ∈ (R.toCx3 F).EEl b := by rw [hEEl]; exact hu
    rw [← h2.2.2] at hh
    obtain ⟨z, hz⟩ := hh
    refine ⟨z, ?_⟩
    rw [← hwu]
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) hz).symm
  obtain ⟨c, hc⟩ := RowBasis.exists_basis_semi (Formalism.IndefR.Links.cj s) (Formalism.IndefR.Links.cj_cj s) g gadd gsmul ginj jE hinj hmem hsurj
  have hsg : ∀ a : D.what₂.LL, Formalism.IndefR.Links.cj s (A3.A.v0.embedding a) = D.what₂.embLL a := by
    intro a
    rw [emb_eq D.what₂.embLL A3.A.v0 a, sgAt_mk D.what₂.embLL R.hv0, Formalism.IndefR.Links.cj_cj]
  refine ⟨((R.toCx3 F).data F.cr b).D, c,
    fun v => (((R.toCx3 F).data F.cr b).XE v).submatrix (Fin.cast rfl) (Fin.cast rfl), ?_⟩
  refine ⟨rfl, fun x => ?_, fun v => ⟨rfl, ?_⟩⟩
  · have := hc (cpt A3.A.v0.embedding x)
    simp only [cpt, hsg] at this
    exact this.trans rfl
  · have hdet := Formalism.IndefR.Cx.PrincipalLevelLattice.frames (R.toCx3 F) F.cr b hW h2 hp v
    have hs := Matrix.det_submatrix_equiv_self (finCongr (rfl : ((R.toCx3 F).data F.cr b).D = ((R.toCx3 F).data F.cr b).D))
      (((R.toCx3 F).data F.cr b).XE v)
    exact (congrArg IsUnit hs).mpr hdet

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.Dom

theorem mem_O_of_forall_dvr {F : Type} [Field F] (Y : Var F) (y : (ratOf Y).Z) (x : Y.Fn)
    (hx : ∀ V : ValuationSubring Y.Fn, IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap ((ratOf Y).O y) Y.Fn) ≤ V.toLocalSubring → x ∈ V) :
    x ∈ (ratOf Y).O y := by
  haveI := (ratOf Y).lft
  haveI : IsLocallyNoetherian (ratOf Y).Z := LocallyOfFiniteType.isLocallyNoetherian (ratOf Y).s
  haveI : IsNoetherianRing ((ratOf Y).O y) :=
    isNoetherianRing_of_ringEquiv _ ((ratOf Y).stalkEquiv y)
  haveI : Algebra.EssFiniteType ((ratOf Y).O y) Y.Fn :=
    Algebra.EssFiniteType.of_isLocalization Y.Fn (nonZeroDivisors ((ratOf Y).O y))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (ratOf Y).Z := fun z =>
    ⟨(Y.isNormalScheme).isDomain_stalk z, (Y.isNormalScheme).isIntegrallyClosed_stalk z⟩
  haveI := RatModel.isIntegrallyClosed_O hN y
  by_contra hn
  have hi : ¬ IsIntegral ((ratOf Y).O y) x := fun h => by
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact hn a.2
  obtain ⟨V, h1, h2, h3⟩ := GlobalTheory.exists_discreteValuationSubring_dominating_notMem hi
  exact h3 (hx V h1 h2)

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

theorem exists_pt_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z)
    (V : ValuationSubring Ω) (hV : LocalSubring.range (algebraMap (M.O z) Ω) ≤ V.toLocalSubring) :
    ∃ v : Sp V ⟶ M.Z, v (IsLocalRing.closedPoint V) = z ∧ spMap (algebraMap V Ω) ≫ v = M.pt ∧
      ∃ σ : IsLocalRing.ResidueField (M.Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V,
        spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ spMap (IsLocalRing.residue _) ≫ M.Z.fromSpecStalk z := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff _ V).1 hV
  let ι : M.O z →+* V := (algebraMap (M.O z) Ω).codRestrict V h1
  haveI hι : IsLocalHom ι := ⟨fun r hr => by
    by_contra hn
    obtain ⟨_, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 (h2 r hn)
    exact hm hr⟩
  let g : M.Z.presheaf.stalk z →+* V := ι.comp (M.stalkEquiv z).toRingHom
  haveI : IsLocalHom g := ⟨fun a ha =>
    (isUnit_map_iff (M.stalkEquiv z) a).1 (IsLocalHom.map_nonunit (f := ι) _ ha)⟩
  refine ⟨spMap g ≫ M.Z.fromSpecStalk z, ?_, ?_, IsLocalRing.ResidueField.map g, ?_⟩
  · show M.Z.fromSpecStalk z (spMap g (IsLocalRing.closedPoint V)) = z
    rw [show spMap g (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ from IsLocalRing.comap_closedPoint g]
    exact Scheme.fromSpecStalk_closedPoint
  · have e : (algebraMap V Ω).comp g = M.stalkHom z := rfl
    have e2 : spMap (M.stalkHom z) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
        Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z)) := by
      rw [RatModel.stalkHom]
      show Spec.map _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_comp]
      rfl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    change spMap (M.stalkHom z) ≫ _ = _
    rw [e2, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo M.pt
  · rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
  {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}

theorem coBear_swap {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ p₁' : Sp K ⟶ Y₁.X}
    {p₂ p₂' : Sp K ⟶ Y₂.X} (hx : x = x') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂' p₁' := by
  subst hx hp₁ hp₂
  obtain ⟨A, hA, g, hg, b₁, b₂⟩ := h
  exact ⟨A, hA, g, hg, b₂, b₁⟩

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle


open GlobalTheory.FlagBundle.Dom in
theorem dominates_O (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) (ψ : Y₂.Fn →ₐ[F] Y₁.Fn) (hψ : ψ.comp φ₂ = φ₁)
    (hg : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt))
    (y : Y₁.X) : ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  let κ := IsLocalRing.ResidueField (Y₁.X.presheaf.stalk y)
  let py : Sp κ ⟶ Y₁.X := spMap (IsLocalRing.residue _) ≫ Y₁.X.fromSpecStalk y
  obtain ⟨A, hA, h, hh, hb⟩ := _root_.GlobalTheory.FlagBundle.bears_self F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ κ py
  obtain ⟨s, ⟨hs, hsb⟩, -⟩ := h₂.2.2 κ (py ≫ f₁) A hA h hh
  refine ⟨s (IsLocalRing.closedPoint κ), fun a ha => ?_⟩
  refine mem_O_of_forall_dvr Y₁ y (ψ a) fun V _ hV => ?_
  obtain ⟨v, -, hv1, σ, hv2⟩ := exists_pt_of_le (ratOf Y₁) y V hV
  haveI : IsProper (f₂ ≫ X.str) := by
    rw [show f₂ ≫ X.str = Y₂.str from h₂.1.inducedModelMorphism_comp_structureMap]
    infer_instance
  haveI : IsProper f₂ := IsProper.of_comp f₂ X.str
  have hψ' : spMap ψ.toRingHom ≫ spMap φ₂.toRingHom = spMap φ₁.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
    rfl
  have hq : (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    have e1 : (ratOf Y₂).pt ≫ f₂ = spMap φ₂.toRingHom ≫ (ratOf X).pt := h₂.1
    have e2 : (ratOf Y₁).pt ≫ f₁ = spMap φ₁.toRingHom ≫ (ratOf X).pt := h₁.1
    erw [Category.assoc, e1, ← Category.assoc, hψ', ← e2, ← Category.assoc, hv1]
  obtain ⟨ℓ, ⟨hℓ1, hℓ2⟩, -⟩ :=
    GlobalTheory.ModelPoints.existsUnique_extension f₂ (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) (v ≫ f₁) hq
  have hinc := _root_.GlobalTheory.FlagBundle.coBear_closedPoint F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v ℓ hℓ1.symm
    (by erw [hℓ2, ← Category.assoc, hv1]; exact hg)
  have hbc := _root_.GlobalTheory.FlagBundle.coBear_spMap F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ κ (IsLocalRing.ResidueField V) σ
    (py ≫ f₁) py s ⟨A, hA, h, hh, hb, hsb⟩
  have hpv : spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ py := hv2
  have E1 : (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hpv)))
  have E2 : (spMap σ ≫ s) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  have E3 : spMap (IsLocalRing.residue V) ≫ v ≫ f₁ = (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ :=
    (congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1.symm).trans (Category.assoc _ _ _).symm
  have E4 : spMap σ ≫ py ≫ f₁ = (spMap σ ≫ s) ≫ f₂ :=
    (congrArg (spMap σ ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm
  have e : spMap (IsLocalRing.residue V) ≫ ℓ = spMap σ ≫ s :=
    _root_.GlobalTheory.FlagBundle.eq_of_coBear F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ h₂ h₁ _ (spMap (IsLocalRing.residue V) ≫ ℓ)
      (spMap σ ≫ s) (spMap σ ≫ py) E1 E2 (coBear_swap E3 hpv rfl hinc) (coBear_swap E4 rfl rfl hbc)
  have hℓc : ℓ (IsLocalRing.closedPoint V) = s (IsLocalRing.closedPoint κ) := by
    have h3 : ℓ (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) =
        s (spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) :=
      congrArg (fun t : Sp (IsLocalRing.ResidueField V) ⟶ Y₂.X =>
        t (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) e
    have h4 : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
    have h5 : spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint κ :=
      Subsingleton.elim (α := PrimeSpectrum κ) _ _
    rw [h4, h5] at h3
    exact h3
  have hsp : ℓ (IsLocalRing.closedPoint V) ⤳ s (IsLocalRing.closedPoint κ) := hℓc ▸ specializes_rfl
  have k1 := RatModel.val_spMap_comp (M := ratOf Y₂) (algebraMap V Y₁.Fn) ℓ hsp ⟨a, ha⟩
  have k2 := RatModel.val_spMap_comp (M := ratOf Y₂) ψ.toRingHom (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, ha⟩
  have k4 := (RatModel.valLoc_eq_val (M := ratOf Y₂) (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩).trans
    (RatModel.val_pt (M := ratOf Y₂) a)
  have k3 : ψ a = algebraMap V Y₁.Fn (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩) := by
    calc ψ a = ψ.toRingHom (RatModel.valLoc (ratOf Y₂).pt _
          ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩) :=
          (congrArg ψ.toRingHom k4).symm
      _ = (ratOf Y₂).val (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) a := k2.symm
      _ = (ratOf Y₂).val (spMap (algebraMap V Y₁.Fn) ≫ ℓ) a :=
          congrArg (fun t : Sp Y₁.Fn ⟶ Y₂.X => (ratOf Y₂).val t a) hℓ2.symm
      _ = _ := k1
  rw [k3]
  exact (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩).2

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem coBear_comp_of_isHom : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ ψ hψ hgen g hg K _ p
  have hgf : g ≫ f₂ = f₁ := by
    have := h₂.1.comp hg
    rw [hψ] at this
    exact this.unique h₁.1

  let y : Y₁.X := p (IsLocalRing.closedPoint K)
  let R := Y₁.X.presheaf.stalk y
  let v₁ : Sp R ⟶ Y₁.X := Y₁.X.fromSpecStalk y
  have hpt : spMap (algebraMap R Y₁.Fn) ≫ v₁ = (ratOf Y₁).pt :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hinc := _root_.GlobalTheory.FlagBundle.coBear_closedPoint F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ R Y₁.Fn v₁ (v₁ ≫ g)
    (by rw [Category.assoc, hgf]) (by
      have e1 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ f₁ = (ratOf Y₁).pt ≫ f₁ := by
        rw [← Category.assoc]; exact congrArg (· ≫ f₁) hpt
      have e2 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ g = spMap ψ.toRingHom ≫ (ratOf Y₂).pt := by
        rw [← Category.assoc, hpt]; exact hg
      rw [e1, hpt, e2]; exact hgen)

  let c := Scheme.stalkClosedPointTo (R := .of K) p
  let σ : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift c.hom
  have hσ : σ.comp (IsLocalRing.residue R) = c.hom := IsLocalRing.ResidueField.lift_comp_residue c.hom
  have hp : spMap σ ≫ spMap (IsLocalRing.residue R) ≫ v₁ = p := by
    rw [← Category.assoc, ← spMap_comp, hσ]
    exact spMap_stalkClosedPointTo p
  have hbc := _root_.GlobalTheory.FlagBundle.coBear_spMap F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ (IsLocalRing.ResidueField R) K σ _ _ _ hinc
  rw [← hp]
  simpa only [Category.assoc] using hbc

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem CoBear₂ : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ g hg hco K _
  have hcomp : ∀ p : Sp K ⟶ Y₁.X, p ≫ f₁ = (p ≫ g) ≫ f₂ := by
    intro p; rw [Category.assoc, hg]
  constructor
  · intro p p' hpp'
    simp only at hpp'
    have h1 := hco K p
    have h2 := hco K p'
    rw [← hpp'] at h2
    exact _root_.GlobalTheory.FlagBundle.eq_of_coBear F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p p' (p ≫ g) (hcomp p)
      (by rw [hcomp p', hpp']) h1 h2
  · intro w
    obtain ⟨A, hA, h, hh, hw⟩ := _root_.GlobalTheory.FlagBundle.bears_self F ι m X Y₂ Eb S₂ φ₂ f₂ hR₂ K w
    obtain ⟨p, ⟨hpx, hpA⟩, -⟩ := hR₁.2.2 K (w ≫ f₂) A hA h hh
    obtain ⟨B, hB, h', -, hpB, hqB⟩ := hco K p
    have hA' : A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)) := by rw [hpx]; exact hA
    have hqA : Bears S₂ φ₂ A h (p ≫ g) :=
      _root_.GlobalTheory.FlagBundle.Bears.transfer F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p (p ≫ g) (hcomp p) A hA' B hB h h'
        hpA hpB hqB
    obtain ⟨q, -, hq⟩ := hR₂.2.2 K (w ≫ f₂) A hA h hh
    refine ⟨p, ?_⟩
    simp only
    rw [hq (p ≫ g) ⟨by rw [← hcomp p, hpx], hqA⟩, hq w ⟨rfl, hw⟩]

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundlePointAtGenericLiftImage
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagBundle

theorem exists_spMap_fromSpecResidueField {Z : Scheme.{0}} (y : Z) {K : Type} [Field K] (p : Sp K ⟶ Z)
    (hp : p (IsLocalRing.closedPoint K) = y) :
    ∃ σ : Z.residueField y →+* K, spMap σ ≫ Z.fromSpecResidueField y = p := by
  subst hp
  exact ⟨(Z.descResidueField (Scheme.stalkClosedPointTo p)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z p⟩

theorem coBear_swap {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
    {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}
    {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ : Sp K ⟶ Y₁.X} {p₂ : Sp K ⟶ Y₂.X}
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) (hx : x = x') : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂ p₁ := by
  subst hx
  obtain ⟨A, hA, g, hg, h₁, h₂⟩ := h
  exact ⟨A, hA, g, hg, h₂, h₁⟩

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.conclusion : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ r hr hrc K _ p p' hp hpp' hc
  set y₁ := r (IsLocalRing.closedPoint Y₂.Fn)
  let c : Sp (Y₁.X.residueField y₁) ⟶ Y₁.X := Y₁.X.fromSpecResidueField y₁
  obtain ⟨τ, hτ⟩ := exists_spMap_fromSpecResidueField y₁ r rfl
  obtain ⟨σ, hσ⟩ := exists_spMap_fromSpecResidueField y₁ p hp
  obtain ⟨A, hA, g, hg, hb₁⟩ := _root_.GlobalTheory.FlagBundle.bears_self F ι m X Y₁ Eb S₁ φ₁ f₁ hR₁ _ c
  obtain ⟨s, ⟨hs, hb₂⟩, -⟩ := hR₂.2.2 _ (c ≫ f₁) A hA g hg
  have hcs : CoBear Eb S₁ φ₁ S₂ φ₂ (c ≫ f₁) c s := ⟨A, hA, g, hg, hb₁, hb₂⟩
  have hτc := _root_.GlobalTheory.FlagBundle.coBear_spMap F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ τ _ _ _ hcs
  have hσc := _root_.GlobalTheory.FlagBundle.coBear_spMap F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ σ _ _ _ hcs
  have hτ' : spMap τ ≫ c = r := hτ
  have hσ' : spMap σ ≫ c = p := hσ
  rw [hτ'] at hτc
  rw [hσ'] at hσc
  have e₁ : (spMap τ ≫ s) ≫ f₂ = r ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hτ']
  have e₂ : (spMap σ ≫ s) ≫ f₂ = p ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hσ']
  have k₁ : spMap τ ≫ s = (ratOf Y₂).pt :=
    _root_.GlobalTheory.FlagBundle.eq_of_coBear F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ r e₁ hr.symm
      (coBear_swap hτc (by rw [Category.assoc, hs])) (coBear_swap hrc hr)
  have k₂ : p' = spMap σ ≫ s :=
    _root_.GlobalTheory.FlagBundle.eq_of_coBear F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ p hpp'.symm e₂
      (coBear_swap hc hpp') (coBear_swap hσc (by rw [Category.assoc, hs]))
  have hgen : s (IsLocalRing.closedPoint _) = genericPoint Y₂.X := by
    have e : (spMap τ ≫ s) (IsLocalRing.closedPoint Y₂.Fn) = s (IsLocalRing.closedPoint _) := by
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
    rw [← e, k₁]
    exact Scheme.fromSpecStalk_closedPoint
  rw [k₂, ← hgen]
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameCStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  first | exact @GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | exact GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | (intros; apply GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_bounded_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧ ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  first | exact @GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | exact GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | (intros; apply GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type <;> assumption)
end

