module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitFinCutIdeleOfNotMem
section
noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU Filter Topology
open GlobalTheory.LocalGlobalChar (eps ev_ind tendsto_eps_tens)

section KFinite

variable {G : Type} [Group G] {K : Subgroup G}

theorem IsKFinite.mul {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K fun g => Φ g * Ψ g := by
  obtain ⟨W, hf, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', hf', hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W * W', Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hf).mul (Module.Finite.iff_fg.1 hf')),
    fun k hk => Submodule.mul_mem_mul (hW k hk) (hW' k hk)⟩

end KFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ideles

def cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) : (AF F ⊗[F] E)ˣ :=
  (∏ w, ideleAtInf F E w (unitInf F E w x)) * ∏ v ∈ S, ideleAt F E v (unitFin F E v x)

omit [NumberField E] in
theorem cutIdele_inv (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    cutIdele S x⁻¹ = (cutIdele S x)⁻¹ := by
  simp only [cutIdele, map_inv, Finset.prod_inv_distrib, mul_inv]

omit [NumberField E] in
theorem unitInf_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) (w : InfinitePlace F) :
    unitInf F E w (cutIdele S x) = unitInf F E w x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]
  simp

omit [NumberField E] in
theorem unitFin_cutIdele_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : unitFin F E v (cutIdele S x) = unitFin F E v x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single v (fun u _ hu => unitFin_ideleAt_ne hu.symm _) (fun h => absurd hv h)]
  simp

omit [NumberField E] in
theorem unitFin_cutIdele_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : unitFin F E v (cutIdele S x) = 1 := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_one (s := S) (fun u hu => unitFin_ideleAt_ne (ne_of_mem_of_not_mem hu hv).symm _)]
  simp

theorem val_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    (cutIdele S x).1 = algebraMap (AF F) (AF F ⊗[F] E) (eps S) * (x.1 - 1) + 1 := by
  refine adele_ext (fun w => ?_) fun v => ?_
  · have h : compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) = 1 := rfl
    rw [map_add (f := _), map_mul, map_sub, h, map_one, one_mul, sub_add_cancel]
    exact congrArg Units.val (unitInf_cutIdele S x w)
  · have h : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.LocalGlobalChar.ind S) ⊗ₜ[F] (1 : E) := rfl
    rw [map_add (f := _), map_mul, map_sub, h, map_one, ev_ind]
    split_ifs with hv
    · rw [← Algebra.TensorProduct.one_def, one_mul, sub_add_cancel]
      exact congrArg Units.val (unitFin_cutIdele_of_mem x hv)
    · rw [TensorProduct.zero_tmul, zero_mul, zero_add]
      exact congrArg Units.val (unitFin_cutIdele_of_notMem x hv)

theorem tendsto_cutIdele (x : (AF F ⊗[F] E)ˣ) : Tendsto (fun S => cutIdele S x) atTop (𝓝 x) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : ∀ y : (AF F ⊗[F] E)ˣ, Tendsto (fun S => (cutIdele S y).1) atTop (𝓝 y.1) := fun y => by
    have := (tendsto_eps_tens (y.1 - 1)).add_const 1
    rw [show y.1 - 1 + 1 = y.1 by ring] at this
    simpa only [val_cutIdele] using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  simpa only [cutIdele_inv] using h x⁻¹

end Ideles

variable {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)} {μ : (AF F ⊗[F] E)ˣ →* Circle} {s : ℂ}
  {Φi : ∀ w, GArch σ Q w → ℂ} {Φf : ∀ v, GLoc σ Q v → ℂ}

end GlobalTheory.Doubling

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
section
noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def halfInf (F : Type) [Field F] [NumberField F] : (AF F)ˣ where
  val := (algebraMap F (Ainf F) 2⁻¹, 1)
  inv := (algebraMap F (Ainf F) 2, 1)
  val_inv := Prod.ext (by
    change algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1
    rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]) (mul_one _)
  inv_val := Prod.ext (by
    change algebraMap F (Ainf F) 2 * algebraMap F (Ainf F) 2⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]) (mul_one _)

def halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : (AF F ⊗[F] E)ˣ :=
  Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (halfInf F)

open scoped TensorProduct in
open NumberField in
theorem _root_.GlobalTheory.Eis.Conv.sigR_halfE {F E : Type} [Field F] [NumberField F] [Field E]
    [Algebra F E] (σ : E →ₐ[F] E) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ (_root_.GlobalTheory.Eis.Conv.halfE F E).1 =
      (_root_.GlobalTheory.Eis.Conv.halfE F E).1 := by
  simp [_root_.GlobalTheory.Eis.Conv.halfE, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

end GlobalTheory.Eis.Conv

end
end

