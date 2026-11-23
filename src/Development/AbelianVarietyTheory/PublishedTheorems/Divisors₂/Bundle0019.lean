module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.Published

def SemiAbelianLieSeminegative : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)],
    SmoothOfRelativeDimension 1 (strHom k (X := C)) → IsProjOver (strHom k (X := C)) → GeometricallyConnected (strHom k (X := C)) →
    ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (W : C.Modules) (r : ℕ), IsVB W r →
      ∀ i : W ⟶ Lie G, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

end GlobalTheory.Published

namespace GlobalTheory.LieSemineg

section Curve

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]

theorem isIntegral_curve (hs : SmoothOfRelativeDimension 1 (strHom k (X := C)))
    (hc : GeometricallyConnected (strHom k (X := C))) : IsIntegral C :=
  have : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  isIntegral_of_smooth_of_geometricallyConnected (strHom k C)

theorem dim_curve [Nonempty C] (hs : SmoothOfRelativeDimension 1 (strHom k (X := C))) : topologicalKrullDim C = 1 := by
  have key : topologicalKrullDim (Set.univ : Set C) = (1 : ℕ) := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens (Opens.mem_top x)
    replace hU : IsAffineOpen (X := C) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(C, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ _ _ hs U hU ⟨x, hx⟩)
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : C → C)) Topology.IsEmbedding.id Set.range_id).symm.trans key

theorem interNum_det_dual (hp : IsProjOver (strHom k (X := C))) (hd : topologicalKrullDim C = 1) {W : C.Modules} {r : ℕ}
    (hW : IsVB W r) : interNum k (structureModule C) ![det (VB.dual W) r] =
      -interNum k (structureModule C) ![det W r] := by
  obtain ⟨_, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have e := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hW.dual.isLB_det hW.isLB_det
    (by
      have heq : cls (CechPic.dual (det W r)) (isLB_dual hW.isLB_det) =
          cls (det (VB.dual W) r) hW.dual.isLB_det :=
        (cls_eq_iff (isLB_dual hW.isLB_det) hW.dual.isLB_det).2 hW.lbIso_det_dual
      rw [← heq]
      exact (cls_dual_add hW.isLB_det).symm)
  rw [interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv C)) 0 rfl] at e
  omega

end Curve

theorem exists_det_ne_zero_field {K ι : Type} [Field K] [Fintype ι] {r : ℕ} (N : Matrix (Fin r) ι K)
    (hN : LinearIndependent K N.row) : ∃ σ : Fin r → ι, (N.submatrix id σ).det ≠ 0 := by
  by_contra! H
  have hs : Submodule.span K (Set.range N.col) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [← Matrix.rank_eq_finrank_span_cols, hN.rank_matrix, Module.finrank_fintype_fun_eq_card])
  have e : (Pi.basisFun K (Fin r)).det.toMultilinearMap = 0 := by
    refine MultilinearMap.ext_of_span_eq_top (γ := fun _ => ι) (g := fun _ j => N.col j) (fun _ => hs) fun σ => ?_
    rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_apply, ← H σ]
    rfl
  have h₂ := DFunLike.congr_fun e ⇑(Pi.basisFun K (Fin r))
  rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_self] at h₂
  exact one_ne_zero h₂

theorem exists_det_ne_zero {A ι : Type} [CommRing A] [IsDomain A] [Fintype ι] {r : ℕ} (M : Matrix (Fin r) ι A)
    (h : LinearIndependent A M.row) : ∃ σ : Fin r → ι, (M.submatrix id σ).det ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_det_ne_zero_field (M.map (algebraMap A (FractionRing A)))
    ((linearIndependent_algebraMap_comp_iff (S := FractionRing A) (v := M.row)).2 h)
  refine ⟨σ, fun h₀ => hσ ?_⟩
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h₀, map_zero]

end GlobalTheory.LieSemineg

namespace GlobalTheory.Published.SemiAbelianLieSeminegative

open GlobalTheory.LieSemineg

variable (h : SemiAbelianLieSeminegative) {k : Type} [Field k] [CharZero k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  (hs : SmoothOfRelativeDimension 1 (strHom k (X := C))) (hp : IsProjOver (strHom k (X := C)))
  (hc : GeometricallyConnected (strHom k (X := C))) (G : Over C) [GrpObj G] [IsSemiAbelian G]

include h hs hp hc

theorem dual_det_nonneg {W : C.Modules} {r : ℕ} (hW : IsVB W r) (i : W ⟶ Lie G) [Mono i] :
    0 ≤ interNum k (structureModule C) ![CechPic.dual (det W r)] := by
  have := isIntegral_curve hs hc
  have e := h k C hs hp hc G W r hW i inferInstance
  have e' : interNum k (structureModule C) ![CechPic.dual (det W r)] =
      interNum k (structureModule C) ![det (VB.dual W) r] := interNum_congr_lbIso k (structureModule C) (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hW.dual.isLB_det) fun j => by fin_cases j; exact hW.lbIso_det_dual
  rw [e', interNum_det_dual hp (dim_curve hs) hW]
  omega

end GlobalTheory.Published.SemiAbelianLieSeminegative
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published.HeckeFEModel

section
variable {E : Type} [Field E] [NumberField E]

theorem exists_exponents (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ v, ExpAt χ v (a v) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ
  have hE : ∀ v, ExpAt χ v (Nat.find (h2 v)) := fun v m => by
    refine ⟨fun h => Nat.find_min' _ h, fun h x hx hx' => Nat.find_spec (h2 v) x hx (hx'.trans ?_)⟩
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨Finsupp.ofSupportFinite (fun v => Nat.find (h2 v)) (h1.subset fun v hv hu => hv ?_), fun v => hE v⟩
  exact (hE v).unique ((expAt_zero_iff χ v).2 hu)

theorem hasInf_inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {χ : HChar E} {n : I → ℤ}
    (h : Formalism.L2.Host.HChar.HasInf χ φ n) : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -n i) := fun k => by
  rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]

theorem isUnitary_inv {χ : HChar E} (h : IsUnitary χ) : IsUnitary χ⁻¹ := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem zero_iff (h : HeckeFunctionalEquationAbs) [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} {Λ Λ' : ℂ → ℂ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) (h1 : IsCompletedL χ n Λ)
    (h2 : IsCompletedL χ⁻¹ (fun i => -n i) Λ') (s : ℂ) : Λ s = 0 ↔ Λ' (1 - s) = 0 := by
  obtain ⟨a, ha⟩ := exists_exponents χ
  obtain ⟨ε, hε, hs⟩ := h E I φ hφ χ n a Λ Λ' hu hi hn ha h1 h2
  have h0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA : ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine mul_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero E)) ?_
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  rw [hs s, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff]
  tauto

end

section
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.DefU.NonTriv

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

end

end GlobalTheory.Published.HeckeFEModel

end
end

