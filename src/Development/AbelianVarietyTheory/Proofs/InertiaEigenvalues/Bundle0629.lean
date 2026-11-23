module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def homSpace : Submodule ℂ (Y →ₗ[ℂ] X) where
  carrier := {φ | ∀ h v, φ (ρ h v) = τ (1, h) (φ v)}
  add_mem' := by
    intro a b ha hb h v
    simp [ha h v, hb h v]
  zero_mem' := by intro h v; simp
  smul_mem' := by
    intro c a ha h v
    simp [ha h v]

theorem commute_apply (g : G) (h : H) (x : X) : τ (g, 1) (τ (1, h) x) = τ (1, h) (τ (g, 1) x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem apply_pair (g : G) (h : H) (x : X) : τ (g, h) x = τ (g, 1) (τ (1, h) x) := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def homRep : Representation ℂ G (homSpace τ ρ) where
  toFun g :=
    { toFun := fun φ => ⟨(τ (g, 1)).comp φ.1, fun h v => by
        simp only [LinearMap.comp_apply]
        rw [φ.2 h v, commute_apply]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by
    ext φ v
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    simp [this]
  map_mul' a b := by
    ext φ v
    have : ((a * b, (1 : H)) : G × H) = (a, 1) * (b, 1) := by simp
    show τ (a * b, 1) _ = τ (a, 1) (τ (b, 1) _)
    rw [this, map_mul, Module.End.mul_apply]

@[simp] theorem homRep_apply_coe (g : G) (φ : homSpace τ ρ) :
    ((homRep τ ρ g φ : homSpace τ ρ) : Y →ₗ[ℂ] X) = (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) := rfl

def evMap : (extTensor (homRep τ ρ) ρ).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (homSpace τ ρ).subtype
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro φ v
    obtain ⟨g, h⟩ := gh
    simp only [LinearMap.comp_apply, extTensor_tmul, TensorProduct.lift.tmul, Submodule.subtype_apply,
      homRep_apply_coe]
    rw [φ.2 h v, ← apply_pair]

end GlobalTheory.TensorFactor

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def diffMap (g : G) (φ : homSpace τ ρ) :
    ρ.IntertwiningMap (τ.comp (MonoidHom.inr G H)) where
  toLinearMap := (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) - (φ : Y →ₗ[ℂ] X)
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.inr_apply, map_sub]
    rw [φ.2 h v, commute_apply]

theorem homRep_eq_of_apply_eq [ρ.IsIrreducible] {g : G} {φ : homSpace τ ρ} {y : Y} (hy : y ≠ 0)
    (h : τ (g, 1) ((φ : Y →ₗ[ℂ] X) y) = (φ : Y →ₗ[ℂ] X) y) : homRep τ ρ g φ = φ := by
  rcases Representation.IsIrreducible.injective_or_eq_zero (diffMap τ ρ g φ) with hi | h0
  · refine absurd (hi (a₁ := y) (a₂ := 0) ?_) hy
    simp [diffMap, h]
  · apply Subtype.ext
    ext v
    have := congrArg (fun f => f v) h0
    simpa [diffMap, sub_eq_zero] using this

end GlobalTheory.TensorFactor


open GlobalTheory.TensorFactor in
theorem GlobalTheory.TensorFactor.exists_equiv_extTensor : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  intro G H X Y _ _ _ _ _ _ _ _ _ _ τ ρ hτs hτ hρ hinj hex
  obtain ⟨ι, hι0, hι⟩ := hex
  haveI := hτ
  haveI := hρ
  have hev : Function.Injective (evMap τ ρ) := hinj (homSpace τ ρ) fun φ hφ => hφ
  let ι' : homSpace τ ρ := ⟨ι, hι⟩
  obtain ⟨y0, hy0⟩ : ∃ v, ι v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hι0 (LinearMap.ext h)
  have hy0' : y0 ≠ 0 := fun h => hy0 (by simp [h])
  have hsurj : Function.Surjective (evMap τ ρ) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (evMap τ ρ)).resolve_right fun h0 =>
      hy0 (by simpa [evMap, ι'] using congrArg (fun f => f (ι' ⊗ₜ y0)) h0)
  refine ⟨homSpace τ ρ, inferInstance, inferInstance, homRep τ ρ, ?_, ?_,
    ⟨(Representation.IntertwiningMap.ofBijective (evMap τ ρ) ⟨hev, hsurj⟩).symm⟩⟩
  · refine isSmooth_of_nhds fun φ => ?_
    have hc : Continuous fun g : G => ((g, (1 : H)) : G × H) := by fun_prop
    refine Filter.mem_of_superset (((hτs ((φ : Y →ₗ[ℂ] X) y0)).preimage hc).mem_nhds ?_)
      fun g hg => homRep_eq_of_apply_eq τ ρ hy0' hg
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    show τ ((1 : G), (1 : H)) _ = _
    simp [this]
  · haveI : Nontrivial (Subrepresentation (homRep τ ρ)) := ⟨⊥, ⊤, fun h => by
      have h1 : ι' ∈ (⊤ : Subrepresentation (homRep τ ρ)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : ι' = 0 := (Submodule.mem_bot ℂ).1 h1
      exact hι0 (congrArg Subtype.val h2)⟩
    refine ⟨fun S => ?_⟩
    let U : Subrepresentation τ :=
      { toSubmodule :=
          LinearMap.range ((evMap τ ρ).toLinearMap ∘ₗ LinearMap.rTensor Y S.toSubmodule.subtype)
        apply_mem_toSubmodule := by
          rintro ⟨g, h⟩ _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul ψ z =>
            refine ⟨⟨homRep τ ρ g ψ, S.apply_mem_toSubmodule g ψ.2⟩ ⊗ₜ ρ h z, ?_⟩
            show ((homRep τ ρ g ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) (ρ h z) =
              τ (g, h) (((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z)
            rw [homRep_apply_coe, LinearMap.comp_apply, (ψ : homSpace τ ρ).2 h z, ← apply_pair]
          | add a b ha hb =>
            rw [map_add (f := _), map_add (f := _)]
            exact add_mem ha hb }
    rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
    · left
      apply Subrepresentation.toSubmodule_injective
      refine eq_bot_iff.2 fun ψ hψ => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun z => ?_))
      have hm : (evMap τ ρ).toLinearMap (LinearMap.rTensor Y S.toSubmodule.subtype (⟨ψ, hψ⟩ ⊗ₜ z)) ∈
          U.toSubmodule := ⟨⟨ψ, hψ⟩ ⊗ₜ z, rfl⟩
      rw [hU] at hm
      have h2 := (Submodule.mem_bot ℂ).1 hm
      have h3 : ((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z = 0 := by simpa [evMap] using h2
      simpa using h3
    · right
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.2 fun φ _ => ?_
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy0'
      let P : homSpace τ ρ ⊗[ℂ] Y →ₗ[ℂ] homSpace τ ρ :=
        (TensorProduct.rid ℂ (homSpace τ ρ)).toLinearMap ∘ₗ LinearMap.lTensor (homSpace τ ρ) l
      have hP : ∀ t, P (LinearMap.rTensor Y S.toSubmodule.subtype t) ∈ S.toSubmodule := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul ψ z => simpa [P] using S.toSubmodule.smul_mem (l z) ψ.2
        | add a b ha hb =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem ha hb
      have hmem : evMap τ ρ (φ ⊗ₜ y0) ∈ U.toSubmodule := by
        rw [hU]
        exact Submodule.mem_top
      obtain ⟨t, ht⟩ := hmem
      have ht' : LinearMap.rTensor Y S.toSubmodule.subtype t = φ ⊗ₜ y0 :=
        hev (a₁ := LinearMap.rTensor Y S.toSubmodule.subtype t) (a₂ := φ ⊗ₜ y0) ht
      have := hP t
      rw [ht'] at this
      simpa [P, hl] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteHeightBreuilKisinLatticeSemistable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WHeight


open GlobalTheory.BSP.HeightEx in
theorem exists_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (b : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), IsUnit (Y.map (inclW l)) ∧ IsUnit Z ∧ (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) ∧ A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Y.map WittVector.frobenius = Y * A.map bk.ev := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (GlobalTheory.BSP.HeightEx.inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := _root_.GlobalTheory.SatLattice.exists_lattice_basis l K bk d _ hdet
  have hY'u := _root_.GlobalTheory.EtaleLattice.isUnit_saturated_basis l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := _root_.GlobalTheory.BSP.saturated_module_free l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add (f := _)]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.semistableSeed_module_lAdic_closed l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.semistable_periods_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.semistablePeriod_span_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := _root_.GlobalTheory.BSP.HeightAprime.main l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨Y, _, b, _, A', hYu, GlobalTheory.T.semistable_disc_period_basis_isUnit l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, hA', hA⟩

end GlobalTheory.BKLim.WHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GroundTheory.Global

namespace GlobalTheory.AbsTwist

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_normOne (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) (x : IdeleGroup F) (hx : x ∈ IdeleGroup.normOneSubgroup F) :
    f x = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ n : ℕ, f (x ^ n) = n * f x := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hm, ih]; push_cast; ring
  have hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C := fun n => by
    obtain ⟨k, hk'⟩ := hxD _ (pow_mem hx n)
    have := hC _ hk'
    rwa [hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f x|)
  rw [div_lt_iff₀ (abs_pos.2 h)] at hn
  exact absurd (hb n) (not_le.2 hn)

theorem module_expScalar (t : ℝ) :
    (IdeleGroup.ideleModule F (GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)) : ℝ) =
      Real.exp ((Module.finrank ℚ F : ℝ) * t) :=
  GlobalTheory.HeckeOne.ideleNorm_expScalar F t

theorem exists_eq_mul_log_module (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) :
    ∃ a : ℝ, ∀ x, f x = a * Real.log (IdeleGroup.ideleModule F x : ℝ) := by
  let e : ℝ → IdeleGroup F := fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)
  have hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t) := fun s t => by
    simp only [e]
    rw [GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]
  have hcont : Continuous fun t => f (e t) :=
    hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩
  set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht
  have h1 := map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1
  have h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x := Subtype.ext (by
    have h3 := module_expScalar (F := F) t
    rw [ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2] at h3
    exact h3)
  have h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F := by
    rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have h5 := hm (e t) ((e t)⁻¹ * x)
  rw [mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht] at h5
  rw [h5]; ring


open GlobalTheory.Mem.Chr.CharModel in
theorem exists_norm_eq_exp (ω : HChar F) :
    ∃ c : ℝ, ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ = Real.exp (c * logNorm F x) := by
  have h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨a, ha⟩ := exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖)
    ((Units.continuous_val.comp ω.2.1).norm.log h0)
    (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)])
    (fun k => by
      have : ω.1 (IdeleGroup.diagonal F k) = 1 := ω.2.2 k
      rw [this]; simp)
  obtain ⟨b, hb⟩ := exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F)
    (logNorm_principal F)
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine absChar_not_unitary (F := F) fun x => ?_
    change ‖Complex.exp (1 * logNorm F x)‖ = 1
    rw [hb]; simp
  refine ⟨a / b, fun x => ?_⟩
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]
  congr 1
  field_simp

end GlobalTheory.AbsTwist

namespace GlobalTheory.CuspRep.CG

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.CharModel GlobalTheory.HeckeGal.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_val_apply (t : ℝ) (x : Ideles E) :
    (((absPow E t).1 x : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * logNorm E x) := rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_neg_mul (t : ℝ) : absPow E (-t) * absPow E t = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change (((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1
  rw [absPow_val_apply, absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem exists_isUnitary_twist_absPow (π : CG E a) (ha : 1 ≤ a) :
    ∃ (π₀ : CG E a) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (absPow E t) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  obtain ⟨c, hc⟩ := GlobalTheory.AbsTwist.exists_norm_eq_exp ω
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  refine ⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩
  · change ‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x,
      show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    field_simp
    ring
  · rw [← twist_mul, absPow_neg_mul, twist_one]

theorem HasSat.twist {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {ν : HChar E} (hν : ν.UnrAt w) : (π.twist ν).HasSat w (B.map (· * ν.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_val_absPow (t : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re,
    Complex.ofReal_re]

theorem HasSat.twist_absPow {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    (t : ℝ) : (π.twist (absPow E t)).HasSat w (B.map (· * (absPow E t).val w)) ∧
      ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) :=
  ⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩

end GlobalTheory.CuspRep.CG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_lattice_periods_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.sst_periods) | (exact GlobalTheory.SstPer.sst_periods) | (intros; apply GlobalTheory.SstPer.sst_periods  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.JumpsOfM

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hF l _ a e _ _ ϖ LL _ hT hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN U hU i hi
  obtain ⟨x, hfix, hx, hx'⟩ := GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin hF l a e ϖ LL hl ι P T I jB Pl AI hStd hCmp hHor hEN i hi
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by rw [← hT.succ_eq]; simp⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  let τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1 :=
    (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact hU τ i (GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector l Pl LL T (ϖ.field a) hG i x hfix hx hx' τ)

end GlobalTheory.JumpsOfM
end

