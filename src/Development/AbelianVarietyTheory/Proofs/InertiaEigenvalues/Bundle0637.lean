module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricPropertiesAllOfBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TransSum

def conjMeet {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ) : Subgroup Γ :=
  K ⊓ K.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_conjMeet {Γ : Type*} [Group Γ] {K : Subgroup Γ} {γ x : Γ} :
    x ∈ conjMeet K γ ↔ x ∈ K ∧ γ⁻¹ * x * γ ∈ K := by
  simp [conjMeet, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem exists_sum_inv {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ)
    [hf : ((conjMeet K γ).subgroupOf K).FiniteIndex] :
    ∃ C : Finset Γ, C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ K, δ = k * γ) ∧
      ∀ F : Γ → ℂ, (∀ k ∈ K, ∀ g, F (g * k) = F g) → ∀ k ∈ K, ∀ g,
        ∑ δ ∈ C, F (g * k * δ) = ∑ δ ∈ C, F (g * δ) := by
  classical
  set H := (conjMeet K γ).subgroupOf K
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let r : K ⧸ H → Γ := fun q => ((Quotient.out q : K) : Γ) * γ
  have hr : Function.Injective r := by
    intro q₁ q₂ h
    have h' : (Quotient.out q₁ : K) = Quotient.out q₂ := Subtype.ext (mul_right_cancel h)
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, h']
  refine ⟨Finset.univ.image r, ?_, ?_, ?_⟩
  · exact Finset.image_nonempty.2 ⟨(QuotientGroup.mk 1 : K ⧸ H), Finset.mem_univ _⟩
  · intro δ hδ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨_, (Quotient.out q).2, rfl⟩
  · intro F hF k hk g
    rw [Finset.sum_image (fun a _ b _ h => hr h), Finset.sum_image (fun a _ b _ h => hr h)]
    let kk : K := ⟨k, hk⟩

    have key : ∀ q : K ⧸ H, F (g * k * r q) = F (g * r (kk • q)) := by
      intro q
      have hq : (QuotientGroup.mk (Quotient.out (kk • q)) : K ⧸ H) = QuotientGroup.mk (kk * Quotient.out q) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hm := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf, mem_conjMeet] at hm
      have e : g * k * r q = g * r (kk • q) * (γ⁻¹ * ((((Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) : K) : Γ)) * γ) := by
        simp only [r, Subgroup.coe_mul, Subgroup.coe_inv, kk]
        group
      rw [e, hF _ hm.2]

    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)

end GlobalTheory.TransSum

namespace GlobalTheory.TransSum

theorem heckeOn_doubleCoset_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hP γ hγ
  have topgrp := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Wc D i).gram
  haveI : CompactSpace (levW R i) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  have hU := GlobalTheory.LevelOpen.isOpen_levG (Wc D i) (R.βW i) (R.datWp i R.triv)
  have hopen : IsOpen (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) := by
    let φ : levW R i → GfC (Wc D i) := fun x =>
      ⟨γ⁻¹ * (x : GA D (Wc D i)) * γ, mul_mem (mul_mem (inv_mem hγ) (hP.1 x.2)) hγ⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) =
        φ ⁻¹' {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjMeet, Set.mem_preimage, Set.mem_setOf_eq, φ]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage hφ
  haveI : Finite (levW R i ⧸ (conjMeet (levW R i) γ).subgroupOf (levW R i)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : ((conjMeet (levW R i) γ).subgroupOf (levW R i)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨C, hne, hC, hsum⟩ := exists_sum_inv (levW R i) γ
  refine ⟨C, hne, hC, fun Tm hT => ?_⟩
  have hCf : ∀ a ∈ C, a ∈ GfC (Wc D i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := hC a ha
    exact mul_mem (hP.1 hk) hγ
  unfold RealDat.Wall at hT ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine GlobalTheory.HeckeParts.isMultMap_heckeOn hT hCf fun v k hk g => ?_
  have h1 : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := hP.2.1 k hk
  rw [h1, one_mul, heckeLin_apply, heckeLin_apply]
  exact hsum (Tm v) (fun k' hk' g' => by rw [hT.lev v k' hk' g', hP.2.1 k' hk', one_mul]) k hk g

end GlobalTheory.TransSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

theorem ratMul_ratMul {m : ℕ} {a c : ℕ} (c₁ : Matrix (Fin a) (Fin m) D.host.E) (c₂ : Matrix (Fin m) (Fin m) D.host.E)
    (u : Mx D m c) : ratMul c₁ (ratMul c₂ u) = ratMul (c₁ * c₂) u := by
  unfold ratMul
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem covolOne_integral_ratMul {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (c c' : Matrix (Fin m) (Fin m) D.host.E) (h1 : c' * c = 1)
    (h2 : c * c' = 1) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (ratMul c a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hl : ∀ a : Mx D m n, ratMul c' (ratMul c a) = a := fun a => by
    rw [ratMul_ratMul, h1, ratMul_one]
  have hr : ∀ a : Mx D m n, ratMul c (ratMul c' a) = a := fun a => by
    rw [ratMul_ratMul, h2, ratMul_one]
  have mem : ∀ (d : Matrix (Fin m) (Fin m) D.host.E) (g : GlobalTheory.MixModel.ratMx D m n),
      ratMul d (g : Mx D m n) ∈ GlobalTheory.MixModel.ratMx D m n := fun d g =>
    GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem d) g.2
  let A : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => ratMul c a
      invFun := fun a => ratMul c' a
      left_inv := hl
      right_inv := hr
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  let L : Mx D m n ≃ₜ+ Mx D m n :=
    { A with
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let e : Mx D m n ≃ᵐ Mx D m n := L.toHomeomorph.toMeasurableEquiv
  haveI := hμ.1
  have hH : (μ.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving e μ (μ.map e) := e.measurable.measurePreserving μ
  let r : GlobalTheory.MixModel.ratMx D m n ≃ GlobalTheory.MixModel.ratMx D m n :=
    { toFun := fun g => ⟨ratMul c' (g : Mx D m n), mem c' g⟩
      invFun := fun g => ⟨ratMul c (g : Mx D m n), mem c g⟩
      left_inv := fun g => Subtype.ext (hr _)
      right_inv := fun g => Subtype.ext (hl _) }
  have hcov : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) (μ.map e) (e '' 𝓕) := by
    refine ⟨hH, ?_, ?_⟩
    · refine hμ.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show ratMul c (ratMul c' (g : Mx D m n) + a) = (g : Mx D m n) + ratMul c a
      unfold ratMul
      rw [Matrix.mul_add]
      congr 1
      exact hr _
    · rw [e.map_apply, e.preimage_image]; exact hμ.2.2
  have h := GlobalTheory.MixModel.covolOne_integral_eq hμ hcov φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

theorem exists_frame_change {W : HSp D} {Y : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hC : IsLagFrame W Y C) (hC' : IsLagFrame W Y C') :
    ∃ c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E,
      C'.1 = C.1 * c ∧ C'.2 = C.2 * c ∧ c * c' = 1 ∧ c' * c = 1 := by
  have mem : ∀ {C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E},
      IsLagFrame W Y C → ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 :=
    fun h j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  let v : ∀ C, IsLagFrame W Y C → Fin W.rank → Y.1 := fun C h j => ⟨_, mem h j⟩
  have sp : ∀ C (h : IsLagFrame W Y C), ⊤ ≤ Submodule.span D.host.E (Set.range (v C h)) := by
    intro C h
    refine le_of_eq (Submodule.map_injective_of_injective Y.1.injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h
  have li : ∀ C (h : IsLagFrame W Y C), LinearIndependent D.host.E (v C h) := fun C h =>
    linearIndependent_of_top_le_span_of_card_eq_finrank (sp C h) (by rw [Fintype.card_fin, Y.2.1])
  let b := Module.Basis.mk (li C hC) (sp C hC)
  let b' := Module.Basis.mk (li C' hC') (sp C' hC')
  have hb : ∀ j, (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C.1 a j), (fun a => C.2 a j)) :=
    fun j => by simp [b, v]
  have hb' : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C'.1 a j), (fun a => C'.2 a j)) :=
    fun j => by simp [b', v]
  have key : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
      ∑ i, b.toMatrix b' i j • (b i : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) := fun j => by
    have := congrArg Subtype.val (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Module.Basis.toMatrix_apply]
    exact this.symm
  refine ⟨b.toMatrix b', b'.toMatrix b, ?_, ?_, Module.Basis.toMatrix_mul_toMatrix_flip b b', Module.Basis.toMatrix_mul_toMatrix_flip b' b⟩
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.1 a) (key j)
    simp only [hb, hb', Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.2 a) (key j)
    simp only [hb, hb', Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lagTerm_frame_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  intro D ψ V W μ 𝓕 hμ hψ f₁ f₂ h₁ h₂ Y C C' hC hC'
  obtain ⟨c, c', e1, e2, hcc, hc'c⟩ := exists_frame_change hC hC'
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  unfold lagTerm
  rw [e1, e2]
  simp only [← ratMul_ratMul]
  refine (covolOne_integral_ratMul (m := W.rank) (n := V.rank) hμ c c' hc'c hcc
    (fun u => f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) ?_).symm
  rintro _ ⟨γ, rfl⟩ a
  exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC h₁ h₂ γ a

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := _root_.GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [_root_.GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LocalRepsFin

theorem exists_isCosetRep_finIdem : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  intro D V β L v f hf α hα
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hG : ∀ g, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g → g ∈ GfC V := fun g hg =>
    GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 hg
  let S : Subgroup (GA D V) := GlobalTheory.IdemSupport.suppGroup V (algebraMap _ (Formalism.L2.Theta.AE D) ε)
  have hS : ∀ g, g ∈ S ↔ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g := fun _ => Iff.rfl
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps (GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := S)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ levG V β L ∧ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) k} =
      (levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end GlobalTheory.LocalRepsFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosetsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
  first | exact @GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | exact GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | (intros; apply GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZero
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rel_gal_of_env {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l} {d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {s : Seed bk d ρ τ} (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A)
    (hε : ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)))
    (S : Strat bk d)
    (hSε : ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f)
    (g : ↥(GK K)) :
    ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
      ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA) := by
    obtain ⟨σ, ⟨h1, h2⟩, -⟩ := En.univ (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    have hn := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q (ainfObj K) En.inl En.inl En.inr bk.ι σ
      (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    obtain ⟨Fk, hFk⟩ := hn.1
    have hr := hn.2 Fk hFk
    have hr' : ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
        ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), ht.Rel (BK.hf bk.ι X) f₁ f₂
          ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) → f₁ = bk.ι → f₂ = (ainfHom K g).comp bk.ι →
          ht.Rel (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ hr h1 h2
    have e : S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), S.ε f₁ f₂ = ε.map σ.f → f₁ = bk.ι →
          f₂ = (ainfHom K g).comp bk.ι → S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ (hSε (ainfObj K) σ) h1 h2
    have hm : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk = (ε.map σ.f).map bk.iA :=
      Matrix.ext fun i j => hFk.ext (ε i j)
    have hM : (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA = (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk :=
      (congrArg (fun M => Matrix.map M bk.iA) e).trans hm.symm
    exact Eq.mpr (congrArg (ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)) hM) hr'

theorem exists_strat_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ),
    Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  intro l _ K bk τ hτ d ρ hρ s ht

  obtain ⟨En⟩ := _root_.GlobalTheory.BSP.nonempty_env l K bk bk.prism (bk.toP bk.E) (bk.toP X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id bk.prism))

  obtain ⟨En₂⟩ := _root_.GlobalTheory.BSP.nonempty_env l K bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)
  obtain ⟨⟨tb⟩, -⟩ := _root_.GlobalTheory.BSP.envelopes_topBasis l K bk En En₂

  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_comparison_matrix_prismCoproduct l K bk d ρ τ s ht hτ hρ En
  have hφ := _root_.GlobalTheory.BSP.Height.phi_eq_of_rel_pow l K bk d ρ τ s ht hτ En.Q En.inl En.inr (Digits l) tb 0 ε
    (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    ((congrArg (fun c => c • ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀))
      (pow_zero ((l : ℕ) : Disc l (BK.hf En.inl X) bk.ρ₀))).trans (one_smul _ _)).symm
  have hc := _root_.GlobalTheory.BSP.StratCocycle.unit_cocycle l K bk d ρ τ s ht En ε hε
  obtain ⟨S, hSa, hSA, hSε⟩ := _root_.GlobalTheory.BSP.strat_of_envCocycle l K bk En d (ht.a + s.N) ht.b ht.A ht.A' ht.A_mul ε hφ hc
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule l K bk d ρ τ s ht hτ S hSa hSA (rel_gal_of_env ht En ε hε S hSε)
  exact ⟨S, T, hT⟩

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroupStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_lie_multiplicities_uniformised_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (IsLocalRing.maximalIdeal T.V) t) (F : Type) [Field F] [IsAlgClosed F] (f : T.V →+* F), Function.Injective f → ∀ (τ : 𝓞 E →+* F) (N : ℕ), LieMult t.act (spMap f) τ N → letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧ n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  first | exact @GlobalTheory.LieUnif.lieMult_unif | exact GlobalTheory.LieUnif.lieMult_unif | (intros; apply GlobalTheory.LieUnif.lieMult_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_representatives_split_place_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  first | exact @GlobalTheory.SmallerLevelHecke.isDC_smaller_level | exact GlobalTheory.SmallerLevelHecke.isDC_smaller_level | (intros; apply GlobalTheory.SmallerLevelHecke.isDC_smaller_level <;> assumption)
end

