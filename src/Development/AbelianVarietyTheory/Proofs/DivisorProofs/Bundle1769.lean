module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable (F : Type) [Field F] [NumberField F]

theorem exists_compact_open_subgroup (κ : Type) [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)}
    (hS : S ∈ 𝓝 0) : ∃ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ S := by
  classical
  have hS' : S ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) := hS
  rw [nhds_pi, Filter.mem_pi] at hS'
  obtain ⟨I, -, t, ht, hsub⟩ := hS'
  have hO : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  have hbox : ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ ⋂ i, t i) → u ∈ S :=
    fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro u hu
    refine hbox u fun i => ?_
    have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have := hNO (c * u i) hi
    rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this

def finIdem : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem finIdem_smul_eq {κ : Type} (w : κ → AF F) :
    finIdem F • w = GlobalTheory.WeilCont.adeleJoin F 0 (fun i => (w i).2) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * (w i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i)
    rw [zero_mul, Pi.zero_apply, map_zero]
  · show (1 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = (w i).2
    exact one_mul _

theorem finIdem_smul_adeleJoin {κ : Type} (x : κ → FiniteAdeleRing (𝓞 F) F) :
    finIdem F • GlobalTheory.WeilCont.adeleJoin F 0 x = GlobalTheory.WeilCont.adeleJoin F 0 x :=
  finIdem_smul_eq _

theorem adeleJoin_zero_zero {κ : Type} :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i) = 0
  rw [Pi.zero_apply, map_zero]

theorem continuous_adeleJoin_zero {κ : Type} :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.WeilCont.adeleJoin F 0 x :=
  continuous_pi fun i => (continuous_const.prodMk (continuous_apply i) :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i), x i) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.WeilTransNbhd

end

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem actAB_smul (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB) (r : AF F)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (r • X) = r • actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p X := by
  unfold actAB
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_mul_inv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ X) = X := by
  unfold actAB
  have h1 : ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1 := by
    show ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p.1)⁻¹ : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1
    exact Units.mul_inv _
  have h2 : (((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    show ((p.2 : GL β (AF F ⊗[F] E)) * ((p.2)⁻¹ : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1
    rw [Units.mul_inv, Matrix.transpose_one]
  calc _ = ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * X *
        ((((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_nhds_finite_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  intro F E _ _ _ _ _ σ a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  haveI hmt : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  haveI : ContinuousSMul (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have hcs : Continuous co.e.symm := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap
  let Ψ : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) → (κ → AF F) × (κ → AF F) :=
    fun q => co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) q.1⁻¹ (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2)))
  let Φ : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →
      (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun q => (fun i => ((Ψ q).1 i).2, fun i => ((Ψ q).2 i).2)
  have hinv : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) => q.1⁻¹ := continuous_fst.inv
  have hm1 : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).1 : GL (Fin a) (AF F ⊗[F] E)) : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp hinv))
  have hm2 : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).2 : GL (Fin b) (AF F ⊗[F] E)) : Matrix (Fin b) (Fin b) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp hinv))
  have hv : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2) :=
    hcs.comp ((continuous_adeleJoin_zero.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_adeleJoin_zero.comp (continuous_snd.comp continuous_snd)))
  have hΨ : Continuous Ψ := hce.comp ((hm1.matrix_mul hv).matrix_mul hm2.matrix_transpose)
  have hΦ : Continuous Φ :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hΨ))).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hΨ)))
  have hΦ0 : Φ (p0, (0, 0)) = (0, 0) := by
    have : Ψ (p0, (0, 0)) = 0 := by
      simp only [Ψ, adeleJoin_zero_zero]
      rw [show ((0 : κ → AF F), (0 : κ → AF F)) = 0 from rfl, map_zero]
      rw [show actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p0⁻¹ (0 : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) = 0 by
        unfold actAB; rw [Matrix.mul_zero, Matrix.zero_mul], map_zero]
    simp only [Φ, this]
    rfl
  have hopen : IsOpen (Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)))) :=
    (hL₁.prod hL₂).preimage hΦ
  have hmem : (p0, ((0 : κ → FiniteAdeleRing (𝓞 F) F), (0 : κ → FiniteAdeleRing (𝓞 F) F))) ∈
      Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F))) := by
    rw [Set.mem_preimage, hΦ0]
    exact ⟨L₁.zero_mem, L₂.zero_mem⟩
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds hmem)
  rw [← Prod.zero_eq_mk, nhds_prod_eq] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := mem_prod_iff.1 hV
  obtain ⟨L₁', hL₁'o, hL₁'c, hL₁'s⟩ := exists_compact_open_subgroup F κ hV₁
  obtain ⟨L₂', hL₂'o, -, hL₂'s⟩ := exists_compact_open_subgroup F κ hV₂
  refine ⟨N, hN, L₁', L₂', hL₁'o, hL₁'c, hL₂'o, fun p hp x hx y hy => ?_⟩
  have hin := hNV (Set.mk_mem_prod hp (hV12 (Set.mk_mem_prod (hL₁'s hx) (hL₂'s hy))))
  refine ⟨(Φ (p, (x, y))).1, hin.1, (Φ (p, (x, y))).2, hin.2, ?_⟩

  have hfin : (GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).1, GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).2) =
      Ψ (p, (x, y)) := by
    have e1 : Ψ (p, (x, y)) = finIdem F • Ψ (p, (x, y)) := by
      simp only [Ψ]
      conv_lhs => rw [← finIdem_smul_adeleJoin x, ← finIdem_smul_adeleJoin y, ← Prod.smul_mk, map_smul,
        actAB_smul, map_smul]
    rw [e1]
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, finIdem_smul_eq]
    · rw [Prod.smul_snd, finIdem_smul_eq]
  rw [hfin]
  simp only [Ψ, LinearEquiv.symm_apply_apply, actAB_mul_inv, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilTransNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.RealUniq

open GlobalTheory.RealActs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div' {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_V (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div' h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_V' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

variable {κ : Type} [Fintype κ]

theorem actsD_zero (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem acts_zero (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

def induced {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem induced_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    induced π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [induced, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

end GlobalTheory.ThK.RealUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperArithmeticGroupUnipotentUnitary
section
set_option autoImplicit false

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem tr_one_mem (M : TwoLevels E r U C) (c : C) : M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at h
  simpa using (M.comp c).Γ.inv_mem h

def upperSub (M : TwoLevels E r U C) (c : C) : Subgroup (GL (Fin r) E) where
  carrier := M.upper c
  one_mem' := ⟨1, one_smul U c, (M.tr 1 c)⁻¹, (M.comp c).Γ.inv_mem (tr_one_mem M c), by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, δ, hδ, rfl⟩
    have hc := (M.tr_conj u c δ).1 hδ
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [hv, mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * δ * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact (M.comp c).Γ.mul_mem ((M.comp c).Γ.mul_mem hγ hc) ((M.comp c).Γ.inv_mem hm)
    · group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [hu, inv_mul_cancel, one_smul] at hm
    have h1 := tr_one_mem M c
    have hε : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := (M.comp c).Γ.mul_mem ((M.comp c).Γ.inv_mem hm) h1
      simpa [mul_inv_rev, mul_assoc] using this
    have hc : (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c ∈ (M.comp c).Γ := by
      rw [M.tr_conj u c, hu]
      simpa [mul_assoc] using (M.comp c).Γ.inv_mem hγ
    refine ⟨u⁻¹, hu', (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c * (M.tr u⁻¹ c * M.tr u c)⁻¹,
      (M.comp c).Γ.mul_mem hc ((M.comp c).Γ.inv_mem hε), ?_⟩
    group

theorem prime_and_mem_of_primesOver {g : ℕ} {P : Ideal (𝓞 E)}
    (hP : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E)) : P.IsPrime ∧ (g : 𝓞 E) ∈ P := by
  obtain ⟨hp, hl⟩ := hP
  refine ⟨hp, ?_⟩
  have hg : (g : ℤ) ∈ P.under ℤ := by
    rw [← hl.over]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hg
  simpa using hg

theorem upper_subgroup (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) (g : ℕ) (hU : M.UnipotentOver g) :
    ∃ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab (M.comp c).Gm (M.comp c).L' γ) ∧
      (∀ γ ∈ Γo, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g γ) ∧
      ∀ u : U, u • c = c → M.tr u c ∈ Γo := by
  refine ⟨upperSub M c, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, δ, hδ, rfl⟩
    have hs := (M.comp c).Γ_stab δ hδ
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm, M.tr_herm]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.tr_L' u c v, hu]
      exact M.Γ_L' c δ hδ _
  · intro γ hγ P hP
    obtain ⟨hp, hg⟩ := prime_and_mem_of_primesOver hP
    exact ⟨r, fun v hv => hU c γ hγ P hp hg v hv⟩
  · intro u hu
    exact ⟨u, hu, 1, (M.comp c).Γ.one_mem, (one_mul _).symm⟩

end GlobalTheory.UpperArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
end

