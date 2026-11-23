module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GramXiEqOfLawsFull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.StrLeStrAddTwo
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Topology

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_zero : pairA F 0 (0 : Af F) = 0 := Prod.ext rfl rfl

theorem pairA_zero_neg (b : Af F) : pairA F 0 (-b) = -pairA F 0 b :=
  Prod.ext (neg_zero (G := Ainf F)).symm rfl

theorem algebraMap_mul_inv {a : F} (ha : a ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) a * algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ ha, map_one]

def ann (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}
  zero_mem' := fun y _ => by
    show ψ (pairA F 0 (0 ⬝ᵥ y)) = 1
    rw [zero_dotProduct, pairA_zero_zero, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb y hy => by
    show ψ (pairA F 0 ((a + b) ⬝ᵥ y)) = 1
    rw [add_dotProduct, GlobalTheory.AnnCompactStd.pairA_zero_add, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  neg_mem' := fun {a} ha y hy => by
    show ψ (pairA F 0 ((-a) ⬝ᵥ y)) = 1
    rw [neg_dotProduct, pairA_zero_neg, AddChar.map_neg_eq_inv, ha y hy, inv_one]

theorem mem_ann {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)}
    {x : κ → FiniteAdeleRing (𝓞 F) F} : x ∈ ann ψ κ L ↔ ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1 := Iff.rfl

def scaledInt (κ : Type) (a : FiniteAdeleRing (𝓞 F) F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {y | ∀ i, a * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by
    show a * 0 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_zero]; exact Subring.zero_mem _
  add_mem' := fun {u v} hu hv i => by
    show a * (u i + v i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_add]; exact Subring.add_mem _ (hu i) (hv i)
  neg_mem' := fun {u} hu i => by
    show a * (-u i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_neg]; exact Subring.neg_mem _ (hu i)

theorem isOpen_scaledInt (κ : Type) [Fintype κ] (a : FiniteAdeleRing (𝓞 F) F) :
    IsOpen (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => a * y i) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext y; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.FinSepChar

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem exists_compact_open_separating {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) : ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.AnnCompactStd.exists_mul_mem_of_forall hψ
  obtain ⟨e, he0, he⟩ := GlobalTheory.AnnCompactStd.exists_psi_fin_trivial hψ
  have hinj : ∀ a : 𝓞 F, a ≠ 0 → algebraMap (𝓞 F) F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  set cc := algebraMap (𝓞 F) F c with hcc
  set dd := algebraMap (𝓞 F) F d with hdd
  set ee := algebraMap (𝓞 F) F e with hee
  have hC := algebraMap_mul_inv (F := F) (hinj c hc0)
  have hD := algebraMap_mul_inv (F := F) (hinj d hd0)
  have hE := algebraMap_mul_inv (F := F) (hinj e he0)
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 F) F with hO

  set L := scaledInt (F := F) κ (ι cc * ι dd) with hL
  have hLo : IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
  refine ⟨ann ψ κ L, ?_, ?_, ?_, ?_⟩
  ·
    set δ := ι ee⁻¹ * (ι cc⁻¹ * ι dd⁻¹) with hδ
    have hVo : IsOpen (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
    have hVU : (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ ann ψ κ L := by
      intro x hx y hy
      have hsum : x ⬝ᵥ y = ι ee * ∑ i, (δ * x i) * ((ι cc * ι dd) * y i) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ]
        linear_combination (-(x i * y i * (ι cc * ι dd) * (ι cc⁻¹ * ι dd⁻¹))) * hE
          + (-(x i * y i * ι dd * ι dd⁻¹)) * hC + (-(x i * y i)) * hD
      rw [hsum]
      exact he _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (hy i))
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hVo.mem_nhds (scaledInt (F := F) κ δ).zero_mem) hVU)
  · exact GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ L hLo
  · intro x hx
    apply hsub
    intro i _
    have hz : ∀ s ∈ O, ψ (pairA F 0 ((ι cc⁻¹ * ι dd⁻¹ * x i) * s)) = 1 := by
      intro s hs
      have hy : (Pi.single i (ι cc⁻¹ * ι dd⁻¹ * s) : κ → FiniteAdeleRing (𝓞 F) F) ∈ L := by
        intro k
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same]
          have : ι cc * ι dd * (ι cc⁻¹ * ι dd⁻¹ * s) = s := by
            linear_combination (ι dd * ι dd⁻¹ * s) * hC + s * hD
          rw [this]; exact hs
        · rw [Pi.single_eq_of_ne hk, mul_zero]; exact Subring.zero_mem _
      have h1 := hx _ hy
      rw [dotProduct_single] at h1
      rw [show ι cc⁻¹ * ι dd⁻¹ * x i * s = x i * (ι cc⁻¹ * ι dd⁻¹ * s) by ring]
      exact h1
    have h2 := hc _ hz
    have h3 := hd _ h2
    have h4 : ι dd * (ι cc * (ι cc⁻¹ * ι dd⁻¹ * x i)) = x i := by
      linear_combination (ι dd * ι dd⁻¹ * x i) * hC + x i * hD
    rw [h4] at h3
    exact Set.mem_iInter.mp h3 i
  · intro x₀ hx₀
    rw [mem_ann] at hx₀
    push_neg at hx₀
    obtain ⟨y, hy, hne⟩ := hx₀
    exact ⟨y, fun u hu => hu y hy, hne⟩

end GlobalTheory.FinSepChar

theorem GlobalTheory.FinSepChar.finite_chars_separate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∀ N ∈ nhds (0 : κ → Af F), ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 :=
  fun _ _ _ _ hψ κ _ _ hN => GlobalTheory.FinSepChar.exists_compact_open_separating hψ κ hN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ReadingSec
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem castFrame_mem_GG {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) :
    castFrame hΨ x ∈ GG Ψ' G p0 ↔ x ∈ GG Ψ G p0 := by
  subst hΨ; rfl

variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

theorem psi_eq (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (c : C) :
    M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ := by
  rw [← ha c]; exact (M.comp_Ψ c).symm

def rdFun (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) : C → Frame M.Ψ D.R.r → ℂ :=
  fun c x => rdR (h.laws v).p ((i : ℕ) + 1) F (e c) (castFrame (psi_eq ha c) x)

theorem mem_dom_iff (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (c : C) (x : Frame M.Ψ D.R.r) :
    castFrame (psi_eq ha c) x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom ↔ x ∈ M.dom := by
  have hG : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Gm = M.Gm := by
    rw [← ha c]; exact M.comp_Gm c
  have hp : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).p0 = M.p0 := by
    rw [← ha c]; exact M.comp_basePoint c
  show castFrame (psi_eq ha c) x ∈ GG _ _ _ ↔ x ∈ GG _ _ _
  rw [hG, hp, castFrame_mem_GG]

end ReadingSec

section ReadingSec2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

set_option synthInstance.maxHeartbeats 100000 in
def rdLin (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) :
    (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] (C → M.dom → ℂ) where
  toFun F := M.res (rdFun h ha F)
  map_add' F G := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.add_apply, Submodule.coe_add, map_add (f := _)]
  map_smul' a F := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.smul_apply, Submodule.coe_smul, map_smulₛₗ, smul_eq_mul]

theorem rdLin_apply (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (c : C) (x : M.dom) :
    rdLin h ha F c x = rdFun h ha F c x.1 := rfl

end ReadingSec2

section LP
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lastPos_kappa (p : PtAt ex Csz) (i : Fin D.R.m) : (p.κ i).LastPos := by
  intro τ k hk
  rw [(p.fw.kap i τ).1 k, Formalism.IndefR.Fock.KV.sig_Wc i τ]
  have e1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ); omega
  have e2 : D.R.k + (i : ℕ) - 1 = (k : ℕ) := by omega
  have h0 := GlobalTheory.PtStringTest.aPl_last_pos i τ
  rw [e2, ← e1] at h0
  exact h0
end LP

theorem exists_ext_embedding {K LL : Type} [Field K] [NumberField K] [Field LL] [NumberField LL] [Algebra K LL]
    (σ₀ : K →+* ℂ) : ∃ σ : LL →+* ℂ, ∀ a, σ (algebraMap K LL a) = σ₀ a := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  haveI : Algebra.IsAlgebraic K LL := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  exact ⟨(IsAlgClosed.lift : LL →ₐ[K] ℂ).toRingHom, fun a => (IsAlgClosed.lift : LL →ₐ[K] ℂ).commutes a⟩

section Card
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem card_of_runModel {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {h : RunsOk (fw2 p) r} {i : Fin D.R.m} {C : Type}
    [Finite C] [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r}
    (hM : RunModel p r h i M ka) : M.Ψ.card = D.R.f := by
  obtain ⟨v, e, -⟩ := hM
  obtain ⟨k⟩ : Nonempty ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp :=
    ⟨((r.used v).full.dict ((i : ℕ) + 1) (r.used v).full.σ₀ 1).1⟩
  have h2 := Formalism.L2.Pj.DatLin.two_card (M.comp (e.symm k)).cmType
  rw [M.comp_Ψ, Formalism.L2.S.Pv.MSTypP.finrank_hostE' D] at h2
  omega

end Card

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspace
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.LiftMod

theorem kstable_of_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (U : Submodule ℂ V) (h : ∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ U, units act a b u ∈ U) : KStable act U := by
  intro X hX u hu
  have hXs : X = ∑ a, ∑ b, X a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hXs, map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun b _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hab : sameBlock a b
  · refine U.smul_mem _ (h a b ?_ u hu)
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (hab : False).elim
    · exact (hab : False).elim
    · rfl
  · rw [hX a b hab, zero_smul]; exact U.zero_mem

theorem lift_mod : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  intro p q V _ _ act hG N N' hN hN' μ v hv h1 h2
  obtain ⟨hLie, hwt, hloc⟩ := hG
  obtain ⟨U, hvU, hUfd, hUst, -⟩ := hloc {v}
  have hU : KStable act U := kstable_of_units act U hUst
  have hvU' : v ∈ U := hvU v (Finset.mem_singleton_self v)
  haveI : FiniteDimensional ℂ U := hUfd
  let W : Submodule ℂ V := N' ⊓ U
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ U)
  have sW : KStable act W := fun X hX w hw => ⟨hN' X hX w hw.1, hU X hX w hw.2⟩
  have hKL : Formalism.MainNotions.SchurIrreducible.IsKLieAct act := fun Y Z _ _ => hLie Y Z
  obtain ⟨T', hT'W, hTN, hhw⟩ := GlobalTheory.DegKeep.joint_lift (ι := Unit) (fun _ => act) (fun _ => hKL) (fun _ v => hwt v)
    (fun w w' hne => absurd (Subsingleton.elim w w') hne) W N (fun _ => sW) (fun _ => hN) (fun _ => μ) v ⟨hv, hvU'⟩
    (fun _ c => h1 c) (fun _ c d hcd => h2 c d hcd)
  exact ⟨T', hT'W.1, hhw (), hTN⟩

end GlobalTheory.HoweR.LiftMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryLiftIdempotentPart
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IntLift

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.UnitaryMove (ct blockUnit)

theorem adjugate_mem {A : Type} [CommRing A] (O : Subring A) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (i j : Fin n) : N.adjugate i j ∈ O := by
  let M : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e : N = O.subtype.mapMatrix M := rfl
  rw [e, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

theorem exists_block {A : Type} [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a) (O : Subring A) (hO : ∀ a ∈ O, c a ∈ O)
    {ε w : A} (h1 : ε * ε = ε) (h2 : ε * c ε = 0) (hε : ε ∈ O) (hw : w ∈ O) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (hd : ε * (w * N.det) = ε) :
    ∃ K K' : Matrix (Fin n) (Fin n) A, K * K' = 1 ∧ K' * K = 1 ∧ ct c K = K' ∧ (∀ i j, K i j ∈ O ∧ K' i j ∈ O) ∧
      ∀ i j, ε * K' i j = ε * N i j := by
  have hP : ∀ i j, (w • N.adjugate) i j ∈ O := fun i j => mul_mem hw (adjugate_mem O N hN i j)
  have hPQ : ε • ((w • N.adjugate) * N) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_assoc, hd]
  have hQP : ε • (N * (w • N.adjugate)) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul, mul_assoc, hd]
  generalize w • N.adjugate = P at hP hPQ hQP
  obtain ⟨a, b, d⟩ := blockUnit c hc h1 h2 P N hPQ hQP
  have hf : 1 - ε - c ε ∈ O := sub_mem (sub_mem (one_mem _) hε) (hO _ hε)
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) A) i j ∈ O := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨_, _, a, b, d, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hP i j))) (mul_mem (hO _ hε) (hO _ (hN j i)))
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hN i j))) (mul_mem (hO _ hε) (hO _ (hP j i)))
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (N i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h1 +
      (ct c P i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h2

theorem toE_injective (D : D7) : Function.Injective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective.comp (GlobalTheory.BotFormula.toAfE D).injective

theorem exists_lift : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  intro D e SS he a N hN x hx
  obtain ⟨-, hx1, hx2⟩ := hx
  have hdet : (N.map (toE D)).det = toE D N.det := (RingHom.map_det (toE D) _).symm
  have h1 := CharVal.eps_idem he
  have hxe : finQ D (x : AE D) = 1 - finQ D e + finQ D e * N.det := toE_injective D (by
    rw [CharVal.toE_finQ, hx1, hdet, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, CharVal.toE_finQ])
  have hxx : finQ D (x : AE D) * finQ D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hd : finQ D e * (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * N.det) = finQ D e := by
    rw [hxe] at hxx
    linear_combination finQ D e * hxx + (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * (1 - N.det)) * h1
  obtain ⟨K, K', a1, a2, a3, a4, a5⟩ := exists_block (Formalism.MainNotions.StandardLatticesGL3.sgA D) (GlobalTheory.NormSum.VacMove.sgA_sgA D) (OhE D)
    (fun _ h => GlobalTheory.NormSum.VacMove.sgA_mem D h) h1 (CharVal.eps_conj he) (CharVal.eps_int he) (CharVal.finQ_int hx2) N hN hd
  let u : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ⟨K, K', a1, a2⟩
  have hu : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D a := by
    change Formalism.UG.cT _ K * _ * K = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact (congrArg (· * K) a3).trans a2
  exact ⟨⟨u, hu⟩, (GlobalTheory.NormSum.mem_intG _).2 a4, a5⟩

end GlobalTheory.StdRead.IntLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFiniteOpenSubgroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilTransNbhdD

theorem exists_nhds_finite_preimage_D : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  intro D a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage D.host.F D.host.E D.sp.cm.sig a b JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0

end GlobalTheory.WeilTransNbhdD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimageStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
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
  first | exact @GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | (intros; apply GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage <;> assumption)
end

