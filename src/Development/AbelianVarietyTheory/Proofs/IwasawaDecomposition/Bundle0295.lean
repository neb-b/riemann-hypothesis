module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankEquivariantHomsIntoIsotypicSumOfIso
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.MultIso

variable {H S0 S X : Type} [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup X] [Module ℂ X]

def precomp (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (B : Submodule ℂ X)
    (φ : S →ₗ[ℂ] S0) (hφ : ∀ g s, φ (σ g s) = σ0 g (φ s)) : homInto σ0 ρ B →ₗ[ℂ] homInto σ ρ B where
  toFun T := ⟨T.1 ∘ₗ φ, fun s => T.2.1 (φ s), fun g s => by
    show T.1 (φ (σ g s)) = ρ g (T.1 (φ s))
    rw [hφ]; exact T.2.2 g (φ s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_homInto_of_asModule (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (B : Submodule ℂ X) (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) :
    Module.rank ℂ (homInto σ ρ B) = Module.rank ℂ (homInto σ0 ρ B) := by
  let φ : S →ₗ[ℂ] S0 :=
    { toFun := fun s => σ0.asModuleEquiv (e (σ.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e (c • σ.asModuleEquiv.symm a) = c • e (σ.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.toLinearMap c _, map_smul] }
  let ψ : S0 →ₗ[ℂ] S :=
    { toFun := fun s => σ.asModuleEquiv (e.symm (σ0.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e.symm (c • σ0.asModuleEquiv.symm a) = c • e.symm (σ0.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.symm.toLinearMap c _, map_smul] }
  have hφψ : ∀ s, φ (ψ s) = s := fun s => by simp [φ, ψ]
  have hψφ : ∀ s, ψ (φ s) = s := fun s => by simp [φ, ψ]
  have φeq : ∀ g s, φ (σ g s) = σ0 g (φ s) := fun g s => by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  have ψeq : ∀ g s, ψ (σ0 g s) = σ g (ψ s) := fun g s => by
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let E : homInto σ0 ρ B ≃ₗ[ℂ] homInto σ ρ B :=
    { precomp σ0 σ ρ B φ φeq with
      invFun := precomp σ σ0 ρ B ψ ψeq
      left_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (φ (ψ s)) = T.1 s
        rw [hφψ])
      right_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (ψ (φ s)) = T.1 s
        rw [hψφ]) }
  exact E.rank_eq.symm

theorem homInto_iSup_range (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    homInto σ0 ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = homInto σ0 ρ C := by
  have hle : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤ C := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    exact hg.1 s
  ext f
  refine ⟨fun hf => ⟨fun s => hle (hf.1 s), hf.2⟩, fun hf => ⟨fun s => ?_, hf.2⟩⟩
  exact (le_iSup₂_of_le f hf le_rfl : LinearMap.range f ≤ ⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ⟨s, rfl⟩

theorem rank_homInto_iSup_range : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) →
    Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C ⟨e⟩
  rw [rank_homInto_of_asModule σ0 σ ρ _ e, homInto_iSup_range]

end GlobalTheory.MultIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankIsotypicConjTypeEqConjModel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.IsotConj

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_zero' (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) : conjMap M M' c h 0 = 0 :=
  MultilinearMap.ext fun _ => star_zero _

theorem conjMap_add (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T T' : MMap M) :
    conjMap M M' c h (T + T') = conjMap M M' c h T + conjMap M M' c h T' :=
  MultilinearMap.ext fun _ => star_add _ _

theorem conjMap_smul (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (r : ℂ) (T : MMap M) :
    conjMap M M' c h (r • T) = star r • conjMap M M' c h T := by
  refine MultilinearMap.ext fun v' => ?_
  show star (r • (T : MMap M) _) = star r • star ((T : MMap M) _)
  rw [star_smul]

theorem conjMap_actM {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (k : Formalism.AUTREP.GAf D.host.E n) (T : MMap M) :
    conjMap M M' c h (principalLevelFrame.actM P M k T) = principalLevelFrame.actM P M' k (conjMap M M' c h T) :=
  MultilinearMap.ext fun _ => funext fun _ => rfl

theorem conjMap_minf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (T : MMap M) (hT : T ∈ principalLevelFrame.Minf θ P M) : conjMap M M' c h T ∈ principalLevelFrame.Minf θ P M' := by
  unfold principalLevelFrame.Minf at hT ⊢
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ _) hT ?_ ?_ ?_
  · intro N T hT
    obtain ⟨T', hT', e1⟩ := hM _ _ T hT
    have : conjMap M M' c h T = T' := by
      refine MultilinearMap.ext fun v' => funext fun g => ?_
      rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
      rfl
    rw [this]
    exact Submodule.mem_iSup_of_mem N (mult_congr θ M' (fun k _ => by simp) hT')
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

def cjS {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x : π.S) : (principalLevelFrame.FinTyp.conjT π).S :=
  ⟨fun g => star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g), by
    show (fun g => star (star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g))) ∈ π.S
    simpa using x.2⟩

theorem cjS_add {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x y : π.S) : cjS π (x + y) = cjS π x + cjS π y :=
  Subtype.ext (funext fun _ => star_add _ _)

theorem cjS_smul {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (a : ℂ) (x : π.S) : cjS π (a • x) = star a • cjS π x :=
  Subtype.ext (funext fun _ => by simp [cjS, mul_comm])

theorem conjT_conjT {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) : principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT π) = π := by
  rcases π with ⟨S0, _, _, _, _⟩
  show Formalism.L2.NG.FinTyp.mk (principalLevelFrame.conjSub (principalLevelFrame.conjSub S0)) _ _ _ _ = _
  congr 1
  exact principalLevelFrame.conjSub_conjSub S0

theorem conjMap_isot (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (T : MMap M)
    (hT : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (principalLevelFrame.FinTyp.conjT π)) :
    conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π := by
  unfold principalLevelFrame.isotIn at hT
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
  · intro Φ T hT
    refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
    · rintro ⟨hΦ, hR⟩ T ⟨f, rfl⟩
      let Ψ : π.S →ₗ[ℂ] MMap M' :=
        { toFun := fun x => conjMap M M' c h (Φ (cjS π x))
          map_add' := fun x y => by rw [cjS_add, map_add (f := _), conjMap_add]
          map_smul' := fun a x => by simp only [RingHom.id_apply]; rw [cjS_smul, map_smul, conjMap_smul, star_star] }
      have hΨ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M') π Ψ := by
        intro k x
        show conjMap M M' c h (Φ (cjS π _)) = principalLevelFrame.actM P M' k (conjMap M M' c h (Φ (cjS π x)))
        rw [← conjMap_actM, ← hΦ k]
        rfl
      have hΨR : LinearMap.range Ψ ≤ principalLevelFrame.Minf θ P M' := by
        rintro _ ⟨x, rfl⟩
        exact conjMap_minf θ P M M' c h hM _ (hR (LinearMap.mem_range_self Φ _))
      have e : cjS π ⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩ = f :=
        Subtype.ext (funext fun _ => star_star _)
      refine Submodule.mem_iSup_of_mem Ψ (Submodule.mem_iSup_of_mem ⟨hΨ, hΨR⟩ ⟨⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩, ?_⟩)
      show conjMap M M' c h (Φ (cjS π _)) = conjMap M M' c h (Φ f)
      rw [e]
    · rw [conjMap_zero']; exact zero_mem _
    · intro T T' h1 h2
      rw [conjMap_add]; exact add_mem h1 h2
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ}
    (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) :
    Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) ≤ Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  obtain ⟨h, hM⟩ := _root_.GlobalTheory.ConjMult.conj_mult θ M M' c hc
  have key : ∀ T ∈ principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π), conjMap M M' c h T ∈ principalLevelFrame.isotL θ P M' J χ' e' π := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, conjMap_isot θ P M M' c h hM π T h3⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
  let j : principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π) →+ principalLevelFrame.isotL θ P M' J χ' e' π :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) = Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  intro D V S S' θ M M' c hc J χ χ' e e' n P π hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' P π hχ he) ?_
  have := rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e P (principalLevelFrame.FinTyp.conjT π) ?_ ?_
  · rwa [conjT_conjT] at this
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]

end GlobalTheory.IsotConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe

variable (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : RT Y u u')

set_option maxHeartbeats 4000000 in
theorem re_termIsId : Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termIsId t) :))

set_option maxHeartbeats 4000000 in
theorem re_termInS : Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termInS t) :))

set_option maxHeartbeats 4000000 in
theorem re_relevant : t.relevant ↔ (eRT Z Y u u' t).relevant := (by with_unfolding_all exact (Iff.rfl (a := t.relevant) :))

set_option maxHeartbeats 4000000 in
theorem re_FeqF : t.FeqF ↔ (eRT Z Y u u' t).FeqF := (by with_unfolding_all exact (Iff.rfl (a := t.FeqF) :))

set_option maxHeartbeats 4000000 in
theorem re_generic : t.generic ↔ (eRT Z Y u u' t).generic := (by with_unfolding_all exact (Iff.rfl (a := t.generic) :))

set_option maxHeartbeats 4000000 in
theorem re_G : t.G = (eRT Z Y u u' t).G := (by with_unfolding_all exact (Eq.refl t.G :))

set_option maxHeartbeats 4000000 in
theorem re_termBBne : ∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p := (by with_unfolding_all exact (fun p => Iff.rfl (a := Formalism.L2.SG.Saturated.termBBne t p) :))

set_option maxHeartbeats 4000000 in
theorem re_ptOf : Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.ptOf t) :))

set_option maxHeartbeats 4000000 in
theorem re_massTerm : Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.massTerm t) :))

set_option maxHeartbeats 4000000 in
theorem re_cTerm : Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t) := by
  with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t) :)

omit t in
set_option maxHeartbeats 4000000 in
theorem re_meanCount : ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := (by with_unfolding_all exact (fun w => Eq.refl (Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) :))


omit t in
set_option maxHeartbeats 4000000 in
theorem eRT_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w :=
  fun D Z X Y u u' => ⟨fun t => ⟨re_termIsId D Z X Y u u' t, re_termInS D Z X Y u u' t,
    re_relevant D Z X Y u u' t, re_FeqF D Z X Y u u' t, re_generic D Z X Y u u' t, re_G D Z X Y u u' t,
    re_termBBne D Z X Y u u' t, re_ptOf D Z X Y u u' t, re_massTerm D Z X Y u u' t,
    re_cTerm D Z X Y u u' t⟩, re_meanCount D Z X Y u u'⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotPart

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (h : GlobalTheory.Mem.R3.StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h


set_option maxHeartbeats 2000000 in
theorem isot_le_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hC i
  obtain ⟨hcore, hSF, -, hW⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hcore.lev).1
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    intro v
    have hS : R.Sb = R.Pg := hP.char.allPl
    rw [ht]
    unfold SsetF
    rw [hQ, hS]
    simp only [Finset.union_empty, Finset.mem_image]
    constructor
    · rintro ⟨PP, h1, rfl⟩
      exact ⟨PP, h1, rfl⟩
    · rintro ⟨PP, h1, h2⟩
      exact ⟨PP, h1, HeightOneSpectrum.ext h2⟩
  have hEq : SsetF R.toRealDat (Y.tupT D.what₂.mu0) = R.SF := by
    ext v
    rw [hSF v, hSF' v]
  unfold HasEig at hE
  rw [hEq] at hE
  intro y hy
  have hy' := (Y.tied.lift.isot i π y).1 hy
  rw [Y.prtWE, Y.mjRead] at hy'
  obtain ⟨U, hU, hUy⟩ := hy'
  obtain ⟨x, hx, hxU⟩ := _root_.GlobalTheory.PartTypeW.part_in_eigenpart R.toRealDat F.lv2 hH.ok.ok2 hcore R.SF hSF Y.hF Y.PY Y.PW
    (stdPsi_of_stdFrame Y.stdPsi.1) (fun j => stdPsi_of_stdFrame (Y.stdPsi.2 j)) _ _ c hE i U hU
  have h1 : U = (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hUy
  have h2 : x = Y.mj.eW i y := (hcore.models.HW i (sg0 D A3.A)).1 (hxU.trans h1)
  rw [Submodule.mem_comap, ← h2]
  rw [← hW] at hx
  exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.Wc' i c) c hC) hx

end GlobalTheory.Mem.R3.IsotPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowFinProdKroneckerAddBinomial
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernSpan

theorem kron_pow' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) (n : ℕ) : kron a b ^ n = kron (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [kron_one]
  | succ n ih => rw [pow_succ, ih, ← kron_mul, pow_succ, pow_succ]

theorem trace_kron' {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).trace = a.trace * b.trace := by
  rw [kron, ← Matrix.trace_kronecker]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm fun x => Matrix.kroneckerMap (· * ·) a b x x

theorem trace_pow_kron_add {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R)
    (L' : Matrix (Fin N) (Fin N) R) (i : ℕ) :
    ((kron L 1 + kron 1 L') ^ i).trace =
      ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  have hc : Commute (kron L (1 : Matrix (Fin N) (Fin N) R)) (kron (1 : Matrix (Fin M) (Fin M) R) L') := by
    unfold Commute SemiconjBy
    rw [← kron_mul, ← kron_mul, mul_one, one_mul, mul_one, one_mul]
  rw [hc.add_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [kron_pow', kron_pow', one_pow, one_pow, ← kron_mul, mul_one, one_mul, ← Nat.cast_comm,
    ← nsmul_eq_mul, Matrix.trace_smul, nsmul_eq_mul, trace_kron', mul_assoc]

end GlobalTheory.GoodMetric.ChernSpan
end
end

