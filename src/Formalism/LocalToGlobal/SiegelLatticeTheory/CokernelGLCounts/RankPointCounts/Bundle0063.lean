module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOfBcPMem
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def BtSit (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    ∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

variable (u u' F0 what₂)

def BtStep (P : Submodule (𝓞 D.host.E) (VS D).V → LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop) : Prop :=
  CtxP u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BtSit Zd γ Z F'₂ φ φ' Λ₂ → P Λ₂ (liftF F'₂)

def BtLift : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsLift Λ₂ F'

def BtAdm : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => AdmWit Λ₂ (gS D) (lf D F0) F' 1

def BtG : Prop := BtStep Zd u u' F0 what₂ fun _ F' => Gval (lf D F0) F' ≠ 0

def BtOK : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => FrameOK D Λ₂ F'

def BtGen : Prop := BtStep Zd u u' F0 what₂ fun Λ₂ F' => IsGeneric Λ₂ (gS D) (lf D F0) F'

variable {u u' F0 what₂}

theorem bwdTerm'_of (h1 : BtLift Zd u u' F0 what₂) (h2 : BtAdm Zd u u' F0 what₂) (h3 : BtG Zd u u' F0 what₂)
    (h4 : BtOK Zd u u' F0 what₂) (h5 : BtGen Zd u u' F0 what₂) : BwdTerm' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ hn
  have hs : BtSit Zd γ Z F'₂ φ φ' Λ₂ := ⟨hZ, hS, hΛ₂, hn⟩
  exact ⟨⟨h1 hC γ Z F'₂ φ φ' Λ₂ hs, ⟨1, h2 hC γ Z F'₂ φ φ' Λ₂ hs⟩, h3 hC γ Z F'₂ φ φ' Λ₂ hs⟩,
    h2 hC γ Z F'₂ φ φ' Λ₂ hs, h5 hC γ Z F'₂ φ φ' Λ₂ hs, h4 hC γ Z F'₂ φ φ' Λ₂ hs⟩

theorem btG_holds : BtG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨⟨w, _, w', hGw', _, hZw'⟩, hS, _, _⟩ := hs
  have h1 : Gval (lf D F0) (liftF F'₂) =
      Formalism.L2.SG.CntLocal.GZ (((Tu D u : ℕ) : D.host.E)) (((Tu D u' : ℕ) : D.host.E)) Z := by
    rw [← hS.1]; rfl
  intro hz
  apply hGw'
  calc
    _ = Formalism.L2.SG.CntLocal.GZ (((Tu D u : ℕ) : D.host.E)) (((Tu D u' : ℕ) : D.host.E)) Z :=
      (Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.Uniq.gz_atMat hZw' (Tu D u) (Tu D u')).symm
    _ = Gval (lf D F0) (liftF F'₂) := h1.symm
    _ = 0 := hz

theorem sgnP'_last (p : PlF D) : sgnP' D p (Fin.last D.R.rS) = 1 := by
  unfold sgnP'
  split
  · unfold TermLoc.sgnP; split
    · simp
    · rfl
  · simp

theorem frFac_last (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem locF'_last (p : PlF D) {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    locF' Zd p F' (Fin.last D.R.rS) = baseChange₂ D p F'.fl.z := by
  unfold locF'
  rw [sgnP'_last, frFac_last, one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem mem_of_baseChange_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ.toIsLattice x fun v => ?_
  haveI := v.isPrime
  letI := hΛ
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v (Λ := Λ) (by infer_instance) x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem btLift_holds : BtLift Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨mem_of_baseChange_mem Zd hlat fun p => ?_, rfl⟩
  have hfr := (hloc p).1.1.2.2.1
  have h1 : locF' Zd p F'₂ (Fin.last D.R.rS) ∈ lattice₂ D Zd.M p Λ₂ := hfr.1.1 (Fin.last D.R.rS)
  rwa [locF'_last] at h1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

structure RGHyp (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop where
  hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f')
  hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f')
  hsd₁ : H.IsSelfDual t₁.abelian₂
  hsd₂ : H.IsSelfDual Λ₂
  hMM₁ : MMo H t₁ ≤ t₁.abelian₂
  hMM₂ : MMo H t₂ ≤ Λ₂
  hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂
  hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂
  hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂
  hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW t₂.f ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩
  hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW t₂.f' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩
  hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f),
        φ (H.mkW t₁.f ⟨u, hu⟩) = H.mkW t₂.f ⟨u', hu'⟩
  hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW t₂.f' ⟨u', hu'⟩

theorem RGHyp.trF {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f)) (hx₂ : a + b ∈ H.perp (H.X t₂.f))
    (h : φ (H.mkW t₁.f ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ (H.mkW t₁.f ⟨u₁, hu₁p⟩) = H.mkW t₂.f ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2 u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f) := mem_perp_isotropicSpan_of_mem_framePerp H n.2
  have hsplit : H.mkW t₁.f ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f ⟨u₁, hu₁p⟩ + H.mkW t₁.f ⟨n, hn⟩ := by
    rw [← map_add (f := _)]
    rfl
  rw [hsplit, map_add (f := _), hφ, D.hC1 n, ← map_add (f := _)] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.trF' {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f'))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f'))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f')) (hx₂ : a + b ∈ H.perp (H.X t₂.f'))
    (h : φ' (H.mkW t₁.f' ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f' ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ' (H.mkW t₁.f' ⟨u₁, hu₁p⟩) = H.mkW t₂.f' ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2' u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f') := mem_perp_isotropicSpan_of_mem_framePerp' H n.2
  have hsplit : H.mkW t₁.f' ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f' ⟨u₁, hu₁p⟩ + H.mkW t₁.f' ⟨n, hn⟩ := by
    rw [← map_add (f := _)]
    rfl
  rw [hsplit, map_add (f := _), hφ, D.hC1' n, ← map_add (f := _)] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f' := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f' ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inr i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f' := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

end RG3

end Formalism.L2.SG.LsDatumA
end
end

