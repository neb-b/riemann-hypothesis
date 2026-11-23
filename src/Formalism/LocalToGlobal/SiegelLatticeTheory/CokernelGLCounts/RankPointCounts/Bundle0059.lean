module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIdentPf
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem ident_generic {r : ℕ} (Lam₁ Lam₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂) :
    H.Ident (⟨Lam₁, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨Lam₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.SendsTo (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).toLinearMap 1 1 (f₁ (Fin.last r)) (f₂ (Fin.last r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ?_⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem omp_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Zd.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)]
  congr 2 <;> ring

theorem betaP_fix {ι : Type} [Fintype ι] (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u y : ι → (VS D).V)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (u k) v • y k) (w : Vp D p)
    (hw : ∀ k, (locH Zd p).h w (baseChange₂ D p (u k)) = 0) : betaP p g w = w := by
  have hk : ∀ k, ∑ i, w i * (D.s.atP p).ιE ((VS D).hT (u k) ((VS D).frame i)) = 0 := by
    intro k
    have e := hw k
    conv_lhs at e => rw [vp_eq_sum p w]
    rw [h_sum_left] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermitian_base_change_smul Zd p]
    rfl
  conv_lhs => rw [vp_eq_sum p w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, betaP_bc, hform, map_add (f := _), baseChangeAt_sum, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]
  rw [← vp_eq_sum p w, Finset.sum_comm]
  simp only [← Finset.sum_smul, hk, zero_smul, Finset.sum_const_zero, add_zero]

theorem gdl_eq (f g : Fin (D.R.rS + 1) → (VS D).V) (l : ℕ) : GDl f g l = leadMinorE (starZh f g) l := by
  unfold GDl leadMinorE
  split_ifs <;> rfl

theorem xspan_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => F.fvec a.castSucc) = F.X := by
  have : (fun a : Fin D.R.rS => F.fvec a.castSucc) = F.e := funext fun a => by simp [FlagG.fvec]
  rw [this]; rfl

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def StarIdentU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) →
    ∀ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z → starCompat γ F'₂ →
      starInU γ F'₂ →
      ∀ p, ∃ φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂),
        LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ'

def StarFrameU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
      starInU γ F'₂

variable {u u' F0 what₂}

theorem starFrameU_holds : StarFrameU u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, hsp⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ⟨?_, ?_⟩, fun b => hsp b⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LprExist : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      ∃ ψ₀ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'),
        (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
          (LinearEquiv.refl _ _) ψ₀ ∧
        (locH Zd p).SendsTo ψ₀.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) ∧
        ψ₀ '' (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' =
          (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F') ∧
        ∀ g, (Zd.M p).split = some g →
          Prod.map ψ₀ (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
            (locH Zd p).iotaGraph g (tLoc Zd p γ) =
            (locH Zd p).iotaGraph g
              ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def LprNondeg : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') ∧
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (tLoc Zd p γ).f').det ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F')).det ∧
      Iso' (locH Zd p) (tLoc Zd p γ).f' ∧ Iso' (locH Zd p) (locF' Zd p F')

variable {u u' F0 what₂}


set_option maxHeartbeats 800000 in
theorem lprPart_of (hE : LprExist Zd u u' F0 what₂) (hN : LprNondeg Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p ψ hI hz
  obtain ⟨ψ₀, hI₀, hz₀, hL, hι⟩ := hE hrows γ Z hC F' hP p
  obtain ⟨n1, n2, d1, d2, k1, k2⟩ := hN hrows γ Z hC F' hP p
  have h : ψ = ψ₀ := psi_unique (H := locH Zd p) (tLoc Zd p γ)
    ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩ (LinearEquiv.refl _ _) ψ ψ₀
    n1 n2 d1 d2 k1 k2 hI hI₀ hz hz₀
  rw [h]
  exact ⟨hL, hι⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaMemO
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bridge

variable {D : D7}

def condI (y : D.host.E) : Ideal (𝓞 D.host.E) where
  carrier := {t | ∃ o : 𝓞 D.host.E, (t : D.host.E) * y = o}
  add_mem' := by
    rintro a b ⟨o₁, h₁⟩ ⟨o₂, h₂⟩
    exact ⟨o₁ + o₂, by push_cast; rw [add_mul, h₁, h₂]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨o, h⟩
    exact ⟨c * o, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩

theorem iota_mem_O (p : PlF D) (y : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → IntP P y) :
    (D.s.atP p).ιE y ∈ (D.s.atP p).O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D]
  have := p.isPrime
  by_contra hno
  push Not at hno
  have hle : (condI y).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro s hs
    by_contra hsp
    obtain ⟨o, ho⟩ := hs
    apply hno s hsp
    have e : algebraMap D.host.F D.host.E (s : D.host.F) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E,
        IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E]
    rw [e, ho]
    exact o.2
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (condI y) hle
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hQc, hb]
    change Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ⊥ = ⊥
    rw [Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
  obtain ⟨t, ht, o, hto⟩ := h ⟨Q, hQp, hQ0⟩ hQc
  exact ht (hIQ ⟨o, hto⟩)

end Bridge

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormBound
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Frac

variable (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V)
  (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
  (hiso : ∀ x ∈ X, ∀ x' ∈ X, brS (VS D) x x' = 0) (horth : ∀ x ∈ X, brS (VS D) y0 x = 0)
  (hy0 : y0 ∈ Λ) (c0 : 𝓞 D.host.E) (hc0 : (c0 : D.host.E) = brS (VS D) y0 y0) (hc0ne : c0 ≠ 0)

include hy0 in
theorem one_mem_J : (1 : D.host.E) ∈ Jsub Λ X y0 := by
  change (1 : D.host.E) • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E)
  rw [one_smul]
  exact Submodule.mem_sup_left hy0

include hun hiso horth hy0 hc0 hc0ne in
theorem isFractional_J : IsFractional (nonZeroDivisors (𝓞 D.host.E)) (Jsub Λ X y0) := by
  refine ⟨c0, mem_nonZeroDivisors_of_ne_zero hc0ne, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hb (one_mem_J Λ X y0 hy0)
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def]
  show (c : D.host.E) = (c0 : D.host.E) * b
  rw [hc, hc0]
  simp only [brS, one_smul, map_smul, smul_eq_mul]
  ring

def Jfrac : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ⟨Jsub Λ X y0, isFractional_J Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne⟩

theorem mem_Jfrac {l : D.host.E} : l ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ↔ l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := Iff.rfl

theorem Jfrac_ne_zero : Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ≠ 0 := by
  intro h
  have h1 : (1 : D.host.E) ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne :=
    (mem_Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne).2 (by rw [one_smul]; exact Submodule.mem_sup_left hy0)
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact one_ne_zero h1

theorem normZ_cO (d : 𝓞 D.host.E) :
    Algebra.norm ℤ (TorsionTotientBound.cO D.host.E d) = Algebra.norm ℤ d := by
  exact Algebra.norm_eq_of_algEquiv (TorsionTotientBound.cO D.host.E).toIntAlgEquiv d

theorem norm_bound :
    (1 : ℝ) ≤ ((FractionalIdeal.absNorm (Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne) : ℚ) : ℝ) ^ 2 *
      |((Algebra.norm ℚ (c0 : D.host.E) : ℚ) : ℝ)| := by
  classical
  have key : ∀ l ∈ Jsub Λ X y0, ∀ m ∈ Jsub Λ X y0,
      ∃ c : 𝓞 D.host.E, (c : D.host.E) = star m * l * c0 := by
    intro l hl m hm
    obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hl hm
    refine ⟨c, ?_⟩
    rw [hc, hc0]
    simp only [brS, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  set J := Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne with hJ
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (c0 : D.host.E) * J ≤ 1 := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
    obtain ⟨c, hc⟩ := key l hl 1 (one_mem_J Λ X y0 hy0)
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨c, ?_⟩
    show (c : D.host.E) = (c0 : D.host.E) * l
    rw [hc, star_one, one_mul, mul_comm]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hmemI : ∀ i : 𝓞 D.host.E, i ∈ I → ∃ l ∈ Jsub Λ X y0, (i : D.host.E) = c0 * l := by
    intro i hi
    have h1 : algebraMap (𝓞 D.host.E) D.host.E i ∈
        (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) hi
    rw [hI, FractionalIdeal.mem_singleton_mul] at h1
    obtain ⟨l, hl, h⟩ := h1
    exact ⟨l, hl, h⟩
  have hc0I : c0 ∈ I := by
    have h1 : (c0 : D.host.E) ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [hI, FractionalIdeal.mem_singleton_mul]
      exact ⟨1, one_mem_J Λ X y0 hy0, (mul_one _).symm⟩
    rw [FractionalIdeal.mem_coeIdeal] at h1
    obtain ⟨x', hx', hx'e⟩ := h1
    have hx'c : x' = c0 := IsFractionRing.injective (𝓞 D.host.E) D.host.E hx'e
    rw [← hx'c]
    exact hx'
  set e := TorsionTotientBound.cO D.host.E with he
  have hcoe : ∀ d : 𝓞 D.host.E, ((e d : 𝓞 D.host.E) : D.host.E) = star (d : D.host.E) := fun d => rfl
  have hA : Ideal.span {c0} * (I * Ideal.map e I) ≤ Ideal.span {c0 * e c0} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    refine Submodule.mul_induction_on hz (fun r hr s hs => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e s).1 hs
      obtain ⟨l, hl, hrl⟩ := hmemI r hr
      obtain ⟨m, hm, hxm⟩ := hmemI x hx
      obtain ⟨c, hc⟩ := key l hl m hm
      rw [Ideal.mem_span_singleton']
      refine ⟨c, IsFractionRing.injective (𝓞 D.host.E) D.host.E ?_⟩
      show ((c * (c0 * e c0) : 𝓞 D.host.E) : D.host.E) = ((c0 * (r * e x) : 𝓞 D.host.E) : D.host.E)
      push_cast
      show (c : D.host.E) * ((c0 : D.host.E) * star (c0 : D.host.E)) =
        (c0 : D.host.E) * ((r : D.host.E) * star (x : D.host.E))
      rw [hc, hrl, hxm, star_mul']
      ring
    · rw [mul_add]
      exact Ideal.add_mem _ ha hb
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h] at hc0I
    exact hc0ne ((Submodule.mem_bot _).1 hc0I)
  have hNIc : Ideal.absNorm (Ideal.map e I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map e I) e rfl).toEquiv.symm
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hA
  rw [map_mul, map_mul, hNIc, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, map_mul,
    normZ_cO, Int.natAbs_mul] at hdvd
  have hn0 : (Algebra.norm ℤ c0).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hc0ne
  have ha0 : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hIne
  have hna : (Algebra.norm ℤ c0).natAbs ≤ Ideal.absNorm I * Ideal.absNorm I := by
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : (Algebra.norm ℤ c0).natAbs * (Algebra.norm ℤ c0).natAbs ≤
        (Algebra.norm ℤ c0).natAbs * (Ideal.absNorm I * Ideal.absNorm I) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pos_of_ne_zero hn0)
  have hJn : ((Ideal.absNorm I : ℕ) : ℚ) = |Algebra.norm ℚ (c0 : D.host.E)| * FractionalIdeal.absNorm J := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := D.host.E), hI, map_mul, FractionalIdeal.absNorm_span_singleton]
  have hq : |Algebra.norm ℚ (c0 : D.host.E)| = (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) := by
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  set q := |Algebra.norm ℚ (c0 : D.host.E)| with hqdef
  set j := FractionalIdeal.absNorm J with hjdef
  have hqpos : 0 < q := by
    rw [hq]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hmain : (1 : ℚ) ≤ j ^ 2 * q := by
    have h3 : (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) ≤ ((Ideal.absNorm I : ℕ) : ℚ) * ((Ideal.absNorm I : ℕ) : ℚ) := by
      exact_mod_cast hna
    rw [← hq, hJn] at h3
    have h4 : q * 1 ≤ q * (j ^ 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h4 hqpos
  have hmainR : ((1 : ℚ) : ℝ) ≤ ((j ^ 2 * q : ℚ) : ℝ) := by exact_mod_cast hmain
  rw [hqdef] at hmainR
  push_cast at hmainR
  exact hmainR

end Frac

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

