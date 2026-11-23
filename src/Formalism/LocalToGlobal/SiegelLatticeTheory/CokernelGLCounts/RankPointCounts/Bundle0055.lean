module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nu_not_class_holds : FCount.NuNotCls M δ u u' F0 what₂ :=
  FCount.nuNotCls_of (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem local_class_holds (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) : LocClsE M δ u u' F0 what₂ :=
  locClsE_of hA hT hrows hN (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem coefProd_of_steps (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of hA (local_class_holds hA hT hrows hN) (phase_class_holds M δ)
    (phaseProd_of hrows hN (Formalism.L2.SG.Pf.phase_well_defined hM hrows) (phaseAtRep_of hPL hPP)) hV

theorem coefficient_product_of_local (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hVP : VolIdxProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of_steps hA hT hrows hN hM hPL hPP (volProd_of hA hT hrows hN (local_class_holds hA hT hrows hN) hVP)

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaRep
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem repG_holds : RepG u u' F0 what₂ := by
  intro hC γ Z hZ
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  obtain ⟨⟨hPD, hmk⟩, -⟩ := hex.choose_spec
  refine ⟨⟨hex.choose.2.1, hPD⟩, hrep.symm, hmk, ?_⟩
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hrow
  have hrel := (hEq ⟨hex.choose.2.1, hPD⟩ (Quot.out γ.cls)).1 (hmk.trans (Quot.out_eq γ.cls).symm)
  have e := Formalism.L2.SG.Pf.g_value_function _ _ _ _ _ hrel
  exact fun h0 => hG (e.symm.trans h0)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaT
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace BwdBetaCut

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E}

theorem map_inf_equiv (A B : Submodule E S.V) :
    (A ⊓ B).map (β : S.V →ₗ[E] S.V) = A.map (β : S.V →ₗ[E] S.V) ⊓ B.map (β : S.V →ₗ[E] S.V) := by
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_map_equiv]

theorem Xplus_mapL (F : LFlag S r T) : Xplus (mapL β hβ F) = (Xplus F).map (β : S.V →ₗ[E] S.V) := by
  simp only [Xplus, FlagG.Xplus]
  rw [Submodule.map_sup, ← Formalism.L2.SG.Pf.X_mapFlag β hβ, Submodule.map_span, Set.image_singleton]
  rfl

include hβ in
theorem Hp_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Hp Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Hp, Hp, Formalism.L2.SG.Pf.UUE_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ]

include hβ in
theorem Ylift_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift, Ylift, Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ, map_inf_equiv]

include hβ in
theorem Ylift'_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift' (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift' Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift', Ylift', Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ,
    map_inf_equiv]

theorem sgRel_mapL (F : LFlag S r T) (F' : LFlag S r T') (y y' : S.V) (al al' : E) :
    SgRel (mapL β hβ F) (mapL β hβ F') (β y) (β y') al al' ↔ SgRel F F' y y' al al' := by
  simp only [SgRel, Formalism.L2.SG.Pf.Xsp_mapL β hβ, Formalism.L2.SG.Pf.zt_mapL]
  constructor
  · rintro ⟨x, hx, x', hx', h⟩
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨x0', hx0', rfl⟩ := Submodule.mem_map.1 hx'
    refine ⟨x0, hx0, x0', hx0', β.injective ?_⟩
    simp only [map_sub, map_add (f := _), map_smul, LinearEquiv.coe_coe] at h ⊢
    exact h
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨β x, Submodule.mem_map_of_mem hx, β x', Submodule.mem_map_of_mem hx', ?_⟩
    rw [← map_sub, h]
    simp only [map_add (f := _), map_smul]

end Gen

end BwdBetaCut

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def IotaC₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (D.sp.Y 0) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x' ∈ Lrep Λ F', ∀ l ∈ Lrep Λ F, ∀ l₂ ∈ Lrep Λ₂ F, l - l₂ ∈ Xsp F →
    (l - x' ∈ NgX Λ (gS D) F F' ↔ l₂ - β₂ x' ∈ NgX Λ₂ (gS D) F F₂)

def W0₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (D.sp.Y 0) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ w ∈ Hp Λ F F', ∃ w₂ ∈ Hp Λ₂ F F₂, w - w₂ ∈ Xsp F ∧ β₂ w - w₂ ∈ Xsp F₂

def Scalar₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (D.sp.Y 0) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ₂ F F₂, ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' ∈ Ylift' Λ₂ F F₂,
    y1 - y2 ∈ Xsp F → y2'' - β₂ y1' ∈ Xsp F₂ →
      ∀ al al' : D.host.E, SgRel F F' y1 y1' al al' ↔ SgRel F F₂ y2 y2'' al al'

def IsPair₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (D.sp.Y 0) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  β₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap β₂ Λ = Λ₂ ∧
    (∀ j, (Xflag F' j).map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j) ∧ β₂ F'.fl.z = F₂.fl.z ∧
    IotaC₂ Λ Λ₂ F F' F₂ β₂ ∧ W0₂ Λ Λ₂ F F' F₂ β₂ ∧ Scalar₂ Λ Λ₂ F F' F₂ β₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaCore₂ : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V, IsPair₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₂

variable {u u' F0 what₂}

namespace BwdBetaCut

theorem unipotent_preserves_x {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (Xsp (lf D F0)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (lf D F0) := by
  have h := Formalism.L2.SG.Pf.Xsp_mapL n (isom_of_N0F hn) (lf D F0)
  rw [mapL_lf hn] at h
  exact h.symm

theorem unipotent_preserves_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (orth (VS D) (Xsp (lf D F0))).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp (lf D F0)) := by
  rw [← Formalism.L2.SG.Pf.orth_map_sat n (isom_of_N0F hn), unipotent_preserves_x hn]

theorem unipotent_inv_sub_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) {v : (VS D).V}
    (hv : v ∈ orth (VS D) (Xsp (lf D F0))) : v - n.symm v ∈ Xsp (lf D F0) := by
  have h1 : n.symm v ∈ orth (VS D) (Xsp (lf D F0)) := by
    rw [← unipotent_preserves_orth hn] at hv
    rw [Submodule.mem_map_equiv] at hv
    exact hv
  have h2 := hn.2.2.1 _ h1
  rwa [LinearEquiv.apply_symm_apply] at h2

theorem Hp_le_orthX (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ) {T' : D.host.E}
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (hL : IsLift Λ (lf D F0)) (hL' : IsLift Λ F') :
    Hp Λ (lf D F0) F' ≤ orth (VS D) (Xsp (lf D F0)) := by
  intro w hw
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)]
  have hw' := hw
  rw [Hp, Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hw'
  intro e he
  refine hw' e ?_
  refine (Submodule.span_le.2 ?_) he
  rintro _ ⟨a, rfl⟩
  have := PI.PairCorankPos.W.frame_mem_UUE Λ hΛ (lf D F0) F' hL hL' (Sum.inl a.castSucc)
  simpa [FlagG.fvec] using this

end BwdBetaCut

namespace BwdBetaCut

theorem map_mul_eq (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V) :
    U.map ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (U.map (b : (VS D).V →ₗ[D.host.E] (VS D).V)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [← Submodule.map_comp]; rfl

theorem orth_Xplus_le {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    orth (VS D) (Xplus F) ≤ orth (VS D) (Xsp F) := by
  intro v hv
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hv ⊢
  exact fun x hx => hv x (le_sup_left (a := Xsp F) hx)

end BwdBetaCut

theorem betaCore_of₂ (h : BetaCore₂ Zd u u' F0 what₂) : BetaCore Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG
  obtain ⟨β₂, hiso, hgm, hfl, hz, hI, hW, hSc⟩ := h hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩ hT hPD hG
  have hni := isom_of_N0F hn
  have hF : mapL n hni (lf D F0) = lf D F0 := mapL_lf hn
  have hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hfix := (hC.2.1.1 γ.lam γ.mem).2.1
  have hL₂ : IsLift Λ₂ (lf D F0) := by
    have := Formalism.L2.SG.Pf.IsLift_mapL n hni Λ₂ (lf D F0)
    rw [hF, hΛ] at this
    exact this.1 hfix.2.2.1
  have hX'' : Xsp (mapL n hni (liftF F'₂)) = (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    Formalism.L2.SG.Pf.Xsp_mapL n hni _
  refine ⟨n * β₂, ⟨⟨Subgroup.mul_mem _ hni hiso, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Formalism.L2.SG.Pf.gmap_mul_sat, hgm, hΛ]
  · intro j
    rw [Formalism.L2.SG.Pf.Xflag_mapL n hni, ← hfl j, BwdBetaCut.map_mul_eq]
  · show n (β₂ (repF γ).fl.z) = n (liftF F'₂).fl.z
    rw [hz]
  · intro x' hx' l hl
    have hN : NgX γ.lam (gS D) (lf D F0) (mapL n hni (liftF F'₂)) =
        Formalism.HermitianLatticesTheory.gmap n (NgX Λ₂ (gS D) (lf D F0) (liftF F'₂)) := by
      rw [← Formalism.L2.SG.Pf.NgX_mapL n hni, hF, hΛ]
    have hLr : Lrep γ.lam (lf D F0) = Formalism.HermitianLatticesTheory.gmap n (Lrep Λ₂ (lf D F0)) := by
      rw [← Formalism.L2.SG.Pf.Lrep_mapL n hni, hF, hΛ]
    have hl₂ : n.symm l ∈ Lrep Λ₂ (lf D F0) := by
      rw [hLr, Formalism.L2.SG.Saturated.mem_gmap_iff] at hl; exact hl
    have hlo : l ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl).2
    rw [hI x' hx' l hl (n.symm l) hl₂ (BwdBetaCut.unipotent_inv_sub_mem hn hlo), hN, Formalism.L2.SG.Saturated.mem_gmap_iff]
    simp only [map_sub]
    rw [show n.symm ((n * β₂) x') = β₂ x' from n.symm_apply_apply (β₂ x')]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW w hw
    refine Submodule.mem_map.2 ⟨(w, n w₂), ?_, rfl⟩
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs]
    have hHp : Hp γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Hp Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Hp_mapL n hni, hF, hΛ]
    have hw₂o := BwdBetaCut.Hp_le_orthX Λ₂ hΛ₂.1 (liftF F'₂) hL₂ hT.1.1 hw₂
    refine ⟨hw, ?_, ?_, ?_⟩
    · rw [hHp]; exact Submodule.mem_map_of_mem hw₂
    · have h3 := hn.2.2.1 w₂ hw₂o
      have : w - n w₂ = (w - w₂) - (n w₂ - w₂) := by abel
      show w - n w₂ ∈ Xsp (lf D F0)
      rw [this]; exact sub_mem h1 h3
    · show n (β₂ w) - n w₂ ∈ Xsp (mapL n hni (liftF F'₂))
      rw [← map_sub, hX'']
      exact Submodule.mem_map_of_mem h2
  · intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al'
    have hY : Ylift γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift_mapL n hni, hF, hΛ]
    have hY' : Ylift' γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift' Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift'_mapL n hni, hF, hΛ]
    have hy2o : y2 ∈ orth (VS D) (Xsp (lf D F0)) :=
      BwdBetaCut.orth_Xplus_le (lf D F0) (Submodule.mem_inf.1 hy2).2
    rw [hY, Submodule.mem_map_equiv] at hy2
    rw [hY', Submodule.mem_map_equiv] at hy2''
    have e1 : y1 - n.symm y2 ∈ Xsp (lf D F0) := by
      have : y1 - n.symm y2 = (y1 - y2) + (y2 - n.symm y2) := by abel
      rw [this]; exact add_mem hd1 (BwdBetaCut.unipotent_inv_sub_mem hn hy2o)
    have e2 : n.symm y2'' - β₂ y1' ∈ Xsp (liftF F'₂) := by
      have hd2' : y2'' - (n * β₂) y1' ∈ (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [← hX'']; exact hd2
      rw [Submodule.mem_map_equiv] at hd2'
      have : n.symm (y2'' - (n * β₂) y1') = n.symm y2'' - β₂ y1' := by
        rw [map_sub]; congr 1; exact n.symm_apply_apply (β₂ y1')
      rwa [this] at hd2'
    rw [hSc y1 hy1 _ hy2 y1' hy1' _ hy2'' e1 e2 al al']
    have hs := BwdBetaCut.sgRel_mapL n hni (lf D F0) (liftF F'₂) (n.symm y2) (n.symm y2'') al al'
    rw [hF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hs
    exact hs.symm

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starInU (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  ∀ b, frame F'₂ b ∈ Submodule.span D.host.E (Set.range (Sum.elim (frame (lf D F0)) (starFrame γ)))

def starOmL (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((starZh f f').adjugate (Fin.last D.R.rS) a) • f a

theorem star_frame_lead_minor (γ : TermDef.Term D u u' F0 what₂) (l : ℕ) :
    leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l = leadMinorE (ZhatL (lf D F0) (repF γ)) l := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) *
        (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h))
    (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h])
    (fun b => by simp [Matrix.of_apply, hξ2 b]) l]

theorem starG_ne (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    (starZh (frame (lf D F0)) (starFrame γ)).det * star (starZh (frame (lf D F0)) (starFrame γ)).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
          star (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS)) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    have he := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2
    change Gval (lf D F0) (repF γ) = _ at he
    rw [he]; exact hG
  rw [← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]
  exact hGv

theorem starGlob (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z)
    (hU : starInU γ F'₂) :
    ∃ (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V),
      (∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') ∧ (∀ b, g (starFrame γ b) = frame F'₂ b) ∧
      (∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k) ∧
      star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂ := by
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set Z₁ := starZh f f₁ with hZ₁
  set F₂ := F'₂.fl with hF₂
  have hfF : f = F0.fvec := rfl
  have hf₂ : frame F'₂ = F₂.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁ := rfl
  obtain ⟨hf1a, hf1b⟩ := star_frame_orthogonal γ
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f f₁ with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans hf1b.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 :=
    FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact hU b
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact hU b
  obtain ⟨g, hiso, hgu, -, hform⟩ := FsLA.isom_ext uu uu' hGr hdet hsp
  refine ⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b),
    hform, ?_⟩

  have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
    rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
    simp only [starOmL, Matrix.conjTranspose_apply]
    rw [← hZ]
    rfl
  have homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FsLA.om, starOmL, map_sum, map_smul]
    have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
    rw [e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
    exact (hgu (Sum.inl a)).symm
  have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
  have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
  rw [e1, e2, homf, homh] at hom3
  exact hom3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

