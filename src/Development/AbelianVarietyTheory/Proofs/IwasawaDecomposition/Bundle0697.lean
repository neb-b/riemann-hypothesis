module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped ComplexOrder
open Formalism.L2.Indef Formalism.IndefR.Cx

noncomputable section

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData

theorem theta_eq_proj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)
    (eV : ∀ t, (Fin ((lv (fc X.zs) b).nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv b) (hDn : X.DnLev cv b) (hUp : X.UpLev cv b) (hC : X.CoordinatesInGoodPart cr cv b)
    (hV : ∀ t F, eV t F ∈ cv.v0R X.zs b t)
    (hO : ∀ t F (x : Fin ((lv (fc X.zs) b).dQ t) → K),
      cv.hR t (cr.toR X.zs b t x) (eV t F) = cv.hR t (cr.toR X.zs b t x) (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F)))
    (t : Bs.Tup) (F : Fin ((lv (fc X.zs) b).nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs b t := sub_mem (hV t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs b t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hO t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv b t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl b := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl b, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Mem.R3.IotaRd

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData Formalism.IndefR.Links.EvTie

theorem sharp_downTo' (D : D7) (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota' (D : D7) (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo']; rfl

theorem rowSideDef3_both : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  intro hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  obtain ⟨h1, h0⟩ := GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCusp D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  have hC := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok
  have hout : ∀ t y, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ t ((R.toCx3 F).jR t y)) = R.Th t (R.jX t y) :=
    fun t y => rfl
  have hb : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ), BlockHyp (A3.A.fam.R t) (A3.A.fam.lvl P ψ) A3.A.fam.v0 1 :=
    fun t P ψ => ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hrow : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) x, rowForm A3.A P ψ t ((rV0 D A3.A P ψ t) *ᵥ x) =
      (A3.A.fam.R t).S.basis.equivFun.symm ((A3.A.fam.R t).vE (A3.A.fam.lvl P ψ) *ᵥ x) := by
    intro t P ψ x
    unfold rowForm rV0
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE (hb t P ψ)]
  have k1 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t (rV0 D A3.A F.P1 F.ψ1 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s1Of R F)).ι t *ᵥ ((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv true (F.eV (R.toCx3 F).zs) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1
      (hC.levs true).2.2 (definite_coordinates_in_good_part _ true) (evTie_of_ok hOk F _).1 (evTie_of_ok hOk F _).2 t x
    have k := ((R.toCx3 F).key_row F.cr true (hC.what₂ true).1 (hC.ratMu true) t
      (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr true t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P1 F.ψ1 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  have k0 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t (rV0 D A3.A F.P0 F.ψ0 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s0Of R F)).ι t *ᵥ ((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    let eV0 : ∀ t, (Fin ((lv (F.fc (R.toCx3 F).zs) false).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t := fun t =>
      ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
        ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P0 F.ψ0)).mulVecLin
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv false eV0 hC.jIsoR (hC.levs false).1 (hC.levs false).2.1
      (hC.levs false).2.2 (definite_coordinates_in_good_part _ false) (fun t y => ⟨y, rfl⟩)
      (fun t y x => evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P0 F.ψ0) ((R.toCx3 F).zs.Z t)
        (BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)) x y) t x
    have k := ((R.toCx3 F).key_row F.cr false (hC.what₂ false).1 (hC.ratMu false) t
      (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr false t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P0 F.ψ0 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  refine ⟨⟨Y.formsA, Y.latA, ?_⟩, ⟨Y.formsAtBottomLevel, Y.latA0, ?_⟩⟩
  · intro t x
    apply Y.Ish.jE.injective
    apply Subtype.val_injective
    have e1 := h1 t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec x)
    have e2 := Z.jEE (((A3.indefDown (s1Of R F)).ι t).mulVec (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k1] at e1
    rw [sharp_iota']
    exact e1.trans e2.symm
  · intro t x
    apply Y.Iz.jE.injective
    apply Subtype.val_injective
    have e1 := h0 t ((rV0 D A3.A F.P0 F.ψ0 t).mulVec x)
    have e2 := Z.jEE0 (((A3.indefDown (s0Of R F)).ι t).mulVec (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k0] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.IotaRd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSums
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.SerCopy

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkAd_step (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host)) (i' i : Fin D.R.m) (h : i' = i) (k : ℕ) (P : PlE D.host)
    (f : Module.End D.what₂.LL (Fin (R.nW i') → D.what₂.LL))
    (hAd : ∀ α Rr, HkDat R Sb i' k P α Rr → ∀ x : Fin (R.nW i') → D.what₂.LL,
      (R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) (f x)) =
        hkNorm R i' k P • Mult.heckeOn (R.MW i' (sg0 D A3.A)) Rr ((R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) x)))
    (α : GA D (Wc D i)) (Rr : Finset (GA D (Wc D i))) (hd : HkDat R Sb i k P α Rr) (x : Fin (R.nW i') → D.what₂.LL) :
    (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e (f x))) =
      hkNorm R i k P • Mult.heckeOn (R.MW i (sg0 D A3.A)) Rr
        ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e x))) := by
  subst h
  exact hAd α Rr hd x

variable {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem heckeAt_of_scaledAt (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    (hr : ∀ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α →
      Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R → ∀ x : S.WL ((j : ℕ) + 1),
        (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (hL ((j : ℕ) + 1) k P x))) =
          ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            Mult.heckeOn (Rl.MW j (sg0 D A3.A)) R ((Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x))))
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho := GlobalTheory.ExportPin.Model.covered_of_allPlaces Rl hIs hA i P hP hsp
  have hR' : Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

theorem heckeRead_ysOf : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R cG kKs hk cf Rw low Pq hL eig θ Bs Sb v₀ ρ hρ hpin hIs hA hAd hSb i j b ν
  refine heckeRead_iff.2 fun k P hk' f => ?_
  refine heckeAt_of_scaledAt (ysOf Bs) v₀ hpin hIs hA hρ (HeckePinRead.isDeltaInv_uD hρ hpin) i j b ν
    (Bs.hs _ (Nat.le_add_left _ _) j.2) hk' ?_ ?_
  · intro α Rr hα hR x
    obtain ⟨hk1, hkr, hsp, hP⟩ := hk'
    have hd : HkDat R Sb j k P α Rr :=
      { split := hsp
        offS := fun h => hP (hSb i h)
        odd := fun h2 => hP (hρ.goodSetup_placesOverTwo_subset i h2)
        le := hkr
        elt := hα
        reps := hR }
    exact hkAd_step R Sb _ j (idxOf_succ D j) k P (hL ((j : ℕ) + 1) k P)
      (fun α' Rr' hd' x' => hAd ((j : ℕ) + 1) k P α' Rr' (Nat.le_add_left _ _) j.2 hd' x') α Rr hd x
  · have hu : Bs.cHk i b P = HeckePinRead.uD D i b P := by
      rw [Bs.cHk_del i b P hk'.2.2.2 (HeckePinRead.frobU D P) (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [← hu]
    exact Bs.hkEq i _ b (Nat.le_add_left _ _) j.2 k P f hk'.2.2.2 hk'.2.2.1 hk'.2.1

end GlobalTheory.HeightCounting.SerCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso :
    ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K)
    (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀]
    [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀)
    (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam),
    (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) →
    ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam),
    (∀ γ x, T' (ρ' γ x) =
      rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T' x)) →
    GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' :=
  @GlobalTheory.CoefMatch.wtMatch_of_coef
end

