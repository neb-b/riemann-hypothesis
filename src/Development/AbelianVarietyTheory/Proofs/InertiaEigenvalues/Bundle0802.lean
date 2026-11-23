module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.ActProof
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem parLev_eq_of {n : ℕ} {LL : Type} [CommRing LL] (hc : CMData D.host.F D.host.E) (J : Matrix (Fin n) (Fin n) D.host.E)
    (β : GL (Fin n) (D.host.E ⊗[D.host.F] Af D.host.F)) (L L' : LevDat D.host.E LL n) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hb : (blkOf L.r L.t : Fin n → ℕ) = blkOf L'.r L'.t) (hb2 : (blk2 L.r : Fin n → ℕ) = blk2 L'.r) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hP, hQ, hb, hb2]

theorem blkOf_eq_zero {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem twoBlockSizes_eq_zero_of_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_twoBlockSizes_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) : g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [twoBlockSizes_eq_zero_of_le h] at hik
  exact absurd hik (lt_irrefl _)

variable (Rl : RealDat3 D A3 Ks) (j : Fin D.R.m)

theorem levChi_flagL (κ : GA D (Wc D j)) : levChi (Wc D j) (Rl.βW j) (flagL (Rl.datWp j Rl.triv)) κ = 1 := by
  unfold levChi levFn
  have h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1 := rfl
  have hs : (flagL (Rl.datWp j Rl.triv)).s = 0 := rfl
  have hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅ := rfl
  rw [h1, subgroupCharExtension_one_apply, hs, hq]
  simp

theorem hasType_of_mem_wall {σ : D.what₂.LL →+* ℂ} {F : MMap (Rl.MW j σ)} (hF : F ∈ Rl.toRealDat.Wall j σ)
    (v : (Rl.MW j σ).Vec) : HasType (Wc D j) (Rl.βW j) (flag1L (Rl.datWp j Rl.triv)) (F v) := by
  have key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv),
      ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h := by
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h
    | zero => intro v κ _ h; simp only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]
    | add x y _ _ hx hy =>
      intro v κ hκ h
      rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
    | smul a x _ hx =>
      intro v κ hκ h
      rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact fun κ hκ h => key F hF v κ hκ h

theorem isLift_transfer {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (b : Bool)
    (g : G0g D.nd) (κ : GA D (Wc D j))
    (h : IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ) :
    IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g) κ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hp.frT] at h2 h3
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    apply parLev_eq_of
    · exact hp.Pg i j b
    · rfl
    · exact (blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm
    · exact (twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm
  refine ⟨h1, hpar ▸ h2, ?_⟩
  funext PP
  apply Units.ext
  ext a c
  have hPP : PP.1 ∈ (ρ.B i j b).G.Pg := (hp.Pg i j b).symm ▸ PP.2
  have hg := hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
  rw [← h3] at hg
  have hg2 : Units.val (cG.symm g PP) a c =
      Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩)
        (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c) := hg.symm
  rw [hg2]
  unfold rTup
  erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]
  rfl

theorem sg0_eq_embLL (Rl : RealDat3 D A3 Ks) : sg0 D A3.A = D.what₂.embLL := by
  ext c
  exact congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)

theorem evW_rho (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (g' : S.G) (κ : GA D (Wc D j)) (hκ : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm (S.eG g')) κ)
    (z : S.WL ((j : ℕ) + 1)) (x : GA D (Wc D j)) :
    evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ g' z) x =
      D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi g' : D.what₂.LLˣ) : D.what₂.LL) * evW YS v₀ j z (x * κ) := by
  have hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g') := by
    rw [← YS.geq j g', MulEquiv.symm_apply_apply]
  have hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ := hgeq ▸ hκ
  set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef
  have hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A) := (hW j _).2.1 ▸ LinearMap.mem_range_self _ _
  have hT := hasType_of_mem_wall Rl j hmem (v₀ j _)
  have hs := level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x
  rw [levChi_flagL, inv_one, one_mul] at hs
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _
  rw [(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]
  change sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _
  rw [hs]
  exact congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))

end GlobalTheory.SeriesTie.ActProof

namespace GlobalTheory.SeriesTie
open Formalism.IndefR.Lev Formalism.L2.DIV
open scoped TensorProduct

theorem actRead_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → ActRead (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW
  intro g κ hκ f x
  have hκ' := ActProof.isLift_transfer Rl j hp i b g κ hκ
  change (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x =
    (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)
  rw [YS.act, Pi.smul_apply, Pi.smul_apply]
  congr 1
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearEquiv.map_zero, map_zero]; rfl
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]
  | tmul a f0 =>
    have hg : S.eG (S.eG.symm g) = g := S.eG.apply_symm_apply g
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 := ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    change ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _
    rw [h2]
    erw [map_mul, map_inv₀, he]
    field_simp

end GlobalTheory.SeriesTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonics
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.RaiseGen

open MvPolynomial GlobalTheory.FockIsotypic

theorem exists_ker_add_range {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E)
    (h : ∀ x, A (A x) = 0 → A x = 0) (x : E) : ∃ x₀ y, A x₀ = 0 ∧ x = x₀ + A y := by
  have hd : Disjoint (LinearMap.ker A) (LinearMap.range A) := by
    rw [Submodule.disjoint_def]
    rintro _ hz ⟨y, rfl⟩
    exact h y hz
  have ht : LinearMap.ker A ⊔ LinearMap.range A = ⊤ :=
    Submodule.eq_top_of_disjoint _ _ (by have := LinearMap.finrank_range_add_finrank_ker A; omega) hd
  obtain ⟨x₀, h0, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (ht ▸ Submodule.mem_top (x := x))
  exact ⟨x₀, y, h0, e.symm⟩

theorem mem_of_filtration {V W K ι : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Fintype ι] (act : K → V →ₗ[ℂ] V) (ρ : K → W →ₗ[ℂ] W) (R L : ι → V →ₗ[ℂ] V)
    (S : ℕ → Submodule ℂ V) [∀ d, FiniteDimensional ℂ (S d)]
    (hR : ∀ i k x, act k (R i x) = R i (act k x)) (hL : ∀ i k x, act k (L i x) = L i (act k x))
    (hL0 : ∀ i, ∀ x ∈ S 0, L i x = 0) (hLs : ∀ i d, ∀ x ∈ S (d + 1), L i x ∈ S d)
    (hRL : ∀ i d, ∀ x ∈ S d, R i (L i x) ∈ S d)
    (hker : ∀ x, ∑ i, R i (L i x) = 0 → ∀ i, L i x = 0)
    (hAA : ∀ x, (∀ j, L j (∑ i, R i (L i x)) = 0) → ∑ i, R i (L i x) = 0)
    (N : Submodule ℂ (W →ₗ[ℂ] V))
    (hN0 : ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w i, L i (φ w) = 0) → φ ∈ N)
    (hNR : ∀ ψ ∈ N, ∀ i, R i ∘ₗ ψ ∈ N) (d : ℕ) :
    ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w, φ w ∈ S d) → φ ∈ N := by
  induction d with
  | zero => exact fun φ hφ hS => hN0 φ hφ fun w i => hL0 i _ (hS w)
  | succ d ih =>
    intro φ hφ hS
    let E : Submodule ℂ (W →ₗ[ℂ] V) :=
      { carrier := {ψ | (∀ k w, ψ (ρ k w) = act k (ψ w)) ∧ ∀ w, ψ w ∈ S (d + 1)}
        add_mem' := fun {a b} ha hb => ⟨fun k w => by simp [ha.1, hb.1], fun w => add_mem (ha.2 w) (hb.2 w)⟩
        zero_mem' := ⟨fun k w => by simp, fun w => zero_mem _⟩
        smul_mem' := fun c a ha => ⟨fun k w => by simp [ha.1], fun w => Submodule.smul_mem _ c (ha.2 w)⟩ }
    haveI : FiniteDimensional ℂ E := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (LinearMap.compRight (M := W) ℂ (S (d + 1)).subtype)) ?_
      intro ψ hψ
      exact ⟨ψ.codRestrict _ hψ.2, rfl⟩
    let A : V →ₗ[ℂ] V := ∑ i, R i ∘ₗ L i
    have hA : ∀ x, A x = ∑ i, R i (L i x) := fun x => by simp [A, LinearMap.sum_apply]
    have hE : ∀ ψ ∈ E, LinearMap.compRight (M := W) ℂ A ψ ∈ E := fun ψ hψ =>
      ⟨fun k w => by
        change A (ψ (ρ k w)) = act k (A (ψ w))
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hA, hψ.1, map_sum, hR, hL], fun w => by
        change A (ψ w) ∈ _
        rw [hA]
        exact Submodule.sum_mem _ fun i _ => hRL i _ _ (hψ.2 w)⟩
    obtain ⟨φ₀, ψ, h0, e⟩ := exists_ker_add_range ((LinearMap.compRight (M := W) ℂ A).restrict hE) (fun ψ h => by
      refine Subtype.ext (LinearMap.ext fun w => ?_)
      have h1 : A (A (ψ.1 w)) = 0 := LinearMap.congr_fun (congrArg Subtype.val h) w
      change A (ψ.1 w) = 0
      rw [hA] at h1
      have h2 := hker _ h1
      rw [hA] at h2 ⊢
      exact hAA _ h2) ⟨φ, hφ, hS⟩
    have e' : φ = φ₀.1 + ∑ i, R i ∘ₗ (L i ∘ₗ ψ.1) := by
      refine LinearMap.ext fun w => ?_
      have h1 : φ w = φ₀.1 w + A (ψ.1 w) := LinearMap.congr_fun (congrArg Subtype.val e) w
      rw [h1, hA]
      simp [LinearMap.sum_apply]
    rw [e']
    refine add_mem (hN0 _ φ₀.2.1 fun w => hker _ ?_) (Submodule.sum_mem _ fun i _ => hNR _ (ih _ ?_ ?_) i)
    · rw [← hA]
      exact LinearMap.congr_fun (congrArg Subtype.val h0) w
    · intro k w
      simp only [LinearMap.comp_apply, ψ.2.1, hL]
    · exact fun w => hLs i d _ (ψ.2.2 w)

section Fischer

variable {σ : Type} [Fintype σ]

theorem fis_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) : fis (X v * P) Q = fis P (pderiv v Q) := by
  classical
  unfold fis
  rw [mul_comm, map_mul, rename_X, ReciprocityTheory.PGsh.fischer_mul_X, pderiv_rename (flat σ).injective]

theorem fis_sum_left {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fis (∑ i ∈ s, f i) Q = ∑ i ∈ s, fis (f i) Q := by
  unfold fis
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_left]

theorem fis_sum_right {α : Type} (s : Finset α) (P : MvPolynomial σ ℂ) (f : α → MvPolynomial σ ℂ) :
    fis P (∑ i ∈ s, f i) = ∑ i ∈ s, fis P (f i) := by
  unfold fis
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_right]

theorem fis_zero_left (Q : MvPolynomial σ ℂ) : fis 0 Q = 0 := by
  simpa using fis_smul_left 0 0 Q

theorem fis_zero_right (P : MvPolynomial σ ℂ) : fis P 0 = 0 := by
  simpa using fis_smul_right 0 P 0

theorem fis_neg_right (P Q : MvPolynomial σ ℂ) : fis P (-Q) = -fis P Q := by
  simpa using fis_smul_right (-1) P Q

theorem eq_zero_of_fis_re (P : MvPolynomial σ ℂ) (h : (fis P P).re = 0) : P = 0 := by
  by_contra hP
  exact fis_self_ne_zero hP (Complex.ext h (Complex.conj_eq_iff_im.1 (fis_conj P P)))

variable {ι : Type} [Fintype ι] (R L : ι → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
  (hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q))

include hadj

theorem lower_eq_zero (P : MvPolynomial σ ℂ) (h : ∑ i, R i (L i P) = 0) (i : ι) : L i P = 0 := by
  have h1 : fis (∑ i, R i (L i P)) P = 0 := by rw [h, fis_zero_left]
  rw [fis_sum_left] at h1
  simp only [hadj, Finset.sum_neg_distrib, neg_eq_zero] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, Complex.zero_re,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => fis_self_re_nonneg _] at h2
  exact eq_zero_of_fis_re _ (h2 i (Finset.mem_univ i))

theorem sum_eq_zero_of_lower (P : MvPolynomial σ ℂ) (h : ∀ j, L j (∑ i, R i (L i P)) = 0) :
    ∑ i, R i (L i P) = 0 := by
  refine eq_zero_of_fis_re _ ?_
  rw [fis_sum_left]
  simp only [hadj, h, fis_zero_right, neg_zero, Finset.sum_const_zero, Complex.zero_re]

end Fischer

theorem fockT_raise {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = ∑ j : Fin n, X (τ, i, j) * (X (τ, l, j) * P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((l : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((i : ℕ) < p τ) = true := decide_eq_true hi
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem raise_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k + 2 := by
  rw [fockT_raise τ p i l hi hl]
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
  have := totalDegree_mul (X (τ, l, j) : PolF D m n) P
  rw [totalDegree_X] at this ⊢
  omega

theorem mem_of_raise : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  intro D n m w BS K _ r _ W _ _ _ ρ N hN0 hNR φ hφ
  classical
  let ι : Type := {t : D.what₂.Tau × Fin m × Fin m // (t.2.1 : ℕ) < w.p t.1 ∧ w.p t.1 ≤ (t.2.2 : ℕ)}
  let T : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ → PolF D m n →ₗ[ℂ] PolF D m n := fun τ Y =>
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Y
  let R : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.1 t.1.2.2 1)
  let L : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.2 t.1.2.1 1)
  have hT : ∀ τ Y k x, GlobalTheory.ExportSeries.fockGL m w BS (r k) (T τ Y x) =
      T τ Y (GlobalTheory.ExportSeries.fockGL m w BS (r k) x) := fun τ Y k x => by
    rw [GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
    exact congrArg _ (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ Y x)
  have hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q) := fun t P Q => by
    simp only [R, L, T]
    rw [fockT_raise _ _ _ _ t.2.1 t.2.2, GlobalTheory.LowerHarm.fockT_lower _ _ _ _ t.2.2 t.2.1, fis_neg_right, neg_neg,
      fis_sum_left, fis_sum_right]
    exact Finset.sum_congr rfl fun j _ => by rw [fis_X_mul, fis_X_mul]
  have hdeg : ∃ d, ∀ w', (φ w').totalDegree ≤ d := by
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (φ (b j)).totalDegree, fun w' => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w', map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (φ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨d, hd⟩ := hdeg
  refine mem_of_filtration (fun k => GlobalTheory.ExportSeries.fockGL m w BS (r k)) (fun k => ρ k) R L
    (fun d => restrictTotalDegree (FVar D m n) ℂ d) (fun t => hT _ _) (fun t => hT _ _) ?_ ?_ ?_
    (lower_eq_zero R L hadj) (sum_eq_zero_of_lower R L hadj) N ?_ ?_ d φ hφ
    fun w' => (mem_restrictTotalDegree _ _ _).2 (hd w')
  · intro t x hx
    rw [mem_restrictTotalDegree] at hx
    exact GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    exact GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : L t x = 0 := GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
      simp [this]
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact raise_deg _ _ _ _ t.2.1 t.2.2 _ k (GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k hx)
  · exact fun ψ hψ h => hN0 ψ hψ fun w' τ i l hi hl => h w' ⟨(τ, l, i), hl, hi⟩
  · exact fun ψ hψ t => hNR ψ hψ _ _ _ t.2.1 t.2.2

end GlobalTheory.RaiseGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitOffS0

theorem main : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  intro D N X ρ hρ i Q hQ P hsplit hP
  have hinv : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := fun z => Formalism.L2.Host.conj_conj (D := D) D.host z
  let c : 𝓞 D.host.E → 𝓞 D.host.E := fun x => RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := fun x => rfl
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      (x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ↔ y ∈ P.asIdeal) :=
    fun x y h => GlobalTheory.Mem.Col2.HAt.mem_conjIdeal_Pv P.asIdeal x y h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hy⟩ := hsplit
    intro heq
    have h1 : c x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal :=
      (key (c x) x (by rw [hc, hinv])).2 hx
    exact hy (c x) (hc x) (heq ▸ h1)
  · intro hPQ
    exact hP (hQ P (by simpa using hPQ))
  · intro Q' hQ' heq
    apply hP
    refine hρ.goodSetup_badPlaces_conj i Q' (hQ Q' (by simpa using hQ')) P ?_
    intro x y hxy
    rw [heq]
    exact key x y hxy

end GlobalTheory.SplitOffS0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMove
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem thetaKO_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP z hz e e₂ M O f f' a _ hf' hom BW Q s g
  have hw := hP.1.weil
  have hf₀ : IsThetaFunO ψ V W f₀ := hP.2.2.2.2.2.2.2.2.2.theta
  have hth : IsThetaFunO ψ V W f' := by
    clear hom
    induction hf' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, -, rfl⟩ := hx
      exact GlobalTheory.TwistFactorCompare.isTheta_heisO hw.std hf₀ y
    | zero => simpa using GlobalTheory.OrientedHeis.theta_smul (0 : ℂ) hf₀
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul (c : ℂ) hx
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hw hP.1.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) sW sW BW BW z 1
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f' hth Q).2
  have hp : ((s * z, g) : GA D V × GA D W) = (s, g) * (z, 1) := by simp
  unfold thetaKO stdF
  rw [hp, map_mul, Module.End.mul_apply, h1, hom, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.LevelSeries

end
end

