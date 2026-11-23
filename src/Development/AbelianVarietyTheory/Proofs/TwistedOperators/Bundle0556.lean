module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

open GlobalTheory.SmallDat

theorem heisS_box_gen {t : T} {i j : ℕ} {e : Num G i j} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : IsLatVac (heisO ψ _ _) (latA G t i j) f₁) (h₂ : IsLatVac (heisO ψ _ _) (latB G i j) f₂) {v : Pl D.host.F}
    {γ : PtS G i j} (hγ : γ ∈ genPtS t e v) : heisS Γ ψ γ (boxS t e f₁ f₂) = boxS t e f₁ f₂ := by
  unfold IsLatVac at h₁ h₂
  rw [heisS_box t e Γ hW₁ hWW ψ γ f₁ f₂]
  rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγl, ε, hε, hxA, hxB⟩
  · have hdA : mapA t e (2 • γ') = 2 • mapA t e γ' := by rw [two_nsmul, two_nsmul, mapA_add]
    have hdB : mapB e (2 • γ') = 2 • mapB e γ' := by rw [two_nsmul, two_nsmul, mapB_add]
    rw [hdA, hdB, h₁.1 _ hγ'.2.1, h₂.1 _ hγ'.2.2]
  · rw [h₁.2 ε hε _ hγl.2.1 hxA, h₂.2 ε hε _ hγl.2.2 hxB]

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W} {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}

theorem exists_vacS (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om')
    (hti : GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X) {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : W.IsVac (.mu t i j) f₁) (h₂ : W.IsVac (.chi i j) f₂) :
    ∃ f, thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e f₁ f₂ := by
  have hψ : Bs.ψ = W.ψ := h.ψ
  have hGood : Γ.M'.IsGood W.ψ := hψ ▸ hT.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := hψ ▸ hT.base.std
  obtain ⟨-, hvac₁⟩ := h₁
  obtain ⟨-, hvac₂⟩ := h₂
  have hbox := GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨Φ, hΦ, hΦθ⟩ := hbox.2.2 f₁ f₂ hvac₁.theta hvac₂.theta
  have hfix : ∀ v, ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ := by
    intro v γ hγ
    refine hbox.2.1 _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_
    rw [thetaS_rho, hΦθ, heisS_box_gen h.JW₁ h.JWW hvac₁.lat hvac₂.lat hγ]
  have hsd := GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW
  have hlat := GlobalTheory.SmallDat.latPtS_le_latAtV t i j e Bs Γ X hti
  obtain ⟨f, hf⟩ := GlobalTheory.PureGlue.eq_pure_of_slices Γ.M'.vac (fun v => (hGood.vac v).2.1) hGood.std Φ hΦ (by
    intro v y hy
    rcases isEmpty_or_nonempty (IxS G i j) with hκ | ⟨⟨k₀⟩⟩
    · refine ⟨(fun ξ : IxS G i j → _ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k))) default / Γ.M'.vac v default, fun ξ => ?_⟩
      have hξ : ξ = default := Subsingleton.elim _ _
      subst hξ
      have hv0 : Γ.M'.vac v default ≠ 0 := by
        intro h0
        apply (hGood.vac v).2.1
        funext ξ'
        rw [Subsingleton.elim ξ' default]
        exact h0
      rw [div_mul_cancel₀ _ hv0]
    obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V' Γ.W v Γ.M'.co hT.geo.hV'.lat.toIsLattice hT.geo.hW.lat.toIsLattice
    have hsdl := GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ (latPtS t e v) (fun γ hγ => hγ.1) ((hsd v).2)
    have hcont : Continuous (GlobalTheory.LatVac.psiAt W.ψ v) := by
      show Continuous (fun x => W.ψ (GlobalTheory.LatVac.liftV v x))
      exact hstd.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))
    have hne1 : GlobalTheory.LatVac.psiAt W.ψ v ≠ 1 := by
      intro h1
      obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := D.host.F) v
      have hx : ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F) ∉ v.adicCompletionIntegers D.host.F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
        first
        | decide
        | simp
        | (intro hle; have := (inv_le_one₀ (by simp)).1 hle; simp at this)
      have hall := (hsdl ((fun _ => c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)), 0)).2
        (fun l _ => by rw [h1, AddChar.one_apply])
      obtain ⟨γ, hγ, hγe⟩ := AddSubgroup.mem_map.1 hall
      have h2 := (hcb γ (hlat v γ hγ) k₀).1
      rw [hγe] at h2
      have h3 : c * (c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)) ∈ v.adicCompletionIntegers D.host.F := h2
      rw [mul_inv_cancel_left₀ hc0] at h3
      exact hx h3
    obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) hcont hne1
      (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v) ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c
      ((AddSubgroup.map_mono ((hsd v).1)).trans (AddMonoidHom.map_closure _ _).le) hc0 hsdl
      (by
        intro l hl k
        obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hl
        exact hcb γ (hlat v γ hγ) k)
      (Γ.M'.vac v) (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_eq_of_acts Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hGood.vac v).1
          (GlobalTheory.SmallDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v (hlat v) γ hγ))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_slice Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hfix v γ hγ) hy)
      (hGood.vac v).2.1
    exact ⟨a, fun ξ => by simpa using congrFun ha ξ⟩)
  exact ⟨f, by rw [← hf, hΦθ]⟩

end GlobalTheory.SmallVac

namespace GlobalTheory.SmallVac

open GlobalTheory.SmallDat GlobalTheory.FlipMatch

theorem vac_datumB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M hst e Bs Γ X om om' h hT hti
  have h₁ : W.IsVac (.mu t i j) (ρ.vT i j) := ρ.vT_is t i j i.2.le j.2
  have h₂ : W.IsVac (.chi i j) (ρ.vX i j) := ρ.vX_is i j i.2 j.2.le
  obtain ⟨f, hf⟩ := exists_vacS hL h hT hti h₁ h₂
  have hGood : Γ.M'.IsGood Bs.ψ := hT.geo.hM'
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨x₁, hx₁⟩ : ∃ x : HomA G t i j, ρ.vT i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₁ (funext hc)
    obtain ⟨x₂, hx₂⟩ : ∃ x : HomB G i j, ρ.vX i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₂ (funext hc)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have hu := congrFun hf (ofMaps t e (x₁, x₂))
    rw [h0, thetaS_smul, zero_mul] at hu
    unfold boxS at hu
    rw [mapA_ofMaps, mapB_ofMaps] at hu
    exact mul_ne_zero hx₁ hx₂ hu.symm
  · exact GlobalTheory.SmallGauss.isGauss W M t i j e Bs Γ X om om' h hT _ _ h₁ h₂ 1 f (by rw [one_smul]; exact hf)
  · exact GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hGood.vac v).1) hGood.std
  · intro u
    erw [Finsupp.sum_single_index, one_mul]
    · exact congrFun hf u
    · exact zero_mul _

end GlobalTheory.SmallVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ConjLineSplit

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (conjU continuous_conjU)
open GlobalTheory.ConjUTransport (conjUInv conjEquiv continuous_conjUInv)

theorem exists_lie_eq_exp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous M)
    (h0 : M 0 = 1) (hm : ∀ s t, M (s + t) = M s * M t) (hU : ∀ t, (M t)ᴴ * H * M t = H) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * H + H * Y = 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • Y) = M t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨Y, hY⟩ := GlobalTheory.banach_oneParamGroup_eq_exp M hc h0 hm
  refine ⟨Y, ?_, hY⟩
  have hd : HasDerivAt M Y 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul, funext hY] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by rw [Matrix.conjTranspose_smul]; simp }
  have hT : HasDerivAt (fun t => (M t)ᴴ) Yᴴ 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const H).fun_mul hd
  rw [funext hU] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) H)
  rwa [h0, Matrix.conjTranspose_one, mul_one, one_mul] at huniq

variable {D : D7}

theorem finTens_eq_zero {z : AE D} (h : ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 → u • z = 0) :
    GlobalTheory.LFun.finTens D.host.F D.host.E z = 0 := by
  let e : AF D.host.F := ((0, 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
  have he : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F e = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := congrArg (GlobalTheory.LFun.finTens D.host.F D.host.E) (h e he)
  rw [Algebra.smul_def, map_mul, map_zero] at h1
  have h2 : GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) e) = 1 := rfl
  rwa [h2, one_mul] at h1

theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig) u z

theorem smul_cA_sub (u : AF D.host.F) {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) (i j : Fin n) :
    (u • (A.map (cA D) - 1)) i j = cA D ((u • (A - 1)) i j) := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, cA_smul, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem conjU_mem_UAt_iff (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram) (g : GA D W) :
    conjU W 1 hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) ↔ g ∈ GinfC W := by
  have hone : ∀ a b : Fin W.rank, GlobalTheory.LFun.finTens D.host.F D.host.E ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) a b) =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    show finHom W g = 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : GlobalTheory.LFun.finTens D.host.F D.host.E ((Formalism.L2.Theta.mt W g - 1) a b) = 0 := by
      refine finTens_eq_zero fun u hu => ?_
      have h2 : (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0 := congrFun (congrFun (h u hu) a) b
      rw [smul_cA_sub] at h2
      have h3 := congrArg (cA D) h2
      rw [Formalism.L2.Theta.cA_cA, map_zero] at h3
      exact h3
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero] at h1
    exact h1
  · intro hg u hu
    have hf : finHom W g = 1 := hg
    refine Matrix.ext fun a b => ?_
    show (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0
    rw [smul_cA_sub, Matrix.smul_apply, GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu, map_zero]
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero]
    exact congrArg (fun k : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf

theorem ext_of_infMat {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g h : GA D W} (hg : g ∈ GinfC W) (hh : h ∈ GinfC W)
    (e : ∀ τ, infMat D.sp.cm.sig W.gram (θ τ) g = infMat D.sp.cm.sig W.gram (θ τ) h) : g = h := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have a : (finHom W g).1 = (finHom W h).1 := by
    rw [show finHom W g = 1 from hg, show finHom W h = 1 from hh]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)))
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun a i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (e τ) i) j


open Classical in
theorem infMat_prod {θ : InfFam D} (W : HSp D) (m : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : D.what₂.Tau → GA D W) (hx : ∀ τ, IsAtTau θ W τ (m τ) (x τ)) (τ : D.what₂.Tau) (l : List D.what₂.Tau)
    (hl : l.Nodup) : infMat D.sp.cm.sig W.gram (θ τ) (l.map x).prod = if τ ∈ l then m τ else 1 := by
  induction l with
  | nil => simpa using GlobalTheory.PointAtPlaceHom.infMat_one W (θ τ)
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, ih hl.2]
    by_cases c : τ = a
    · subst c
      rw [(hx τ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hx a).2.2 τ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem exists_eq_prod_oneP {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (g : ℝ → GA D W) (hc : Continuous g)
    (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (hg : ∀ t, g t ∈ GinfC W) :
    ∃ Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, Y τ ∈ lieAt W τ) ∧
      ∀ t, g t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => oneP θ W τ (Y τ) t).prod := by
  have h1 : Continuous (matHom W) := continuous_subtype_val
  choose Y hY hexp using fun τ => exists_lie_eq_exp (gramAt D W τ) (fun t => infMat D.sp.cm.sig W.gram (θ τ) (g t))
    (continuous_matrix fun i j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp
      ((Units.continuous_val.comp (h1.comp hc)).matrix_elem i j))
    (by rw [h0, GlobalTheory.PointAtPlaceHom.infMat_one]) (fun s t => by rw [hm, GlobalTheory.PointAtPlaceHom.infMat_mul])
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W (g t) τ)
  refine ⟨Y, hY, fun t => ext_of_infMat hθ W (hg t) ?_ fun τ => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ _
  · rw [infMat_prod W _ _ (fun τ' => GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hY τ') t) τ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ τ)), hexp]

theorem line_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  intro D θ hθ W Wd hJ γ hγ
  let φ := conjEquiv W 1 one_ne_zero hJ
  obtain ⟨Y, hY, hprod⟩ := exists_eq_prod_oneP hθ W (fun t => φ.symm (γ (Multiplicative.ofAdd t)))
    ((continuous_conjUInv W 1 one_ne_zero hJ).comp (hγ.1.comp continuous_ofAdd))
    (by rw [ofAdd_zero, map_one, map_one]) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    (fun t => (conjU_mem_UAt_iff W Wd hJ _).1 (by
      have e : conjU W 1 hJ (φ.symm (γ (Multiplicative.ofAdd t))) = γ (Multiplicative.ofAdd t) := φ.apply_symm_apply _
      rw [e]
      exact hγ.2 _))
  let p : D.what₂.Tau → (Multiplicative ℝ →* GA D W) := fun τ =>
    { toFun := fun t => oneP θ W τ (Y τ) (Multiplicative.toAdd t)
      map_one' := GlobalTheory.Mem.Lift.oneP_zero hθ
      map_mul' := fun s t => GlobalTheory.Mem.Lift.oneP_add hθ (hY τ) _ _ }
  refine ⟨Y, fun τ => φ.toMonoidHom.comp (p τ), hY, fun τ => ⟨?_, fun t => ?_⟩, fun τ t => rfl, fun t => ?_⟩
  · exact (continuous_conjU W 1 hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ (hY τ)).comp continuous_toAdd)
  · exact (conjU_mem_UAt_iff W Wd hJ _).2 (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)
  · have e := congrArg φ (hprod (Multiplicative.toAdd t))
    rw [φ.apply_symm_apply, map_list_prod, List.map_map] at e
    exact e

end GlobalTheory.ConjLineSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WeilConv

theorem weilConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.SquareSt.WeilConvergence := by
  intro D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨N, C, hC⟩ := _root_.GlobalTheory.SiegelThetaBound.theta_le_torus_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : ∀ h, Continuous fun g => thetaKO ω g h Φ := fun h =>
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ h, ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := _root_.GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top D.host.F M.rank r X.rank hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ h, ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := fun h => by
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov (hcont h).enorm.measurable
            (fun γ hγ g => by rw [hinv h γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N *
            ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) := by
          refine hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
          have ht0 : ∀ i, 0 < t i := ht.1
          have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
            Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ((hC h q hq t ht a ha k hk).trans ?_)
          have hH : 0 ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
          gcongr
          exact le_max_left _ _
      _ = C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := by
          rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
  refine ⟨N, (C₁ : ℝ) * max C 0 * I.toReal, fun h => ⟨⟨(hcont h).aestronglyMeasurable, ?_⟩, ?_⟩⟩
  · exact (key h).trans_lt (by finiteness)
  · rw [integral_norm_eq_lintegral_enorm (hcont h).aestronglyMeasurable]
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    refine (ENNReal.toReal_mono (by finiteness) (key h)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

end GlobalTheory.WeilConv

end
end

