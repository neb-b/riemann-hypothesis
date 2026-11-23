module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

variable {D : D7} {V : HSp D} {n : ℕ}

def RatFrame (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h)

theorem ratF_injective (V : HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, γ₀, h₀, e⟩ h
  have h1 : finHom V γ = 1 := congrArg Subtype.val h
  have h2 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((finHom V γ).1 i j) = inclR (F := D.host.F) (Af D.host.F) (γ₀.1 i j) := by
      have : (matHom V γ).1 i j = inclR (F := D.host.F) (AF D.host.F) (γ₀.1 i j) :=
        (congrArg (fun g : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e).symm
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 i j) = _
      rw [this]
      simp [inclR]
    have hi : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) := by
      haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
      exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    apply hi
    rw [← h3, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  subst h2
  exact Subtype.ext (Subtype.ext (e.symm.trans (map_one _)))

def frameEquiv (P : principalLevelFrame.RowPsi V n) : GAf D.host.E n ≃* Bridge.Gf V :=
  MulEquiv.ofBijective ((finHom V).rangeRestrict.comp P.ψ)
    ⟨fun a b e => P.inj (TopMult.lift_unique (P.into a) (P.into b) e), fun y => by
      obtain ⟨h, hh, e⟩ := TopMult.exists_lift y
      obtain ⟨g, rfl⟩ := P.onto h hh
      exact ⟨g, e⟩⟩

theorem frameEquiv_apply (P : principalLevelFrame.RowPsi V n) (g) : frameEquiv P g = (finHom V).rangeRestrict (P.ψ g) := rfl

theorem RatFrame.iff {P : principalLevelFrame.RowPsi V n} (h : RatFrame P) (g) :
    g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ, Bridge.ratF V γ = frameEquiv P g :=
  (h g).trans ⟨fun ⟨γ, hγ, e⟩ => ⟨⟨γ, hγ⟩, Subtype.ext e⟩, fun ⟨γ, e⟩ => ⟨γ.1, γ.2, congrArg Subtype.val e⟩⟩

theorem comap_le_Umax {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsBaseFrame V β Λ 1)
    (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    (levEnv V β Lv).J.comap (frameEquiv P).toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
  (hP.2 κ).2 ((GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG (Lv := flag1L Lv) ⟨P.into κ, hκ⟩))

section Read

variable {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem weight_match (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    {x₀ : D.what₂.Mt μ j} (h₀ : x₀ ≠ 0) (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (δ : Γ) (hδ : ι δ = φ γ) (v : X.wt.W) :
    e (X.wt.ρ γ v) = ρ δ (e v) := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  let U : Subrepresentation X.wt.ρ := ⟨Submodule.span ℂ (Set.range (X.real x₀)), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => X.wt.ρ g w ∈ Submodule.span ℂ (Set.range (X.real x₀))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, (hA x₀).1.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := X.wt.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ (X.real_inj ?_)
    rw [map_zero]
    funext g
    have : X.real x₀ g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  have hv : v ∈ Submodule.span ℂ (Set.range (X.real x₀)) := by
    show v ∈ U.toSubmodule
    rw [hU]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => e (X.wt.ρ γ v) = ρ δ (e v)) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨h, rfl⟩
    have := hFm x₀ δ (φ h) 1
    rw [← (hA x₀).1.1 γ h, hread, hread, map_mul, ← hδ]
    simpa using this
  · simp
  · intro a b _ _ ha hb
    simp only [map_add (f := _), ha, hb]
  · intro c a _ ha
    simp only [map_smul, ha]

def pullForm : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ).comp e.toLinearMap).compl₂ e.toLinearMap

theorem pullForm_apply (a b : X.wt.W) : pullForm X e a b = inner ℂ (e a) (e b) := rfl

theorem classSum_of_read {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ, ι γ = φ h) (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : IsBounded (J.comap φ.toMonoidHom)) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x'))
    (h0 : (∀ x : D.what₂.Mt μ j, x = 0) → ∃ β, IsInvForm X.wt β) : ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := classSum_transport (W := W) ι hι φ hrat J y hy
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := h0 hz
    obtain ⟨T, c', hT, -, -⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  · obtain ⟨x₀, h₀⟩ := not_forall.1 hz
    have hβ : IsInvForm X.wt (pullForm X e) := by
      refine ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => ?_, fun γ a b => ?_⟩
      · rw [pullForm_apply]
        exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))
      · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
        have hw := weight_match X ι φ ρ J χ e Fm hFm hread h₀ γ δ hδ
        exact (congrArg₂ (inner ℂ) (hw a) (hw b)).trans (hρ δ _ _)
    obtain ⟨T, c', hT, hc', hcmp⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ (J.comap φ.toMonoidHom) (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
      ⟨(hA x).1, fun κ => funext fun g => e.injective (by
        have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
        show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
        rw [map_smul, hread, hread, map_mul]
        simpa using this)⟩
    refine ⟨_, T, c * c', hβ, hT, mul_pos hc hc', fun x x' => ?_⟩
    rw [hip, ← htr X.wt (pullForm X e) (X.real x) (X.real x') _ _ fun g => by rw [pullForm_apply, hread, hread],
      hcmp _ _ _ _ (hA x) (hA x') (hB x) (hB x')]
    push_cast
    ring

end Read

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodTypeNoChi

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem p_comp : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c c' : G → ℂ) (F : GA D V → ℂ),
    HasType V β (flag1L L) F →
      gaL V β L eG c (gaL V β L eG c' F) = gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F := by
  intro D V β L hL G _ _ eG c c' F hF
  have hm : ∀ y z : G, actL V β L (eG y) (actL V β L (eG z) F) = actL V β L (eG (y * z)) F := fun y z => by
    rw [map_mul]
    exact Formalism.IndefR.Eqv.Act.levelGroupAction_mul_of_lifts hL (eG y) (eG z) hF
  have lhs : gaL V β L eG c (gaL V β L eG c' F) =
      ∑ y : G, ∑ z : G, (c y * c' z) • actL V β L (eG (y * z)) F := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [mul_comm]
  have rhs : gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F =
      ∑ y : G, ∑ x : G, (c y * c' (y⁻¹ * x)) • actL V β L (eG x) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun z => by simp

theorem p_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ (i : Fin D.R.m) (t : T), LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i t
  obtain ⟨c, hc⟩ := h.βV i
  refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem isClass_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem charLab_inv {g : ℕ} [Fact g.Prime] {L : LabelDatum g} {θ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (h : GlobalTheory.GLp.IsCharLab L θ c) : GlobalTheory.GLp.IsCharLab L θ⁻¹ c⁻¹ := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨inv_ne_zero hc, fun u hu => ?_⟩
  have e1 : ((θ⁻¹ u : ℂˣ) : ℂ) = ((θ u : ℂˣ) : ℂ)⁻¹ := by simp
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective]
  have e2 : L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c⁻¹) = (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))⁻¹ := by
    rw [map_inv₀]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  rw [e1, hv u hu, e2]

theorem seriesKillsAvg : SeriesKillsAvg := by
  intro g _ L r f θ c hc hf hf' a b ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    cases r with
    | zero => exact absurd (_root_.funext fun i : Fin 0 => Fin.elim0 i) ha
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hfin, -⟩ := irr_finite_and_finsum_zOf_eq_one (Gn g (n + 1))
  rw [eSerC_eq_sum L (n + 1) hfin f, Finset.sum_mul]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hψ
  obtain ⟨hirr, hlab⟩ := hψ
  apply _root_.GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero g (n + 1) ψ hirr θ a b
  rw [_root_.GlobalTheory.MirAvg.tr_mirEl_indep g n ψ (isClass_irr hirr) θ a ha b]
  have hinv := charLab_inv hc
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).1]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (_root_.GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv g n ψ hirr θ).1 (right_ne_zero_of_mul hne)
    exact hf' ((_root_.GlobalTheory.GLq.DetRoot.root_of_hc_det g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).1 hip)
  · simp only [if_true]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).2]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (_root_.GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv g n ψ hirr θ).2 (right_ne_zero_of_mul hne)
    exact hf' ((_root_.GlobalTheory.GLq.DetRoot.root_of_hc_det g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).2 hip)

theorem goodNoChi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hc : GlobalTheory.Hk3.Core R F := hG.core
  have hl : R.toLevCh.Is A.μ0 := hc.lev
  have hL : LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := p_lifts D G Pl0 T A Ks R hl i t
  intro y hy PP a ha b ε hε l
  have hT : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) :=
    _root_.GlobalTheory.DefiniteType.hasType_extV D G Pl0 T A Ks R F hc i t y l
  have hy' := hy l
  have e1 := p_comp _ _ _ hL R.eG (mirC R i PP a b ε) (RealDat.eC (A := A) (sg0 D A)) _ hT
  have e0 := congrArg (gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a b ε)) hy'
  have h0 : (fun x => ∑ y, mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x)) = fun _ => 0 :=
    funext (GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero seriesKillsAvg D G Pl0 T A Ks R F hG i PP a ha b ε hε)
  have e2 := congrArg (fun c => gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG c (fun h => l (R.extV i t y h))) h0
  have e3 : gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (fun _ : G => (0 : ℂ)) (fun h => l (R.extV i t y h)) = 0 := by
    simp only [gaL, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  exact e0.symm.trans (e1.trans (e2.trans e3))

end GlobalTheory.GoodTypeNoChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CoordUnfold


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem integral_fundamentalDomain_eq_iterated_split : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  intro D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D s m
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D t m
  obtain ⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩ := GlobalTheory.MixModel.lattice_Mx D r m
  haveI : BorelSpace (Mx D s m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r m) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  haveI := hν.1
  haveI := hη.1
  haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩
  set rJ : Mx D r s := J.map (incA D) with hrJ
  set rK : Mx D r t := K.map (incA D) with hrK
  set rL : Mx D s r := L.map (incA D) with hrL
  set rM : Mx D t r := M.map (incA D) with hrM
  have hLJ' : rL * rJ = 1 := by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one
  have hLK' : rL * rK = 0 := by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero
  have hMJ' : rM * rJ = 0 := by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero
  have hMK' : rM * rK = 1 := by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one
  have hJLKM' : rJ * rL + rK * rM = 1 := by
    rw [hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add (f := _), hJLKM]
    · exact GlobalTheory.MixModel.rat_one
    · exact fun a b => map_add (incA D) a b
  let Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m :=
    { toFun := fun p => rJ * p.2 + rK * p.1
      invFun := fun u => (rM * u, rL * u)
      left_inv := by
        rintro ⟨v, y⟩
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      right_inv := by
        intro u
        show rJ * (rL * u) + rK * (rM * u) = u
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]
      map_add' := by
        rintro ⟨v, y⟩ ⟨v', y'⟩
        simp only [Prod.mk_add_mk, Matrix.mul_add]
        abel
      continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))
      continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }
  have hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v := fun _ _ => rfl
  let Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m := Ec.toHomeomorph.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl
  set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set mm : Measure (Mx D r m) := lam.map Me with hm
  haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hμm := Measure.isAddLeftInvariant_eq_smul μ mm
  set c := Measure.addHaarScalarFactor μ mm with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm
  set Γ : AddSubgroup (Mx D t m × Mx D s m) :=
    (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m := by
    rintro ⟨v, y⟩
    rw [hEapp]
    simp only [Γ, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨hv, hy⟩
      exact add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy)
        (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)
    · intro h
      have h1 : rM * (rJ * y + rK * v) = v := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]
      have h2 : rL * (rJ * y + rK * v) = y := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h
      · rw [← h2]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h
  have hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam := isAddFundamentalDomain_prod hη.2.1 hν.2.1
  have hac : lam.map Me ≪ μ := by
    intro A hA
    rw [hμm, Measure.smul_apply] at hA
    exact (smul_eq_zero.1 hA).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam μ := ⟨Me.measurable.aemeasurable, hac⟩
  let eΓ : GlobalTheory.MixModel.ratMx D r m → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p
      rw [hMe, hMe, map_add (f := _), Ec.apply_symm_apply])
  refine ⟨(c : ℝ), fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hKK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm := by
    rw [hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add (f := _)]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨) := by
    rw [Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  rfl

end GlobalTheory.CoordUnfold

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D ι π s r}

end GlobalTheory.TripleLocal

end
end

