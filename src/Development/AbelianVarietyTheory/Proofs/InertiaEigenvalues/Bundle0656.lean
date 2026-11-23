module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeRepresentativesRightTranslateIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.UpInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levW_le_GfC (R : RealDat D A Ks) (i : Fin D.R.m) {k : GA D (Wc D i)} (hk : k ∈ levW R i) :
    k ∈ GfC (Wc D i) := hk.1

theorem mem_locK_iff (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC (Wc D i)) :
    (g : GA D (Wc D i)) ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} ↔
      g ∈ KR R i ∧ cf (Wc D i) v g = g := by
  simp only [Set.mem_setOf_eq, KR, Subgroup.mem_subgroupOf, cf_eq_self_iff]

theorem dcRep_exists (R : RealDat D A Ks) (i : Fin D.R.m) (hT : TransLaws R i)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i)) (hα : cf (Wc D i) v α = α) :
    ∃ C, DCRep (cf (Wc D i) v) (KR R i) α C := by
  classical
  obtain ⟨C, hsupp, hrep⟩ := hT.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα)
  refine ⟨C.subtype (· ∈ GfC (Wc D i)), fun δ hδ => ?_, fun x ⟨k₁, k₂, h1, h2, h3, h4, hx⟩ => ?_⟩
  · rw [Finset.mem_subtype] at hδ
    refine ⟨(cf_eq_self_iff _ v δ).2 (hsupp _ hδ), ?_⟩
    obtain ⟨-, k₁, hk₁, k₂, hk₂, he⟩ := hrep.1 _ hδ
    refine ⟨⟨k₁, levW_le_GfC R i hk₁.1⟩, ⟨k₂, levW_le_GfC R i hk₂.1⟩, ?_⟩
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, levW_le_GfC R i hk₁.1⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, levW_le_GfC R i hk₂.1⟩).1 hk₂
    exact ⟨a1, a2, b1, b2, Subtype.ext he⟩
  · have hk₁ := (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩
    have hk₂ := (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩
    have hx' : (x : GA D (Wc D i)) = (k₁ : GA D (Wc D i)) * α * k₂ := by rw [hx]; rfl
    obtain ⟨γ, ⟨hγC, hγK⟩, huniq⟩ := hrep.2 x ⟨_, hk₁, _, hk₂, hx'⟩
    have hγG : γ ∈ GfC (Wc D i) := (hrep.1 γ hγC).1
    have e : ((⟨γ, hγG⟩⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = γ⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm := (mem_locK_iff R i v (⟨γ, hγG⟩⁻¹ * x)).1 (by rw [e]; exact hγK)
    refine ⟨⟨γ, hγG⟩, ⟨Finset.mem_subtype.2 hγC, hm⟩, ?_⟩
    rintro δ ⟨hδC, hδK, hδc⟩
    have e' : ((δ⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm' := (mem_locK_iff R i v (δ⁻¹ * x)).2 ⟨hδK, hδc⟩
    rw [e'] at hm'
    exact Subtype.ext (huniq (δ : GA D (Wc D i)) ⟨Finset.mem_subtype.1 hδC, hm'⟩)

theorem isCosetRep_map (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i))
    (C : Finset (GfC (Wc D i))) (hC : DCRep (cf (Wc D i) v) (KR R i) α C) :
    (∀ γ ∈ C.map (Function.Embedding.subtype _), SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} α
        (C.map (Function.Embedding.subtype _)) := by
  classical
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_, fun x ⟨k₁, hk₁, k₂, hk₂, hx⟩ => ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    exact (cf_eq_self_iff _ v δ).1 (hC.1 δ hδ).1
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨-, k₁, k₂, h1, h2, h3, h4, he⟩ := hC.1 δ hδ
    refine ⟨δ.2, k₁, (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩, k₂, (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩, ?_⟩
    simp [he]
  · have g₁ := levW_le_GfC R i hk₁.1
    have g₂ := levW_le_GfC R i hk₂.1
    have hxG : x ∈ GfC (Wc D i) := by
      rw [hx]; exact (GfC (Wc D i)).mul_mem ((GfC (Wc D i)).mul_mem g₁ α.2) g₂
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, g₁⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, g₂⟩).1 hk₂
    have hx2 : (⟨x, hxG⟩ : GfC (Wc D i)) = ⟨k₁, g₁⟩ * α * ⟨k₂, g₂⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hx
    have hex := hC.2 ⟨x, hxG⟩ ⟨_, _, a1, a2, b1, b2, hx2⟩
    obtain ⟨δ, ⟨hδC, hδK, hδc⟩, huniq⟩ := hex
    have hm := (mem_locK_iff R i v (δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).2 ⟨hδK, hδc⟩
    have e : ((δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e] at hm
    refine ⟨(δ : GA D (Wc D i)), ⟨Finset.mem_map_of_mem _ hδC, hm⟩, ?_⟩
    rintro γ ⟨hγC, hγK⟩
    obtain ⟨δ', hδ', rfl⟩ := Finset.mem_map.1 hγC
    have e' : ((δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ' : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨c1, c2⟩ := (mem_locK_iff R i v (δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).1 (by rw [e']; exact hγK)
    exact congrArg Subtype.val (huniq δ' ⟨hδ', c1, c2⟩)

theorem heckeReps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m),
    TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)),
    (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) →
    (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧
    (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C →
      ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hT B hB
  refine ⟨fun v α hα => dcRep_exists R i hT v α hα, fun v α C hα hC γ => ?_⟩
  obtain ⟨hs, hr⟩ := isCosetRep_map R i v α C hC
  have hB1 : ∀ y, B 1 y = y := fun y => ext_inner_left ℂ fun x => by
    rw [← hB, OneMemClass.coe_one, hT.2.2.2.2.2]
  have key : ∀ (γ : GfC (Wc D i)) y y', (∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' =
      ∑ δ ∈ C.map (Function.Embedding.subtype _), trPair R i (γ * δ) x y) →
      B γ y' = (∑ δ ∈ C, B (γ * δ)) y := fun γ y y' h => ext_inner_left ℂ fun x => by
    rw [← hB, h γ γ.2 x, Finset.sum_map, ContinuousLinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hB]; rfl
  ext y
  obtain ⟨y', -, hy'⟩ := hT.2.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα) _ hs hr y
  have e1 := key 1 y y' hy'
  simp only [one_mul, hB1] at e1
  rw [ContinuousLinearMap.mul_apply, ← e1, key γ y y' hy']

end GlobalTheory.UpInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKs
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HTBasisEx

variable {l : ℕ} [Fact l.Prime]

theorem basis_of_invariants (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hE : E.1 = Ks K s) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]) (D : Submodule ↥E.1 (Fin d → P.R.BdR))
    (hD : ∀ y ∈ D, ∀ g ∈ GK E,
      ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y)
    (hfin : Module.Finite ↥E.1 ↥D) (hd : Module.finrank ↥E.1 ↥D = d) :
    ∃ (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ), LinearIndependent (PadicComplex l) e ∧
      (∀ k, ∃ y ∈ D, (∀ i, y i ∈ (P.PD E).Fil (u k)) ∧ ¬ ∀ i, y i ∈ (P.PD E).Fil (u k + 1)) ∧
      ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
        (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (e k) = e k := by
  classical
  obtain ⟨sy, hsy⟩ := GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist l P AI Θ E
  have hsum : ∀ (a : ℤ) (t : Finset (Fin d)) (f : Fin d → P.R.BdR),
      (∀ j ∈ t, f j ∈ (P.PD E).Fil a) → sy a (∑ j ∈ t, f j) = ∑ j ∈ t, sy a (f j) := by
    intro a t f
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
    | insert j t hj ih =>
      intro hf
      have ht : ∀ j ∈ t, f j ∈ (P.PD E).Fil a := fun j h => hf j (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        (hsy a).1 _ (hf j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ ht), ih ht]
  obtain ⟨x, u, hx, hind⟩ := _root_.GlobalTheory.exists_family_adapted_filtration ↥E.1 (Fin d → P.R.BdR) D
    (fun a => Submodule.pi Set.univ fun _ => (P.PD E).Fil a) d hfin hd
    (fun a y hy i hi => (P.PD E).Fil_anti a (hy i hi))
    (by
      intro y
      choose n hn using fun i => (P.PD E).Fil_exh (y i)
      have hanti : Antitone (P.PD E).Fil := antitone_int_of_succ_le (P.PD E).Fil_anti
      obtain ⟨b, hb⟩ := (Set.finite_range n).bddBelow
      exact ⟨b, fun i _ => hanti (hb ⟨i, rfl⟩) (hn i)⟩)
    (fun y hy => funext fun i => (P.PD E).Fil_sep _ fun a => hy a i (Set.mem_univ i))
  have hxF : ∀ k i, x k i ∈ (P.PD E).Fil (u k) := fun k i => (hx k).2 i (Set.mem_univ i)
  have hact : ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
      (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (fun i => sy (u k) (x k i)) =
        fun i => sy (u k) (x k i) := by
    intro σ hσ k
    funext i
    have hg : ∀ j, P.actQdR σ (x k j) ∈ (P.PD E).Fil (u k) := fun j => by
      rw [← P.PD_actdR E ⟨σ, hσ⟩]
      exact (P.PD E).Fil_G _ _ _ (hxF k j)
    have h1 := congrFun (hD _ (hx k).1 σ hσ) i
    conv_rhs => rw [← h1]
    simp only [twAct, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum _ _ _ (fun j _ => by
      rw [← Algebra.smul_def]
      exact ((P.PD E).Fil (u k)).smul_of_tower_mem _ (hg j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, (hsy _).2.1 _ _ (hg j),
      (hsy _).2.2.2 σ _ (hxF k j), IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
    have hc : ∀ c : Om l, (c : PadicComplex l) = algebraMap (Om l) (PadicComplex l) c :=
      fun _ => rfl
    rw [hc]
    exact mul_left_comm _ _ _
  refine ⟨fun k i => sy (u k) (x k i), u, ?_, fun k => ⟨x k, (hx k).1, hxF k, fun h => ?_⟩, hact⟩
  · refine GlobalTheory.T.serreTate_linearIndependent_of_weightwise l AI.actC P.χQ (GK E) E.1 ?_ d d _ _ u hact ?_
    · intro i y hy
      have := _root_.GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs i y
        (by intro g hg; apply hy; unfold GK; rw [hE]; exact hg)
      rwa [hE]
    · intro a c hc h0
      refine hind a c hc fun i _ => ?_
      have hm : ∀ k, c k • x k i ∈ (P.PD E).Fil a := by
        intro k
        by_cases hk : u k = a
        · exact Submodule.smul_mem _ _ (hk ▸ hxF k i)
        · rw [hc k hk, zero_smul]; exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      refine ((hsy a).2.2.1 _ (Submodule.sum_mem _ fun k _ => hm k)).1 ?_
      rw [hsum a _ _ fun k _ => hm k]
      have h1 := congrFun h0 i
      rw [Finset.sum_apply, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : u k = a
      · subst hk
        exact (by rw [Pi.smul_apply, Algebra.smul_def]; exact (hsy _).2.1 _ _ (hxF k i))
      · simp only [Pi.smul_apply, hc k hk, zero_smul, ZeroMemClass.coe_zero, smul_eq_mul]
        rw [((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)]
        simp
  · have := hind (u k) (Pi.single k 1) (fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e])) _)
      (by
        intro i _
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h i) k
    simp at this


set_option maxHeartbeats 1600000 in
theorem htBasis_of_isCrys (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hEs : E.1 = Ks K s) (hle : K.1 ≤ E.1) (LL : FinExt l)
    (h7K : fontCore (P.PD K)) (h7E : fontCore (P.PD E))
    (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hcrys : IsCrys (P.PD E) (T'.ρ.comp (Subgroup.inclusion (GK_le hle))))
    {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T' M A)
    (m : ℕ) (hm : s ≤ m) :
    {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
      DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a}.Finite ∧
    HTBasis AI.actC P.χQ (Gj K m) M
      {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a} := by
  have hLL : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨bV, hbV⟩ := _root_.GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat l K LL T' d M A hM
  let ρ' : Representation ↥LL.1 ↥(GK E) T'.V := T'.ρ.comp (Subgroup.inclusion (GK_le hle))
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T'.V, ρ := T'.ρ, cont := T'.cont }
  let AE : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T'.V, ρ := ρ'
      cont := fun x => (T'.cont x).comp (continuous_inclusion (GK_le hle)) }
  have hK := h7K _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AK
  have hE := h7E _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AE
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  refine ⟨GlobalTheory.T.finite_setOf_inf_filtration_ne_succ _ _ (DdR (P.PD K) T'.ρ) (fun a => FilV (P.PD K) a) hK.2.1.1 hanti, ?_⟩
  classical
  let M0 : GQ l → Matrix (Fin d) (Fin d) ℚ_[l] := fun g =>
    if hg : g ∈ GK K then Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i else 0
  have hM0 : ∀ g (hg : g ∈ GK K), M0 g = Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i :=
    fun g hg => dif_pos hg
  have hmul : ∀ g ∈ GK K, ∀ g' ∈ GK K, M0 (g * g') = M0 g * M0 g' := by
    intro g hg g' hg'
    rw [hM0 g hg, hM0 g' hg', hM0 _ (mul_mem hg hg')]
    have key : ∀ γ : ↥(GK K), (Matrix.of fun i j => bV.repr (T'.ρ γ (bV j)) i) =
        LinearMap.toMatrix bV bV ((T'.ρ γ).restrictScalars ℚ_[l]) := fun γ => by
      ext i j
      rw [LinearMap.toMatrix_apply]; rfl
    have hcomp : (T'.ρ ⟨g * g', mul_mem hg hg'⟩).restrictScalars ℚ_[l] =
        (T'.ρ ⟨g, hg⟩).restrictScalars ℚ_[l] ∘ₗ (T'.ρ ⟨g', hg'⟩).restrictScalars ℚ_[l] := by
      refine LinearMap.ext fun v => ?_
      exact LinearMap.congr_fun (map_mul T'.ρ ⟨g, hg⟩ ⟨g', hg'⟩) v
    rw [key, key, key, hcomp]
    exact LinearMap.toMatrix_comp bV bV bV _ _
  obtain ⟨ΦE, -, hΦE⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD E) ρ' bV
  obtain ⟨DE, hDE, hfin, hdim⟩ := _root_.GlobalTheory.deRham_invariants_coord_finrank (P.PD E) ρ' bV hLL hE.2.1.1 (hE.2.2 hcrys) ΦE hΦE
  have hinv : ∀ y ∈ DE, ∀ g ∈ GK E,
      ((M0 g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y := by
    intro y hy g hg
    have := (hDE y).1 hy ⟨g, hg⟩
    simp only [P.PD_actdR] at this
    rw [hM0 g (GK_le hle hg)]
    exact this
  obtain ⟨e, u, hli, hu, hact⟩ := basis_of_invariants P AI Θ K s hs E hEs M0 DE
    hinv hfin hdim
  have hFil : ∀ a x, x ∈ (P.PD E).Fil a ↔ x ∈ (P.PD K).Fil a := fun a x =>
    Set.ext_iff.1 (P.PD_Fil E K a) x
  refine ⟨e, u, hli, fun k => ?_, fun σ hσ k => ?_⟩
  · obtain ⟨y, hy, hy1, hy2⟩ := hu k
    simp only [hFil] at hy1 hy2
    obtain ⟨z, hz, hz1, hz2⟩ := GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt l P K E hle d M0 hmul (u k) y (hinv y hy) hy1 hy2
    obtain ⟨Φ, h1, h2⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro heq
    have hmem : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := by
      refine ⟨?_, (h1 _ _).2 (by simpa using hz1)⟩
      simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply]
      have := hz g g.2
      rw [hM0 g g.2] at this
      simp only [P.PD_actdR]
      exact this
    have hmem' : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) := by
      have heq' : DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) =
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := heq
      rw [heq']; exact hmem
    exact hz2 (by simpa using (h1 _ _).1 hmem'.2)
  · have hσE : σ ∈ GK E := by
      refine IntermediateField.fixingSubgroup_le (?_ : E.1 ≤ Ks K m) hσ
      rw [hEs]
      refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      change x ^ (l ^ (s + n)) = 1
      rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]
    have hσK : σ ∈ GK K := GK_le hle hσE
    have hMσ : M σ = (M0 σ).map (algebraMap ℚ_[l] (PadicComplex l)) := by
      rw [hM0 σ hσK]
      ext i j
      exact hbV ⟨σ, hσK⟩ i j
    have := hact σ hσE k
    unfold twAct at this ⊢
    rw [hMσ]
    exact this

theorem exists_htBasis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  intro D HW F h7 l _ K s LL h S E' T hcr d M A hM m hm
  obtain ⟨Θ⟩ := _root_.GlobalTheory.ThetaTie.nonempty_thetaL D l
  obtain ⟨E, hEs⟩ : ∃ E : FinExt l, E.1 = Ks K s :=
    ⟨⟨Ks K s, GlobalTheory.MemLoc.finiteDimensional_Ks_of_finExt K s⟩, rfl⟩
  have hle : K.1 ≤ E.1 := hEs ▸ h.2.2.1
  exact htBasis_of_isCrys (D.loc l) (D.locA l) Θ K s ⟨h.1, h.2.1⟩ E hEs hle LL (h7 l K) (h7 l E) T
    (GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h) E hEs hle T hcr)
    M A hM m hm

end GlobalTheory.HTBasisEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

theorem unit_completion_approx_integer : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro E' _ _ w' u hu
  have hvF : ∀ z : E', Valued.v (algebraMap E' (w'.adicCompletion E') z) = w'.valuation E' z :=
    fun z => valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' z
  set x : w'.adicCompletion E' := (u : w'.adicCompletion E') with hxdef
  have hx1 : Valued.v x ≤ 1 := by
    have : Valued.v x = 1 := hu
    exact this.le
  have hopen : IsOpen {z : w'.adicCompletion E' | Valued.v (z - x) < 1} := by
    have h1 := Valued.isOpen_ball (w'.adicCompletion E') 1
    have h2 : {z : w'.adicCompletion E' | Valued.v (z - x) < 1} =
        (fun z => z - x) ⁻¹' {w | Valued.v.restrict w < 1} := by
      ext z; simp [Valuation.restrict_lt_one_iff]
    rw [h2]
    exact h1.preimage (continuous_id.sub continuous_const)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := 𝓞 E') (K := E') w').exists_mem_open hopen
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hk
  have hk1 : Valued.v (algebraMap E' (w'.adicCompletion E') k) ≤ 1 := by
    have : algebraMap E' (w'.adicCompletion E') k =
        (algebraMap E' (w'.adicCompletion E') k - x) + x := by ring
    rw [this]
    exact Valuation.map_add_le _ hk.le hx1
  have hk1' : w'.valuation E' k ≤ 1 := by
    rw [← hvF]; exact hk1
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer (K := E') w' hk1' 1
  refine ⟨a, ?_⟩
  have e1 : x - algebraMap E' (w'.adicCompletion E') (a : E') =
      (x - algebraMap E' (w'.adicCompletion E') k) +
      (algebraMap E' (w'.adicCompletion E') k - algebraMap E' (w'.adicCompletion E') (a : E')) := by
    ring
  rw [e1]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [← Valuation.map_neg, neg_sub]; exact hk
  · rw [← map_sub, hvF]
    have : w'.valuation E' ((a : E') - k) < 1 := by simpa using ha
    rw [← Valuation.map_neg, neg_sub]; exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitRealPrime

theorem exists_prime_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ p : ℕ, p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, -, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E 0
  refine ⟨p, hp, fun w hw => ?_⟩
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨a, b, hab, ha, hb⟩ :=
    GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
  by_cases h : a = w
  · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
  · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

end GlobalTheory.SplitRealPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacter
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.DegreeOne

theorem classOfDegreeOne_eq_ofChar : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 →
    ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  intro _ k _ _ _ _ _ x hx
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocLanglands.DegreeOne
end

