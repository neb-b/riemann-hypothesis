module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPair
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.ExtClassKs

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_ext [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (T Z : LocLat G Qp LL O) (htriv : ∀ g x, Z.ρ g x = x) (e₀ : ↥Z.L.T) (he₀ : (e₀ : Z.V) ≠ 0)
    (hone : Z.L.T = Submodule.span O {(e₀ : Z.V)}) (zc : ↥(latticeCocycles T.L)) :
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (et : ↥Y.L.T),
      IsSESLat (Qp := Qp) ι π ∧ π.f et = e₀ ∧ Module.finrank LL Y.V = Module.finrank LL T.V + 1 ∧
        ∀ g, ι.f ((zc : G → T.V) g) = Y.ρ g et - et := by
  let Yt : LocLat G Qp LL O := GlobalTheory.FiniteAdm.extLat hinj T zc
  let ι : LatHom T.L Yt.L :=
    { f := LinearMap.inl LL T.V LL
      equiv := fun g x => by
        change ((T.ρ g x, 0) : T.V × LL) = (T.ρ g x + (0 : LL) • (zc : G → T.V) g, 0)
        simp
      cont := by
        change Continuous fun x : T.V => ((x, 0) : T.V × LL)
        exact continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, 0, map_zero _⟩ }
  haveI : ContinuousSMul LL Z.V := IsModuleTopology.toContinuousSMul LL Z.V
  let π : LatHom Yt.L Z.L :=
    { f := (LinearMap.toSpanSingleton LL Z.V (e₀ : Z.V)).comp (LinearMap.snd LL T.V LL)
      equiv := fun g x => by
        rw [htriv]
        rfl
      cont := by
        change Continuous fun x : T.V × LL => x.2 • (e₀ : Z.V)
        exact continuous_snd.smul continuous_const
      T_le := by
        rintro ⟨v, a⟩ ⟨-, o, rfl⟩
        change (algebraMap O LL o) • (e₀ : Z.V) ∈ Z.L.T
        rw [algebraMap_smul]
        exact Z.L.T.smul_mem o e₀.2 }
  refine ⟨Yt, ι, π, ⟨((0 : T.V), (1 : LL)), Submodule.zero_mem _, 1, map_one (algebraMap O LL)⟩,
    ⟨LinearMap.inl_injective, ?_, ?_, ?_, ?_⟩, one_smul LL (e₀ : Z.V), ?_, ?_⟩
  · intro w
    have hw : w ∈ Submodule.span LL {(e₀ : Z.V)} := by
      rw [← Submodule.span_span_of_tower O, ← hone, Z.L.span]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), a), rfl⟩
  · intro w hw
    rw [hone] at hw
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), algebraMap O LL o), ⟨Submodule.zero_mem _, o, rfl⟩,
      algebraMap_smul LL o (e₀ : Z.V)⟩
  · rintro ⟨w, a⟩
    constructor
    · intro h0
      have ha : a = 0 := (smul_eq_zero.1 (show a • (e₀ : Z.V) = 0 from h0)).resolve_right he₀
      exact ⟨w, Prod.ext rfl ha.symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact zero_smul LL (e₀ : Z.V)
  · intro y hy
    exact hy.1
  · change Module.finrank LL (T.V × LL) = _
    rw [Module.finrank_prod, Module.finrank_self]
  · intro g
    change (((zc : G → T.V) g, 0) : T.V × LL) =
      ((T.ρ g 0 + (1 : LL) • (zc : G → T.V) g - 0, 1 - 1) : T.V × LL)
    simp

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem generic [T2Space LL] [IsTopologicalRing LL] (E : EtTie W RA RW inclR φR gR πA)
    (hinj : Function.Injective (algebraMap O LL)) (hR : Function.Injective (algebraMap O RW))
    (hdense : ∀ M : Submonoid ↥W.GKs, IsClosed (M : Set ↥W.GKs) →
      (∀ g : ↥W.GKs, W.resΓ (g : G) = 1 → g ∈ M) → (∀ g : ↥W.GKs, W.resΓ (g : G) = W.gam → g ∈ M) →
      ∀ g, g ∈ M)
    (T : LocLat G Qp LL O) (hGKs : W.GKs = ⊤) (M p : ℕ)
    (hBK : ∀ (Y : LocLat G Qp LL O) (ι : T.V →ₗ[LL] Y.V), (∀ g x, ι (T.ρ g x) = Y.ρ g (ι x)) →
      Function.Injective ι → Module.finrank LL Y.V = Module.finrank LL T.V + 1 →
      ∀ x : Y.V, x ∉ LinearMap.range ι → ∀ c : G → T.V, (∀ g, ι (c g) = Y.ρ g x - x) →
      (∃ y : T.V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ g y - y) → IsCrys PD Y.ρ)
    (hlift : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L), IsCrys PD Y.ρ →
      IsSESLat (Qp := Qp) ι π →
      ∃ c : ℕ, ∀ z ∈ W.N W.one, ∃ y ∈ W.N Y, W.map π y = (p : LetA O n) ^ c • z)
    (hint : p8 W T M) (κ : LatticeCohomology (resLat T W.GKs)) (hκ : κ ∈ H1fIntegralCyclotomicLayer W T) :
    ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ M) ∧ z ∈ aN W T W.X ∧
      W.cl T ⟨(y, z), hyz⟩ = (p ^ c : ℕ) • κ := by
  obtain ⟨c₀, hc₀, rfl⟩ := hκ
  obtain ⟨xB, hxB⟩ : ∃ x : T.V ⊗[Qp] B, ∀ g : ↥W.GKs,
      (c₀ : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (g : G) x - x := hc₀.2.2
  have hmem : ∀ g, g ∈ W.GKs := fun g => by rw [hGKs]; exact Subgroup.mem_top g
  have hz1 : (fun g => (c₀ : ↥W.GKs → T.V) ⟨g, hmem g⟩) ∈ latticeCocycles T.L :=
    ⟨⟨c₀.2.1.1.comp (Continuous.subtype_mk continuous_id hmem),
      fun g g' => c₀.2.1.2 ⟨g, hmem g⟩ ⟨g', hmem g'⟩⟩, fun g _ => c₀.2.2 ⟨g, hmem g⟩ (Set.mem_univ _)⟩
  obtain ⟨e, e₀, hspan, hje, hN⟩ := E.one_e
  have hone : W.one.L.T = Submodule.span O {(e₀ : W.one.V)} := by
    have h1 := congrArg (Submodule.map W.one.L.T.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨e', he', hsp⟩ := W.one_line
    have : e' ∈ W.one.L.T := by rw [hsp]; exact Submodule.mem_span_singleton_self e'
    rw [hone, h0, Submodule.span_singleton_eq_bot.2 rfl] at this
    exact he' ((Submodule.mem_bot _).1 this)
  have hφe : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγe : ∀ g, W.γD W.one g e = e := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have h1 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
    rw [E.jD_act, hje]
    simp [TWact, h1]
  have heN : e ∈ W.N W.one := by rw [hN]; exact Submodule.mem_span_singleton_self e
  obtain ⟨Y, ι, π, et, hS, hπ, hrk, hc⟩ := exists_ext hinj T W.one W.one_triv e₀ he₀ hone ⟨_, hz1⟩
  have hY : IsCrys PD Y.ρ := hBK Y ι.f ι.equiv hS.1 hrk et
    (fun hx => he₀ (by rw [← hπ]; exact (hS.2.2.2.1 _).2 hx)) _ hc ⟨xB, fun g => hxB ⟨g, hmem g⟩⟩
  obtain ⟨k, hk⟩ := hlift Y ι π hY hS
  obtain ⟨x, hxN, hxπ⟩ := hk e heN
  have hxπ' : W.map π x = ((p : O) ^ k) • e := by
    rw [hxπ, ← algebraMap_smul (LetA O n) ((p : O) ^ k) e, map_pow, map_natCast]
  obtain ⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩ := hint Y ι π hS hY e heN hφe hγe x hxN _ hxπ'
  have hιinj : Function.Injective (W.map ι) := by
    intro a b hab
    apply E.jD_inj T
    apply GlobalTheory.Cyc.DictKs.lTensor_inj hS RW
    have h1 := congrArg (E.jD Y) hab
    rw [E.jD_map, E.jD_map] at h1
    exact h1
  have key : W.map ι ((W.γD T W.gam y - y) - (W.φD T z - z)) = W.map ι 0 := by
    rw [map_zero, map_sub, map_sub, map_sub, W.map_γ, W.map_φ, hyι, hzι, LocWach.γ, map_sub, map_sub,
      W.φγ_comm]
    abel
  have hyz : (y, z) ∈ W.divisibleCocycles T := by
    have h0 := hιinj key
    rw [sub_eq_add_neg] at h0
    exact h0
  refine ⟨k, y, z, hyz, hy, hz, ?_⟩
  refine (GlobalTheory.Cyc.DictKs.generic E hR hdense T Y W.one ι π hS (((p : O) ^ k) • et) (((p : O) ^ k) • e₀) x
    (by
      rw [Submodule.coe_smul, Submodule.coe_smul, ← hπ, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        map_smul, algebraMap_smul])
    (by rw [hxπ', map_smul, hje, TensorProduct.tmul_smul]) ⟨(y, z), hyz⟩ hyι hzι (((p : O) ^ k) • c₀)
    (fun g => by
      have h1 := hc g
      change ι.f ((c₀ : ↥W.GKs → T.V) g) = _ at h1
      change ι.f (((p : O) ^ k) • (c₀ : ↥W.GKs → T.V) g) = _
      rw [Submodule.coe_smul, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        ← algebraMap_smul LL ((p : O) ^ k) ((c₀ : ↥W.GKs → T.V) g), map_smul, map_smul, h1, smul_sub])).trans ?_
  rw [Submodule.Quotient.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

end Generic


set_option maxHeartbeats 1600000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT hGKs M hh hJ κ hκ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  refine generic E (fun a b hab => Subtype.ext hab) (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL)
    (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h)) T hGKs (mx M) l
    ?_ ?_ (_root_.GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places D HW F Cm l K s LL h T M hh hT hJ) κ hκ
  · intro Y ι h1 h2 h3 x h4 c h5
    exact (GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Y.V Y.ρ ι
      h1 h2 h3 hT x h4 c h5).1
  · intro Y ι π hY hS
    exact (GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T Y _ ι π hT hY (Formalism.MainNotions.LiftingTheory.gen_one_crys _) hS).imp
      fun c hc z hz => (hc z hz).1

end GlobalTheory.NL.ExtClassKs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.GenCountUnram

theorem admGenL_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  intro D l _ K LL
  unfold Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound
  intro hbij T hT
  have ht := D.locT l
  have hgood := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have h27 := GlobalTheory.T.h1fT_span_card_bound l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood T
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) ht K LL T.V T.ρ hT).1
  have hgen := h27 hDR
  obtain ⟨s, hs, hcard⟩ := hgen
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := ⟨T.V, T.ρ, T.cont⟩
  have hseq0 := GlobalTheory.SeqDim.h1f_finrank l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood A
  have hseq := (hseq0 hDR).2
  have hdR0 := GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) ht K LL T.V T.ρ
  haveI := hdR0.1
  have hdR := hdR0.2
  have hK : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij).toLinearEquiv.finrank_eq.symm
  refine ⟨s, hs, ?_⟩
  rw [hK] at hdR
  have hle : finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0)
      ≤ finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ) := Submodule.finrank_mono inf_le_left
  have hmul : finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V + finrank ↥LL.1 T.V
      = (finrank ℚ_[l] ↥(K0 K) + 1) * finrank ↥LL.1 T.V := by ring
  rw [← hmul]
  zify at hcard hdR hle ⊢
  linarith

end GlobalTheory.GenCountUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fKsOntoUpToPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.RightExactKs


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem h1fKs_onto_up_to_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), Function.Surjective π.f → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ κ₂ ∈ H1fIntegralCyclotomicLayer W T₂, ∃ (c : ℕ), ∃ κ₁ ∈ H1fIntegralCyclotomicLayer W T₁, (resHom π W.GKs).H1map κ₁ = (l ^ c : ℕ) • κ₂ := by
  intro D HW l _ K s LL h W T₁ T₂ π hπ h₁ h₂ κ₂ hκ₂
  refine (Submodule.mem_map.1 hκ₂).elim fun c₂ hc => ?_
  have hf : ((c₂ : _) : ↥W.GKs → T₂.V) ∈ BlochKatoCocyclesSubgroup ((D.loc l).PD K) W.GKs T₂ := hc.1.2
  refine hf.2.elim fun x hx => ?_
  refine (lift_cocycle (D.loc l) (D.locA l) (D.locT l) h.2.2.1 W ((HW l).W_s K s LL h)
    T₁ T₂ π hπ h₁ h₂ c₂ κ₂ hc.2 x hx).elim fun n hn => hn.elim fun c₁ hn =>
      hn.elim fun κ₁ hn => ?_
  refine ⟨n, κ₁, Submodule.mem_map.2 ⟨c₁, ⟨c₁.2, ?_⟩, hn.1⟩, hn.2.2⟩
  exact ⟨mem_continuousCocycles_restrictLattice T₁ W.GKs c₁, hn.2.1⟩

end GlobalTheory.NL.RightExactKs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.IntConnTaylor

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK
  obtain ⟨sh, φ₂, h1, h2, h3⟩ := GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible l (↥LL.1)
  obtain ⟨ε, hε0, hεφ, hεS⟩ := GlobalTheory.T.exists_integral_crystal_stratification_matrix hBS l a e ϖ LL hl2 ι P T I hBK sh φ₂ h1 h2 h3
  have hc := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow (↥(OL LL)) (↥LL.1) l e a ι P sh φ₂ h1 h2 h3 ε hε0 hεφ
  have hphi : ∀ j, P.phi (bas j) ∈ P.MM := fun j =>
    P.ext_mono (fun _ h => A_le_S l e h) (P.phi_mem_L (P.bas_mem_M j))
  have hpow : ∀ (n : ℕ) (j : ι), (P.nabla ^ n) (P.phi (bas j)) ∈ P.MM := fun n j =>
    mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => by rw [← hc τ n i j]; exact hεS τ i j n
  have hMM : ∀ m ∈ P.MM, P.nabla m ∈ P.MM := fun m hm =>
    P.nabla_mem_MM_of_basis (fun j => by simpa using hpow 1 j) hphi hm
  let C : Conn P := ⟨P.nabla, fun f v => P.nabla_smul_tot f v, hMM⟩
  have hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k *
      (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e := fun τ j k i =>
    mul_mem (pow_mem (uIn (S (↥(OL LL)) (↥LL.1) e)).2 k)
      (P.mem_extc_iff.1 (mem_tot.1 (hpow k j) τ) i)
  exact ⟨C, rfl, _root_.GlobalTheory.TaylorBasis.main l a e ϖ LL hl2 ι P _ _ C hS (GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis hBS l a e ϖ LL hl2 ι P T I hBK hS)⟩

end GlobalTheory.IntConnTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.LocGL

section FiniteGroup

variable {G V W X Y : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ W]

theorem charIdem_apply (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v =
      ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v := by
  simp [charIdem, LinearMap.sum_apply]

theorem map_charIdem {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : V) : φ (charIdem σ τ v) = charIdem σ' τ (φ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [charIdem_apply, map_smul, map_sum, φ.isIntertwining]

theorem charIdem_apply_rep (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) (v : V) :
    charIdem σ τ (σ h v) = σ h (charIdem σ τ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [charIdem_apply, map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  have e : LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) = LinearMap.trace ℂ W (τ g⁻¹) := by
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group]
    exact τ.char_conj g⁻¹ h
  show _ = LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) • σ (h * g * h⁻¹) (σ h v)
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem commute_charIdem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) :
    Commute (charIdem σ τ) (σ h) := LinearMap.ext (charIdem_apply_rep σ τ h)

def coeffMap (σ : Representation ℂ G V) (τ : Representation ℂ G W) (ℓ : Module.Dual ℂ W) (v : V) :
    τ.IntertwiningMap σ where
  toLinearMap := ∑ g : G, (ℓ ∘ₗ τ g⁻¹).smulRight (σ g v)
  isIntertwining' h := LinearMap.ext fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
    simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem charIdem_mem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v ∈ isotypic σ τ := by
  classical
  let b := Module.finBasis ℂ W
  have key : ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v = ∑ i, coeffMap σ τ (b.coord i) v (b i) := by
    have : ∀ i, coeffMap σ τ (b.coord i) v (b i) = ∑ g : G, b.repr (τ g⁻¹ (b i)) i • σ g v := fun i => by
      show (∑ g : G, (b.coord i ∘ₗ τ g⁻¹).smulRight (σ g v)) (b i) = _
      simp [LinearMap.sum_apply]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  rw [charIdem_apply, key]
  exact (isotypic σ τ).toSubmodule.smul_mem _ (Submodule.sum_mem _ fun i _ => apply_mem_isotypic _ _)

theorem charIdem_self {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) : charIdem τ τ = 1 := by
  have := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
    ⟨charIdem τ τ, fun g => commute_charIdem τ τ g⟩
  have h1 : charIdem τ τ = c • (1 : Module.End ℂ W) :=
    LinearMap.ext fun w => (congrArg (fun f : τ.IntertwiningMap τ => f w) hc).symm
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have ho := Representation.char_orthonormal τ τ
  rw [if_pos ⟨.refl _⟩, Nat.card_eq_fintype_card] at ho
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 : LinearMap.trace ℂ W (charIdem τ τ) = Module.finrank ℂ W := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [charIdem, map_smul, map_sum, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
    refine (congrArg _ (Eq.trans ?_ ho)).trans (mul_one _)
    exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)
  rw [h1, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
  rw [h1, mul_right_cancel₀ hd (h2.trans (one_mul _).symm), one_smul]

theorem charIdem_of_mem {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) {v : V}
    (hv : v ∈ isotypic σ τ) : charIdem σ τ v = v := by
  refine Submodule.iSup_induction _ (motive := fun v => charIdem σ τ v = v) hv ?_ (map_zero _) fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact (map_charIdem f τ w).symm.trans (by rw [charIdem_self hτ]; rfl)
  · rw [map_add (f := _), hx, hy]

end FiniteGroup

section Compact

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}

theorem map_idem (hπ : IsSmooth π) (hσ : IsSmooth σ) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) (v : V) :
    f (idem hπ hH v) = idem hσ hH (f v) := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  rw [idem_eq_cosetSum hπ hH U hU, idem_eq_cosetSum hσ hH U fun u hu => by rw [← f.isIntertwining, hU u hu]]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, f.isIntertwining]

theorem map_idem_of_mem (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : f (idem hπ hH v) = f v := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [idem_eq_cosetSum hπ hH U hU]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, f.isIntertwining]
  rw [Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_mem_fixed_map_eq (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : ∃ u ∈ fixed π H, f u = f v :=
  ⟨_, idem_mem hπ hH v, map_idem_of_mem hπ hH f hv⟩

theorem map_fixed_of_surjective (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) {f : π.IntertwiningMap σ}
    (hf : Function.Surjective f) : (fixed π H).map f.toLinearMap = fixed σ H := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_fixed.2 fun u hu => by rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  · obtain ⟨v, rfl⟩ := hf w
    exact exists_mem_fixed_map_eq hπ hH f hw

end Compact

section LevelZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W}
  {ρ : Representation ℂ (GL n k) X}

theorem levelZeroMap_injective {f : π.IntertwiningMap σ} (hf : Function.Injective f) :
    Function.Injective (levelZeroMap f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem levelZeroMap_surjective (hπ : IsSmooth π) {f : π.IntertwiningMap σ} (hf : Function.Surjective f) :
    Function.Surjective (levelZeroMap f) := by
  rintro ⟨x, hx⟩
  obtain ⟨v, rfl⟩ := hf x
  obtain ⟨u, hu, h⟩ := exists_mem_fixed_map_eq hπ (levelPre_bot (k := k) (n := n) ▸ isCompact_levelPre ⊥) f hx
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

end LevelZero

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryAdelicMatrixAddHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus

theorem map_mul_right_unitary : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D m V.rank)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m V.rank => (HMul.hMul (x : Matrix (Fin m) (Fin V.rank) (AE D)) (mt V g) : Mx D m V.rank)) = μ := by
  intro D V m g μ hμ
  exact _root_.GlobalTheory.mul_unitary_map_haar D V.rank m V.gram (fun a b => V.herm.eq (V.frame b) (V.frame a)) (gram_det_ne V) g μ hμ

end GlobalTheory.AdelicModulus
end

