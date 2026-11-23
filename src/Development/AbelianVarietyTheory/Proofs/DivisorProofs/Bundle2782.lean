module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareChars_isGood : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∃ S₀ Q : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ S₀ ∪ Q, (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
        Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v)) ∧
      ∀ B : Base D.host.F D.host.E, S₀ ∪ Q ⊆ B.P → B.v₁ ∉ S₀ ∪ Q → SplitsFully D.host.E B.v₁ →
        HasExp B.emb (alpha G t i j) B.mα → HasExp B.emb (beta G i j) B.mβ →
        Chars.IsGood B ⟨alpha G t i j, beta G i j, S₀, Q⟩ (spW G i j).rank (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _hst
  refine ⟨G.pl.S0, (L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · have hw : G.pl.w v ∈ locPl G t := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
      have e := G.pl.under_w hv
      exact ⟨⟨_, hw, e⟩, e ▸ _root_.GlobalTheory.LocPlSplit.locPl_split hL t _ hw⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hv).1
      have hw : P ∈ locPl G t := Finset.mem_union_right _ hP
      exact ⟨⟨P, hw, e⟩, e ▸ _root_.GlobalTheory.LocPlSplit.locPl_split hL t _ hw⟩
  · intro B hsub hv₁ hsp hα hβ
    have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
    obtain ⟨rα, rβ⟩ := _root_.GlobalTheory.SquareResChars.resEta_alpha_beta hL t i j
    refine ⟨?_, ?_, _root_.GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rα, _root_.GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rβ, hα, hβ, ?_, hsub, ?_, ?_, ?_, ⟨hv₁, hsp⟩⟩
    · have hm := (hL.mu0 j).1
      have hx := (hL.xi t).1
      have he := hL.eta.1
      refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
      have e1 := hm.2 x
      have e2 := hx.2 x
      have e3 := he.2 x
      show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply]
      rw [e1, e2, e3]
      simp
    · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
      have he := hL.eta.1
      refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
      have e1 := hc.2 x
      have e3 := he.2 x
      show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply, e1, e3]
      simp
    · exact Finset.disjoint_sdiff
    · intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
        · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
        · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hw
        obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h1
        exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P hP e h2
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      refine GlobalTheory.T.alpha_unramified_outside hL t i j w (fun h => hw' (Finset.mem_union_left _ h)) fun P hP e => hw' ?_
      by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨P, hP, e⟩, h⟩)
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.SympLevelExt

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem map_linComb {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {T : Over S}
    {T' : Over S'} (ρ : (T ⟶ A) →* (T' ⟶ A')) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    ρ (linComb y a) = linComb (fun i => ρ (y i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact map_pow ρ (y i) (a i)

theorem dense_of_bot_mem {R : Type} [CommRing R] [IsDomain R] (D : Set (Sp R))
    (hD : (⊥ : PrimeSpectrum R) ∈ D) : Dense D := by
  intro p
  have hs : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)

theorem extend_torsion {R F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ G) (hx : x ^ n = 1) :
    ∃ σ : baseOver (Sp R) ⟶ G, σ ^ n = 1 ∧ spMap (algebraMap R F) ≫ σ.left = x.left := by
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (spMap (algebraMap R F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (spMap (algebraMap R F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))
  have j₃ : IsDominant (spMap (algebraMap R F)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R F (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _)
    (by simp)
  let σ' : baseOver (Sp R) ⟶ G := Over.homMk σ (by simpa using hσ₁)
  have hσ : spMap (algebraMap R F) ≫ σ'.left = x.left := by
    show spMap (algebraMap R F) ≫ σ = x.left
    simpa using hσ₂
  refine ⟨σ', ?_, hσ⟩
  let U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R F)) (by simp)
  have hU : U ≫ σ' = x := Over.OverMorphism.ext hσ
  have e : U ≫ σ' ^ n = U ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]
  exact over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _
    (congrArg (fun q => q.left) e)

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem generic_basis {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    {Q : PolAV (Sp F)} (G : Over (Sp R)) [GrpObj G] (φ : Q.A.left ⟶ G.left)
    (hp : IsGrpPullback Q.A G (spMap (algebraMap R F)) φ) (k : ℕ) [NeZero k] (ze₀ : Γ(Sp F, ⊤)ˣ)
    (lev₀ : Out.Level Q k ze₀) (y : Fin (2 * Q.g) → (baseOver (Sp R) ⟶ G))
    (hy : ∀ i, (lev₀.pt i).left ≫ φ = spMap (algebraMap R F) ≫ (y i).left)
    (z : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶ G) (hz : z ^ k = 1) :
    ∃! c : Fin (2 * Q.g) → ZMod k,
      linComb (fun i => (Over.homMk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F))
        (by simp) : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶
          baseOver (Sp R)) ≫ y i) (fun i => (c i).val) = z := by
  let s : Sp (AlgebraicClosure F) ⟶ Sp F := spMap (algebraMap F (AlgebraicClosure F))
  let T : Over (Sp F) := Over.mk s
  let ρ := pushHom hp T
  have hinj : Function.Injective ρ := fun a b hab => by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · exact congrArg (fun q => q.left) hab
    · rw [Over.w a, Over.w b]
  have hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w := fun w =>
    ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  have hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) =
      (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i := fun i => by
    apply Over.OverMorphism.ext
    show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left
    rw [Category.assoc, hy, Category.assoc]
  have hlin : ∀ d : Fin (2 * Q.g) → ℕ,
      ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) =
      linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d := fun d => by
    rw [map_linComb]
    simp only [hcomp]
  obtain ⟨a, rfl⟩ := hsurj z
  have ha : a ^ k = 1 := hinj (by rw [map_pow, hz, map_one])
  obtain ⟨c, hc⟩ := lev₀.span (AlgebraicClosure F) s a ha
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩
  · show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a
    simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]
    rw [← hlin, hc]
  · intro c' hc'
    have e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i)
        (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a := by
      rw [hlin]; exact hc'
    have e' := lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)
    funext i
    have := congrArg (fun f => ((f i : ℕ) : ZMod k)) e'
    simpa using this

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem level_extends : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  intro R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev
  obtain ⟨lev₀⟩ := hlev
  cases Q with
  | mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt =>
  dsimp only at hg
  subst hg
  have hL := abelianSchemeLaws_all.1
  haveI : NeZero K := ⟨hK.ne'⟩
  let j := spMap (algebraMap R F)
  let P : PolAV (Sp R) :=
    { A := (Over.pullback (spMap h)).obj P₁.A
      isAb := TLinPf.isAb_pullback (spMap h) P₁.A P₁.isAb
      g := P₁.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P₁.A (spMap h)).1 P₁.smoothDim
      L := P₁.L.pull (pullback.fst P₁.A.hom (spMap h))
      isLB := pull_isLB P₁.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.sym
      ample := by
        haveI := P₁.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback P₁.isLB P₁.ample (IsPullback.of_hasPullback P₁.A.hom (spMap h))
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P₁.isLB (pullback.fst P₁.A.hom (spMap h)))
        exact kTriv_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.isLB (pull_isLB P₁.isLB _) ((isGen_iff w).1 hw) P₁.ktriv }
  let ψ : P.A.left ⟶ P₁.A.left := pullback.fst P₁.A.hom (spMap h)
  have hψ : IsGrpPullback P.A P₁.A (spMap h) ψ := isGrpPullback_pullback P₁.A (spMap h)
  have hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h := by
    simp only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h := by rw [hpb.1.w, hc, Category.assoc]
  let φ' : QA.left ⟶ P.A.left := hψ.1.lift φ (QA.hom ≫ j) hw
  have e₁ : φ' ≫ ψ = φ := hψ.1.lift_fst _ _ _
  have e₂ : φ' ≫ P.A.hom = QA.hom ≫ j := hψ.1.lift_snd _ _ _
  have hpb' : IsGrpPullback QA P.A j φ' := hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂
  have hQL' : LBIso QL (P.L.pull φ') := by
    refine LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_
    have := lbIso_pull_comp P₁.isLB ψ φ'
    rw [e₁] at this
    exact this
  have hP : IsProper P.A.hom := P.isAb.proper
  have := P.isAb.comm
  choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) =>
    extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i))
      (by rw [← map_pow, lev₀.torsion, map_one])
  have hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left := fun i => (hy₂ i).symm
  have hKu' : IsUnit (K : Γ(Sp R, ⊤)) := by
    have := hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  let x : Sp (AlgebraicClosure F) ⟶ Sp R := spMap (algebraMap F (AlgebraicClosure F)) ≫ j
  have hx : (⊥ : PrimeSpectrum R) ∈ Set.range x := by
    obtain ⟨w⟩ : Nonempty (Sp (AlgebraicClosure F)) := inferInstance
    refine ⟨w, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w),
      Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]
  have hbasis := torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁
    (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp,
      fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K _ lev₀ y hy z hz⟩)
  have hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R)
      (c c' : Fin (2 * P.g) → Fin K),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro F' _ _ s c c' hcc
    obtain ⟨d, -, hd⟩ := hbasis F' s
      (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)))
      (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)
    have h₁ := hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])
    have h₂ := hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)
    funext i
    apply Fin.ext
    have := congrArg (fun f => (f i).val) (h₁.trans h₂.symm)
    simpa only [ZMod.val_natCast_of_lt (Fin.is_lt _)] using this
  obtain ⟨lev, -⟩ := level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ'
    hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by
      obtain rfl : i₀ = i := Fin.ext hi
      exact hy i₀) hind
  exact ⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩

end GlobalTheory.SympLevelExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoBergmanMeasureChernFormPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_of_abs_sub_le_eventually (a q : ℕ → ℝ) (I G W V C : ℝ) (hC : 0 ≤ C) (hq : Tendsto q atTop (𝓝 G))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, |a m - I - ε * W| ≤ C * (G + ε * V - q m)) : Tendsto a atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hK : 0 < |W| + C * |V| + 1 := by positivity
  set ε := e / (2 * (|W| + C * |V| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hq' := Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)
  filter_upwards [h ε hε0, hq'] with m hm hqm
  rw [Real.dist_eq] at hqm ⊢
  have h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W| := by
    have := abs_add_le (a m - I - ε * W) (ε * W)
    rw [abs_mul, abs_of_pos hε0] at this
    simpa using this
  have h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := neg_abs_le (q m - G)
    have := le_abs_self V
    nlinarith
  have h3 : C * |q m - G| ≤ (C + 1) * |q m - G| := by nlinarith [abs_nonneg (q m - G)]
  have h4 : (C + 1) * |q m - G| < e / 2 := by
    have := mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)
    rwa [mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)] at this
  have h5 : ε * (|W| + C * |V|) < e / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg W, abs_nonneg V]
  nlinarith

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_finsum_integral_berg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  intro k _ X _ p D hX hG P hpos ω r f hf hli hr w hw
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hcpt : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hfm : ∀ σ, IsFiniteMeasure (ω σ).meas := fun σ => (_root_.GlobalTheory.HSAmp.volDens_meas_finite_openPos k X p D hX hG σ (ω σ)).1
  choose ρ hρR hρ0 hρint using fun σ => _root_.GlobalTheory.HSAmp.exists_isRatio_chernInt k X p D hX hG P.L hpos σ (ω σ)
  have hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C := fun σ g hg => by
    haveI := hcpt σ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  have hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas := fun σ g hg => by
    haveI := hfm σ
    obtain ⟨C, hC⟩ := hbd σ g hg
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)
  set C : ℝ := ∑ σ, |Cw σ| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwC : ∀ σ y, |w σ y| ≤ C := fun σ y => (hCw σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw
  set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'
  set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW
  set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV
  have hch : chInt P.L D w = Iw := by
    simp only [chInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)
  have hgd : gdeg P.L D = G' := by
    simp only [gdeg, chInt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hρint σ _ continuous_const]
    simp
  rw [hch]
  rw [hgd] at hr
  refine tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial)
    (G' / D.factorial) W V C hC0 hr fun ε hε => ?_
  filter_upwards [_root_.GlobalTheory.HSAmp.Morse.cmb_le k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1
  obtain ⟨hfam, hpd, -⟩ := _root_.GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  obtain ⟨hBi, hBs, hB0, hBx⟩ := _root_.GlobalTheory.HSAmp.berg_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m))
    (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd
  set M : ℝ := (m : ℝ) ^ D with hMdef
  have hM : 0 < M := pow_pos (by exact_mod_cast hm1) D
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M :=
    fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le)
      fun c => hmo (Fin (r m)) (f m) (hf m) c σ y
  have hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas := fun σ => by
    haveI := hfm σ
    exact (((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M
  have hl1 := abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas)
    (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle
    (fun σ => (hw σ).measurable) hC0 hwC
  have e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas =
      M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas := fun σ => by
    have h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas := hint σ _ ((hw σ).mul (hρR σ).1)
    have h2 := hint σ _ (hw σ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext y; ring
  have e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas =
      M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas := fun σ => by
    haveI := hfm σ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]
    congr 1; funext y; ring
  simp only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢
  simp only [Fintype.card_fin] at hBs
  rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs] at hl1
  rw [← hIw, ← hW, ← hG', ← hV] at hl1
  set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA
  have eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M := by
    field_simp
    ring
  rw [eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M =
      C * (M / D.factorial * G' + M * ε * V - (r m : ℝ)) := by
    field_simp
  rw [eq2]
  exact hl1

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeriesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_shortSeries_eq_mul_adelicSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.OneMapExact.trace_short_eq | exact GlobalTheory.OneMapExact.trace_short_eq | (intros; apply GlobalTheory.OneMapExact.trace_short_eq <;> assumption)
end

