module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem spMap_injective_divisor {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_ext_Bt {S : Type} [CommRing S] {α β : Bt P' x0 hu →+* S}
    (h1 : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)))
    (h2 : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu)) : α = β := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    have e : (o ⊗ₜ[Localization.Away P'.f] b : Bt P' x0 hu) =
        algebraMap O (Bt P' x0 hu) (show O from o) * inB P' x0 hu b := by
      change _ = (o ⊗ₜ[Localization.Away P'.f] (1 : P'.B)) * ((1 : OL P' x0 hu) ⊗ₜ b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rw [e, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun h1 (show O from o)) (RingHom.congr_fun h2 b)
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

theorem aH_cancel_aff (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {S : Type} [CommRing S]
    (α β : Bt P' x0 hu →+* S)
    (h : spMap α ≫ (aH P' x0 hu hπ).left = spMap β ≫ (aH P' x0 hu hπ).left) : α = β := by
  have hO : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)) := by
    have e := congrArg (· ≫ G'.hom) h
    simp only [Category.assoc, Over.w (aH P' x0 hu hπ)] at e
    apply spMap_injective_divisor
    exact (GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) α).symm.trans (e.trans (GlobalTheory.HTMap.spc _ β))
  have hB : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu) := by
    have e := congrArg (· ≫ π) h
    simp only [Category.assoc, aH_left_π] at e
    have e2 : spMap (α.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (β.comp (inB P' x0 hu)) ≫ P'.u.left :=
      (GlobalTheory.HTMap.spc_assoc _ _ _).symm.trans (e.trans (GlobalTheory.HTMap.spc_assoc _ _ _))
    refine P'.fin.mono S _ _ (GlobalTheory.HTMap.FP.alg_ext ?_) e2
    change α.comp ((inB P' x0 hu).comp P'.str) = β.comp ((inB P' x0 hu).comp P'.str)
    rw [inB_str, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hO]
  exact ringHom_ext_Bt P' x0 hu hO hB

theorem aH_left_mono (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Mono (aH P' x0 hu hπ).left := by
  constructor
  intro T g h e
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => ?_
  have ea := Spec.map_preimage (T.affineCover.f i ≫ g)
  have eb := Spec.map_preimage (T.affineCover.f i ≫ h)
  have key := aH_cancel_aff P' x0 hu hπ (Spec.preimage (T.affineCover.f i ≫ g)).hom
    (Spec.preimage (T.affineCover.f i ≫ h)).hom (by
      change Spec.map (Spec.preimage (T.affineCover.f i ≫ g)) ≫ _ = Spec.map (Spec.preimage (T.affineCover.f i ≫ h)) ≫ _
      rw [ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (T.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))
  exact ea.symm.trans ((congrArg Spec.map (CommRingCat.hom_ext key)).trans eb)

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocusPull

theorem exists_gen_of_nonzeroLocus_eq_top {Y : Scheme.{0}} {M : LB Y} (s : M.Sec) (h : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤) :
    ∃ t : LB.Gen M, t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have hy' : y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := h ▸ trivial
      exact (Y.mem_basicOpen _ y hy).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen s hy).1 hy')
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem isLocus_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V) :
    IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V) := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  exact ⟨_, pull_isLB hL f, GlobalTheory.secPull s f, rfl, GlobalTheory.nonzeroLocus_secPull s f⟩

theorem pull_eq_zero_of_isLocus {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V)
    (hf : ∀ y, f y ∈ V) : GlobalTheory.CechPic.pull f c = 0 := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  have htop : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s f) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact top_unique fun y _ => hf y
  exact (cls_eq_zero_iff (pull_isLB hL f)).2 (exists_gen_of_nonzeroLocus_eq_top _ htop)

theorem locus_pull :
    (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) :=
  ⟨fun _ _ f _ _ h => isLocus_pull f h, fun _ _ f _ _ h hf => pull_eq_zero_of_isLocus f h hf⟩

end GlobalTheory.LocusPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtension
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_eq gs_mul gs_pull gs_res gs_compat mem_pull chartPullOut chartPullUnpull)

theorem ker_descend {k K : Type} [Field k] [Field K] [Algebra k K] {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) k) (v : Fin a → K) (hv : (D.map (algebraMap k K)).mulVec v = 0) :
    ∃ (r : ℕ) (e : Fin r → K) (u : Fin r → Fin a → k), (∀ l, D.mulVec (u l) = 0) ∧
      ∀ j, v j = ∑ l, e l * algebraMap k K (u l j) := by
  classical
  let V := Submodule.span k (Set.range v)
  haveI : Module.Finite k V := FiniteDimensional.span_of_finite k (Set.finite_range v)
  let bV := Module.finBasis k V
  have hv' : ∀ j, v j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hli : LinearIndependent k (fun l => (bV l : K)) :=
    bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank k V) → Fin a → k, ∀ j, v j = ∑ l, c l j • (bV l : K) :=
    ⟨fun l j => bV.repr ⟨v j, hv' j⟩ l, fun j => by
      have := congrArg Subtype.val (bV.sum_repr ⟨v j, hv' j⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm⟩
  refine ⟨_, fun l => (bV l : K), c, fun l => ?_, fun j => ?_⟩
  · funext p
    have hp := congrFun hv p
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, hc, Finset.mul_sum] at hp
    rw [Finset.sum_comm] at hp
    have : ∑ l, (∑ j, D p j * c l j) • (bV l : K) = 0 := by
      rw [← hp]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    exact Fintype.linearIndependent_iff.1 hli _ this l
  · rw [hc j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, mul_comm]

theorem mem_nonzeroLocus_iff_isUnit {X Z : Scheme.{0}} {N : LB X} (s : LB.Sec N) (r : Z ⟶ X) (z : Z) {j : N.ι}
    (hj : r z ∈ N.U j) : r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f j)) := by
  have key : ∀ {j : N.ι} (hj : r z ∈ N.U j), IsUnit (gs r z _ (s.f j)) ↔ r z ∈ X.basicOpen (s.f j) := by
    intro j hj
    rw [gs_eq r z _ hj]
    refine ((Z.mem_basicOpen ((r.app _).hom (s.f j)) z hj).symm).trans ?_
    rw [← Scheme.Hom.preimage_basicOpen]
    rfl
  rw [key hj]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨j, h⟩⟩
  obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hm : r z ∈ N.U j' := X.basicOpen_le _ hj'
  rw [← key hj, gs_compat s r z hj hm]
  exact (Units.isUnit _).mul ((key hm).2 hj')

theorem linComb_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem exists_sec_of_baseChange : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ K _ _ t c hK y
  classical
  let ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Over.mk t
  let h : Over.mk (ιK ≫ t) ⟶ T := Over.homMk ιK rfl
  rw [← linComb_whisker P.A P.L 2 h c] at hK
  let M : LB (T ⊗ P.A).left := twistLB P.A P.L 2 c
  have hM : M.IsLB := LB.isLB_linComb P.isLB _ _
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of k) := (fst T P.A).left
  let π := (h ▷ P.A).left
  let f' : (Over.mk (ιK ≫ t) ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk (ιK ≫ t)) P.A).left
  have H : IsPullback π f' f ιK := GlobalTheory.AbLaw.SecBC.isPullback_whisker P.A h
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_snd P.A T
  haveI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb P.isAb.proper
  haveI : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hpb P.isAb.smooth
  haveI : Flat f := inferInstance
  obtain ⟨Q⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f hM
  haveI hι : Surjective ιK := ⟨fun p => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have hπ : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip hι
  obtain ⟨z, rfl⟩ := hπ.surj y
  by_contra hy
  push Not at hy
  obtain ⟨sK, hsK⟩ := hK z
  obtain ⟨i, hi⟩ := GlobalTheory.SecTwist.perf_cover Q (π z)
  have m₁ : π z ∈ M.U (Q.ch i) := Q.le i hi
  have m₂ : z ∈ (LB.LinComb P.L (K := Fin 2) (fun k => π ≫ ![(snd T P.A).left, (translPt P.A c).left] k)
      ![((2 : ℕ) : ℤ) - 1, 1]).U (Q.ch i) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k
  let sb : LB.Sec (M.pull π) := GlobalTheory.SecTwist.pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK
  obtain ⟨E, hE⟩ := GlobalTheory.SecTwist.perf_sec Q (algebraMap k K) H
  have hu1 : IsUnit (gs (𝟙 _) z ((M.pull π).U (fun _ => Q.ch i)) (sb.f (fun _ => Q.ch i))) := by
    have a₁ := GlobalTheory.SecTwist.gs_pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK (𝟙 _) z (fun _ => Q.ch i)
      (mem_pull.2 m₁)
    rw [Category.id_comp] at a₁
    refine a₁ ▸ (mem_nonzeroLocus_iff_isUnit sK (𝟙 _) z m₂).1 hsK
  obtain ⟨r, e, u, hu, hvu⟩ := ker_descend Q.D₀ (E.symm sb).1 (E.symm sb).2
  have h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.SecTwist.perf_sec Q (RingHom.id k) h₀
  have ker : ∀ l, (Q.D₀.map (RingHom.id k)).mulVec (u l) = 0 := fun l => by
    rw [show Q.D₀.map (RingHom.id k) = Q.D₀ from rfl]
    exact hu l
  let s : Fin r → LB.Sec M := fun l => GlobalTheory.SecTwist.pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩)
  have hG : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) =
      ∑ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z (u l j) * gs π z (Q.W i) (Q.u j i) := fun l => by
    have a₃ := GlobalTheory.SecTwist.gs_pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩) π z (Q.ch i) m₁
    have a₄ := hE₀ ⟨u l, ker l⟩ i _ π z hi
    rw [Category.comp_id] at a₃ a₄
    exact a₃.trans a₄
  have hnu : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _ := fun l => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← mem_nonzeroLocus_iff_isUnit (s l) π z m₁]
    exact hy (s l)
  have e1 : ∀ a : k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (algebraMap k K a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z a :=
    fun a => by
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp]
      congr 1
      exact H.w.symm
  have hsb := hE (E.symm sb) i _ (𝟙 _) z hi
  rw [Equiv.apply_symm_apply] at hsb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Category.id_comp, hvu, ← GlobalTheory.SecTwist.cstHom_apply, map_sum, map_mul] at hsb
  simp only [GlobalTheory.SecTwist.cstHom_apply, e1] at hsb
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hu1
  rw [hsb]
  have key : ∀ l, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (e l) * gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈
      IsLocalRing.maximalIdeal _ := fun l => Ideal.mul_mem_left _ _ (hnu l)
  have := Ideal.sum_mem (IsLocalRing.maximalIdeal _) fun l (_ : l ∈ Finset.univ) => key l
  simp only [hG, Finset.mul_sum] at this
  rw [Finset.sum_comm] at this
  convert this using 2 with j
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TwistDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRow3

theorem oneFormMapRow_threeLevel_of_characterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O ph hn hC hE hFW hIo i hP hT
  obtain ⟨hcore, hoff, hused⟩ := _root_.GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 T.Q.c.F R F hC hE
  exact _root_.GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O ph hn hcore hoff hused hFW hIo i hP hT

end GlobalTheory.OneMapRow3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionClassifyingFamilyChart
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RepChart

theorem repChart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A B S' U _ b P M hP hM φ hφb hsame hopen T t N hN
  have hP' := hP.fam.isLB
  have hM' := hM.isLB
  have hN' := hN.isLB
  obtain ⟨x, ⟨hxb, hxN⟩, -⟩ := hP.univ T t N hN
  have ex : cls N hN' = evc hP' (fst A T) (snd A T ≫ x) := (cls_eq_iff hN' (pull_isLB hP' _)).2 hxN
  have eφ : evc hM' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ fst U S') = evc hP' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ φ) :=
    (same_iff hM' hP' _ _).1 hsame
  have eY : ∀ (Y : Over S) (y : Y ⟶ T), evc hN' (fst A Y) (snd A Y ≫ y) = evc hP' (fst A Y) (snd A Y ≫ y ≫ x) := by
    intro Y y
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) ex
    rw [pull_evc, lift_fst, lift_snd_assoc] at e
    exact e
  have eV : ∀ (Y : Over S) (v : Y ⟶ U ⊗ S'), evc hM' (fst A Y) (snd A Y ≫ v ≫ fst U S') =
      evc hP' (fst A Y) (snd A Y ≫ v ≫ φ) := by
    intro Y v
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ v)).left) eφ
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    exact e
  have uniq : ∀ (Y : Over S) (y : Y ⟶ T) (x₁ x₂ : Y ⟶ B), x₁ ≫ b = y ≫ t → x₂ ≫ b = y ≫ t →
      evc hP' (fst A Y) (snd A Y ≫ x₁) = evc hN' (fst A Y) (snd A Y ≫ y) →
      evc hP' (fst A Y) (snd A Y ≫ x₂) = evc hN' (fst A Y) (snd A Y ≫ y) → x₁ = x₂ := by
    intro Y y x₁ x₂ h₁ h₂ e₁ e₂
    have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN' _
    have hF : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
      refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' z ↦ ?_⟩
      simp only [evc_ev hN', lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hN').1 hN.add Z a a' (z ≫ y)
    refine (hP.univ Y (y ≫ t) _ hF).unique ⟨h₁, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
      ⟨h₂, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
    · rw [cls_ev hN', cls_ev hP', e₁]
    · rw [cls_ev hN', cls_ev hP', e₂]
  refine ⟨x.left ⁻¹ᵁ φ.left.opensRange, fun Y y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu⟩
    rw [same_iff hN' hM'] at hu
    let v : Y ⟶ U ⊗ S' := lift u (y ≫ t)
    have hvx : v ≫ φ = y ≫ x := by
      refine uniq Y y _ _ ?_ ?_ ?_ (by rw [eY])
      · rw [Category.assoc, hφb, lift_snd]
      · rw [Category.assoc, hxb]
      · rw [← eV, lift_fst, hu]
    intro z
    have e := congrArg (fun q : Y ⟶ B ↦ q.left z) hvx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    exact ⟨_, e⟩
  · intro h
    have hr : Set.range (y.left ≫ x.left) ⊆ Set.range φ.left := by
      rintro _ ⟨z, rfl⟩
      have := h z
      simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at this
      simpa [Scheme.Hom.comp_apply] using this
    let l := IsOpenImmersion.lift φ.left (y.left ≫ x.left) hr
    have hl : l ≫ φ.left = y.left ≫ x.left := IsOpenImmersion.lift_fac _ _ _
    let v : Y ⟶ U ⊗ S' := Over.homMk l (by
      rw [← Over.w φ, ← Category.assoc, hl, Category.assoc, Over.w x, Over.w y])
    have hvx : v ≫ φ = y ≫ x := Over.OverMorphism.ext (by simpa [v] using hl)
    refine ⟨v ≫ fst U S', (same_iff hN' hM' _ _).2 ?_⟩
    rw [eV, hvx, eY]

end GlobalTheory.RepChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (exact GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (intros; apply GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_unique_of_iso_grp : ∀ (S : Scheme.{0}), Nonempty S → ∀ (X Y : Over S) [GrpObj X] (f : X ⟶ Y), IsIso f → ∀ g g' : ℕ, SmoothOfRelativeDimension g X.hom → SmoothOfRelativeDimension g' Y.hom → g = g' := by
  intro S hS X Y _ f hf g g' hg hg'
  obtain ⟨s⟩ := hS
  have : IsIso f.left := (Over.forget S).map_isIso f
  have sq : CommSq f.left X.hom Y.hom (𝟙 S) := ⟨by rw [Over.w f, Category.comp_id]⟩
  have h2 : SmoothOfRelativeDimension g' X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback (IsPullback.of_horiz_isIso sq) hg'
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique X.hom hg h2 ((η[X]).left s)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanVal.value_tangent | exact GlobalTheory.MBLow.TanVal.value_tangent | (intros; apply GlobalTheory.MBLow.TanVal.value_tangent <;> assumption)
end

