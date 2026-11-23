module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

open scoped DirectSum

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (n : ℕ)

theorem gsRoots_ρ_apply_of_mem (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (d : gsRoots S n) : (gsRoots S n).ρ g d = d := by
  have key : ∀ ζ : rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S),
      galRootsOfUnityHom K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n g ζ = ζ := by
    intro ζ
    apply Subtype.ext
    apply Units.ext
    show (((restrictRootsOfUnity g n ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S) = ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)
    rw [restrictRootsOfUnity_coe_apply]
    have hx : ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n _).1 ζ.2, Units.val_one]
    have hK : (((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ K.1 :=
      hμ _ (by rw [← IntermediateField.coe_pow, hx]; rfl)
    have hx' : ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) =
        algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟨_, hK⟩ := Subtype.ext rfl
    rw [hx']
    exact g.commutes _
  rw [galRootsOfUnity_ρ_apply, key]
  rfl

theorem nonempty_addEquiv_gsRoots [NeZero n] (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) :
    Nonempty (gsRoots S n ≃+ ZMod n) := by
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ n
  have hK : ζ₀ ∈ K.1 := hμ ζ₀ hζ₀.pow_eq_one
  set z : maxUnramifiedOutside K.1 ℚ̄ S := algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟨ζ₀, hK⟩
  have hz : IsPrimitiveRoot z n :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) (h := hζ₀)
      (maxUnramifiedOutside K.1 ℚ̄ S).val.injective
  have : HasEnoughRootsOfUnity (maxUnramifiedOutside K.1 ℚ̄ S) n := ⟨⟨z, hz⟩, inferInstance⟩
  have hcard : Nat.card (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) = Nat.card (Multiplicative (ZMod n)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  exact ⟨MulEquiv.toAdditive (mulEquivOfCyclicCardEq hcard)⟩

theorem sum_of_apply_of_injective {ι κ : Type*} [Fintype ι] [DecidableEq κ] {M : κ → Type*}
    [∀ k, AddCommGroup (M k)] (e : ι → κ) (he : Function.Injective e) (b : ∀ i, M (e i)) (i₀ : ι) :
    (∑ i, DirectSum.of M (e i) (b i)) (e i₀) = b i₀ := by
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i₀
    (fun i _ hi => DirectSum.of_eq_of_ne (e i) (e i₀) (b i) (fun h => hi (he h.symm)))
    (fun h => absurd (Finset.mem_univ i₀) h), DirectSum.of_eq_same]

theorem sum_of_apply_of_not_mem {ι κ : Type*} [Fintype ι] [DecidableEq κ] {M : κ → Type*}
    [∀ k, AddCommGroup (M k)] (e : ι → κ) (b : ∀ i, M (e i)) (k : κ) (hk : ∀ i, e i ≠ k) :
    (∑ i, DirectSum.of M (e i) (b i)) k = 0 := by
  rw [DFinsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => DirectSum.of_eq_of_ne (e i) k (b i) (hk i).symm

theorem sum_apply_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    {N : Type*} [AddCommGroup N] (f : ∀ i, M i →+ N) (i : ι) (m : M i) :
    ∑ j, f j (Pi.single i m j) = f i m := by
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

section General

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]

theorem localToCompact_globalToLocal_apply (φ : ∀ v, H v →ₜ* G) (A : Rep.{u} k G) [IsDiscreteRep A]
    [∀ v, IsDiscreteRep (Rep.res (φ v).toMonoidHom A)] (m : ℕ) (x : cohomology A m) :
    (localToCompact φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m).hom
      ((globalToLocal φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m).hom x) = 0 := by
  have hz := ConcreteCategory.congr_hom (globalToLocal_localToCompact φ A
    (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m) x
  rw [ConcreteCategory.comp_apply] at hz
  exact hz.trans rfl

end General

section Inv

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [NeZero n] [Fintype S]


set_option maxHeartbeats 1600000 in
theorem surjective_gsCompactInv [Nonempty S] (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Surjective (gsLocalInvRoots S ιs n v)) :
    Function.Surjective (gsCompactInv S ιs n hodd h3) := by
  classical
  intro a
  obtain ⟨v⟩ := ‹Nonempty S›
  obtain ⟨η, hη⟩ := ht v a
  refine ⟨(localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom (Pi.single v η), ?_⟩
  refine (gsCompactInv_localToCompact S ιs n hodd h3 _).trans ?_
  refine (gsSumInvRoots_apply S ιs n _).trans ?_
  exact (sum_apply_pi_single (fun w => gsLocalInvRoots S ιs n w) v η).trans hη


omit [Fintype S] in
abbrev gsLocalBrauerRoots (v : S) (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    localGaloisCohomology K 2 (.inr (v : HeightOneSpectrum (𝓞 K.1))) :=
  (cohomologyMap (rootsLocalMorZ S ιs n v) 2).hom (cohomologyULiftIntAddEquiv _ 2 z)

omit [Fintype S] [NeZero n] in
theorem placeInv_gsLocalBrauerRoots (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (gsLocalBrauerRoots S n ιs v z) =
      gsLocalInvRootsQZ S ιs n v z := by
  refine (placeInv_inr_apply _ _).trans (Eq.symm ?_)
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs n v) z).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine congrArg (brauerInvZOfIsSepClosure _ _) ?_
  exact AddMonoidHom.comp_apply _ _ _

omit [Fintype S] [NeZero n] in
theorem nsmul_gsLocalBrauerRoots (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    n • gsLocalBrauerRoots S n ιs v z = 0 := by
  have h : n • z = 0 := nsmul_cohomology_eq_zero (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (fun ζ => nsmul_gsRoots S n ζ) 2 z
  exact (map_nsmul _ n _).symm.trans ((congrArg _ ((map_nsmul _ n z).symm.trans
    ((congrArg _ h).trans (map_zero _)))).trans (map_zero _))


open Classical in
noncomputable def gsBrauerFamily
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    ⨁ w : Place K.1, localGaloisCohomology K 2 w :=
  ∑ v : S, DirectSum.of (fun w => localGaloisCohomology K 2 w) (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (gsLocalBrauerRoots S n ιs v (ξ v))

omit [NeZero n] [Fintype S] in
theorem injective_inr_val : Function.Injective fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1) :=
  fun _ _ h => Subtype.ext (Sum.inr_injective h)

open Classical in
omit [NeZero n] in
theorem gsBrauerFamily_inr (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2)
    (v : S) : gsBrauerFamily S n ιs ξ (.inr (v : HeightOneSpectrum (𝓞 K.1))) = gsLocalBrauerRoots S n ιs v (ξ v) :=
  sum_of_apply_of_injective (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)) (injective_inr_val S)
    (fun v => gsLocalBrauerRoots S n ιs v (ξ v)) v

open Classical in
omit [NeZero n] in
theorem gsBrauerFamily_inr_of_not_mem
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2)
    (w : HeightOneSpectrum (𝓞 K.1)) (hw : w ∉ S) : gsBrauerFamily S n ιs ξ (.inr w) = 0 :=
  sum_of_apply_of_not_mem (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1))
    (fun v => gsLocalBrauerRoots S n ιs v (ξ v)) _ (fun v h => hw (Sum.inr_injective h ▸ v.2))

omit [NeZero n] in
theorem nsmul_gsBrauerFamily (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    n • gsBrauerFamily S n ιs ξ = 0 := by
  rw [gsBrauerFamily, Finset.smul_sum]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← map_nsmul, nsmul_gsLocalBrauerRoots, map_zero]

theorem sumPlaceInv_gsBrauerFamily
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    sumPlaceInv K (gsBrauerFamily S n ιs ξ) = zmodToQZ n (∑ v, gsLocalInvRoots S ιs n v (ξ v)) := by
  refine (map_sum (sumPlaceInv K) _ _).trans ((Finset.sum_congr rfl fun v _ => ?_).trans
    (map_sum (zmodToQZ n) _ _).symm)
  exact (sumPlaceInv_of _ _).trans
    ((placeInv_gsLocalBrauerRoots S n ιs v (ξ v)).trans (zmodToQZ_gsLocalInvRoots S ιs n v (ξ v)).symm)


omit [NeZero n] [Fintype S] in
theorem placeInv_brauerLocal_sUnitsBrauer (v : S) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        (brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) (.inr (v : HeightOneSpectrum (𝓞 K.1)))) =
      brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ((gsLocalRes S (ιs v) 2).hom
          (cohomologyULiftIntAddEquiv _ 2
            ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1))))) (sUnitsBrauer_apply K S y)).trans ?_
  refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
    (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
  refine (placeInv_inr_apply _ _).trans ?_
  simp only [gsLocalEmbeddings_fin]


omit [NeZero n] [Fintype S] in
theorem exists_sUnits_of_mem_localPrimaryKernel (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (β : ⨁ w : Place K.1, localGaloisCohomology K 2 w) (hβ : β ∈ localPrimaryKernel K S ℓ) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2, (∃ j : ℕ, ℓ ^ j • y = 0) ∧
      brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) = β := by
  let ι := gsLocalEmbeddings S ιs
  obtain ⟨⟨k, hk⟩, hloc, hsum⟩ := hβ
  obtain ⟨b, hb⟩ := (sumPlaceInv_eq_zero_iff ι β).mp hsum
  have hbk : ℓ ^ k • b = 0 := by
    apply brauerLocal_injective ι
    rw [map_nsmul, hb, hk, map_zero]
  obtain ⟨z, hz⟩ := exists_gsBrauerInfl_eq K S ℓ hℓ hS b k hbk
  let e := cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2
  let x := e.symm z
  have hex : e x = z := e.apply_symm_apply z
  have hxk : ℓ ^ k • x = 0 := by
    apply e.injective
    apply gsBrauerInfl_injective K S
    rw [map_nsmul, hex, map_nsmul, hz, hbk, map_zero, map_zero]
  let E := sUnitsQuotSequence K.1 ℚ̄ S
  let P := picSequence K S ι
  have hP : P.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2
      (sUnitsQuotDiv_injective K S ι)) ((Rep.epi_iff_surjective _).2 (picQuot_surjective K S ι))
    apply shortComplex_exact_of_forall_exists
    intro f hf
    obtain ⟨p, hp⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
    exact ⟨p, hp⟩
  let p := (cohomologyMap E.g 2).hom x
  have hp : (cohomologyMap P.f 2).hom p = 0 := by
    have hcomp : E.g ≫ P.f = unitsDiv K S ι := sUnitsQuotSequence_g_comp_sUnitsQuotDiv K S ι
    refine (cohomologyMap_comp_hom_apply E.g P.f 2 x).symm.trans ?_
    rw [hcomp]
    apply eq_zero_of_divFunEval_eq_zero (gsDecomp K S ι) (continuous_gsDecomp K S ι)
    intro v
    have hm : (Rep.resFunctor (gsDecomp K S ι v)).map (unitsDiv K S ι) ≫
        divFunEval (gsDecomp K S ι) ℤ v = ordEmbMor S (ι.fin v.1) v.2 := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      exact (divFunEval_unitsDiv K S ι v a).trans (ordEmbMor_hom_apply S (ι.fin v.1) v.2 a).symm
    refine (cohomologyMapAlong_cohomologyMap_apply (gsDecomp K S ι v) (continuous_gsDecomp K S ι v)
      (unitsDiv K S ι) (divFunEval (gsDecomp K S ι) ℤ v) 2 x).trans ?_
    refine (congrArg (fun m => (cohomologyMapAlong (gsDecomp K S ι v)
      (continuous_gsDecomp K S ι v) m 2).hom x) hm).trans ?_
    apply (gsLocalRes_eq_zero_iff S (ι.fin v.1) v.2 x).1
    refine (congrArg (gsLocalRes S (ι.fin v.1) 2).hom hex).trans
      ((brauerLocal_gsBrauerInfl_inr K S ι v.1 z).symm.trans ?_)
    exact (congrArg (fun t => brauerLocal ι t (.inr v.1)) hz).trans
      ((congrArg (fun t => t (.inr v.1)) hb).trans (hloc v.1 v.2))
  have hp0 : p = 0 := by
    apply eq_zero_of_mem_range_δ_of_coprime hP 1 2 rfl (exists_δ_eq_of_cohomologyMap_f_eq_zero hP 1 2 rfl p hp) ℓ
      (fun a => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ι) ℓ
        (exists_coprime_smul_picInfRep K S ι ℓ hℓ hS) 1 a) k
    exact (map_nsmul (cohomologyMap E.g 2).hom (ℓ ^ k) x).symm.trans
      ((congrArg (cohomologyMap E.g 2).hom hxk).trans (map_zero _))
  obtain ⟨y, hy⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero
    (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 2 x hp0
  have hyb : sUnitsBrauer K S y = b :=
    (sUnitsBrauer_apply K S y).trans
      ((congrArg (gsBrauerInfl K S 2).hom ((congrArg e hy).trans hex)).trans hz)
  have hyk : ℓ ^ k • sUnitsBrauer K S y = 0 :=
    (congrArg (fun t => ℓ ^ k • t) hyb).trans hbk
  obtain ⟨y', hj, hy'⟩ := exists_primary_map_eq (sUnitsBrauer K S) hℓ
    (isTorsion_cohomology (galSUnitsMax K.1 ℚ̄ S) (by norm_num) y) hyk
  exact ⟨y', hj, (congrArg (brauerLocal ι) (hy'.trans hyb)).trans hb⟩


set_option maxHeartbeats 4000000 in
theorem injective_gsCompactInv (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Injective (gsLocalInvRoots S ιs n v)) :
    Function.Injective (gsCompactInv S ιs n hodd h3) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz0
  refine Exists.elim (localToCompact_two_surjective S ιs n h3 z) (fun ξ hξ => ?_)
  subst hξ
  have hsum : ∑ v, gsLocalInvRoots S ιs n v (ξ v) = 0 :=
    (gsSumInvRoots_apply S ιs n ξ).symm.trans ((gsCompactInv_localToCompact S ιs n hodd h3 ξ).symm.trans hz0)
  have hmem : gsBrauerFamily S n ιs ξ ∈ localPrimaryKernel K S ℓ :=
    ⟨⟨k, hnk ▸ nsmul_gsBrauerFamily S n ιs ξ⟩, gsBrauerFamily_inr_of_not_mem S n ιs ξ,
      (sumPlaceInv_gsBrauerFamily S n ιs ξ).trans (by rw [hsum, map_zero])⟩

  refine Exists.elim (exists_sUnits_of_mem_localPrimaryKernel S ιs ℓ hℓ hS _ hmem) (fun y hy => ?_)
  refine Exists.elim hy.1 (fun j hj => ?_)
  have hyβ' := hy.2
  have hny : n • y = 0 := by
    let ι := gsLocalEmbeddings S ιs
    let E := sUnitsQuotSequence K.1 ℚ̄ S
    let P := picSequence K S ι
    have hP : P.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2
        (sUnitsQuotDiv_injective K S ι)) ((Rep.epi_iff_surjective _).2 (picQuot_surjective K S ι))
      apply shortComplex_exact_of_forall_exists
      intro f hf
      obtain ⟨p, hp⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
      exact ⟨p, hp⟩
    have hb : sUnitsBrauer K S (n • y) = 0 := by
      apply brauerLocal_injective ι
      rw [map_nsmul, map_nsmul, hyβ', nsmul_gsBrauerFamily, map_zero]
    let e := cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2
    have hf : (cohomologyMap E.f 2).hom (n • y) = 0 := by
      apply e.injective
      apply gsBrauerInfl_injective K S
      calc
        _ = sUnitsBrauer K S (n • y) := (sUnitsBrauer_apply K S (n • y)).symm
        _ = 0 := hb
        _ = _ := (map_zero (gsBrauerInfl K S 2).hom).symm.trans
          (congrArg (gsBrauerInfl K S 2).hom (map_zero e).symm)
    obtain ⟨p, hp⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero
      (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 1 2 rfl (n • y) hf
    have hnj : ℓ ^ j • (n • y) = 0 := by rw [smul_comm, hj, smul_zero]
    have hpk : ℓ ^ j • p = 0 := by
      obtain ⟨z, hz⟩ := exists_cohomologyMap_g_eq_of_δ_eq_zero
        (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 1 2 rfl (ℓ ^ j • p) (by
          rw [map_nsmul, hp]
          exact hnj)
      have : Subsingleton (cohomology E.X₂ 1) := subsingleton_cohomology_one_galUnits
      rw [← hz, Subsingleton.elim z 0, map_zero]
    have : Subsingleton (cohomology P.X₂ 1) :=
      ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_divFunRep_int (gsDecomp K S ι))
    have hp0 : (p : cohomology P.X₁ 1) = 0 :=
      eq_zero_of_mem_range_δ_of_coprime hP 0 1 rfl
        (exists_δ_eq_of_cohomologyMap_f_eq_zero hP 0 1 rfl p (Subsingleton.elim _ _)) ℓ
        (fun a => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ι) ℓ
          (exists_coprime_smul_picInfRep K S ι ℓ hℓ hS) 0 a) j hpk
    exact hp.symm.trans ((congrArg (δ (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 1 2 rfl).hom hp0).trans
      (map_zero _))

  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv hn => by
    subst hnk
    rw [Nat.cast_pow] at hn
    exact hv (hS v (v.isPrime.mem_of_pow_mem k hn))
  refine Exists.elim (exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero
    (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S n hnS) 2 y
    ((cohomologyMap_nsmul_id_apply _ n 2 y).trans hny)) (fun x hx => ?_)

  have hres : ∀ v, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom x =
      ξ v := by
    intro v
    apply ht v
    apply zmodToQZ_injective
    refine (zmodToQZ_gsLocalInvRoots S ιs n v _).trans ?_
    refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs n v) _).trans ?_
    refine (AddMonoidHom.comp_apply _ _ _).trans ?_
    have hlocal := cohomologyMap_uliftInt_cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n)
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (rootsLocalMorZ S ιs n v)
      (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x
    refine (congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      ((AddMonoidHom.comp_apply _ _ _).trans hlocal)).trans ?_
    refine Eq.trans ?_ ((placeInv_gsLocalBrauerRoots S n ιs v (ξ v)).trans (zmodToQZ_gsLocalInvRoots S ιs n v (ξ v)).symm)
    refine Eq.trans ?_ (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
      (gsBrauerFamily_inr S n ιs ξ v))
    refine Eq.trans ?_ (congrArg (fun β : ⨁ w : Place K.1, localGaloisCohomology K 2 w =>
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))) (β (.inr (v : HeightOneSpectrum (𝓞 K.1))))) hyβ')
    refine Eq.trans ?_ (placeInv_brauerLocal_sUnitsBrauer S ιs v y).symm
    rw [← hx]
    rfl
  have hg : (globalToLocal (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom x = ξ := funext hres
  exact hg ▸ localToCompact_globalToLocal_apply (gsFinFamily S ιs) (gsRoots S n) 2 x

theorem bijective_gsCompactInv [Nonempty S] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Bijective (gsLocalInvRoots S ιs n v)) :
    Function.Bijective (gsCompactInv S ιs n hodd h3) :=
  ⟨injective_gsCompactInv S n ιs ℓ k hℓ hnk hS hodd h3 fun v => (ht v).1,
    surjective_gsCompactInv S n ιs hodd h3 fun v => (ht v).2⟩

theorem bijective_gsCompactInv_of_mem [Nonempty S] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3)) :
    Function.Bijective (gsCompactInv S ιs n hodd h3) :=
  bijective_gsCompactInv S n ιs ℓ k hℓ hnk hS hodd h3 (bijective_gsLocalInvRoots S ιs n hμ)

end Inv

end

end GroundTheory.ProfCoh
