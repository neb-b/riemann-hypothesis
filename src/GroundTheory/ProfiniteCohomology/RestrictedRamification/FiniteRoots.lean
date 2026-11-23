module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicFinite
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
public import GroundTheory.GlobalFields.SUnits
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section General

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)


include hnS in
theorem finite_cohomology_one_rootsOfUnity [Finite S] :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1) := by
  refine (AddMonoidHom.finite_iff_finite_ker_range (kummerPicHom (Ω := Ω) S n)).2 ⟨?_, inferInstance⟩
  let k := kummerSUnitsHom (Ω := Ω) S n hnS
  have : Module.Finite ℤ (Additive (S.unit F)) := inferInstance
  have : AddGroup.FG (Additive (S.unit F)) := Module.Finite.iff_addGroup_fg.1 this
  have : AddGroup.FG k.range := AddGroup.fg_of_surjective k.rangeRestrict_surjective
  have htor : IsAddTorsion k.range := by
    rintro ⟨_, a, rfl⟩
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), ?_⟩
    apply Subtype.ext
    change n • k a = 0
    rw [← map_nsmul]
    exact (kummerSUnitsHom_eq_zero_iff (Ω := Ω) S n hnS _).2 ⟨a, rfl⟩
  have : Finite k.range := AddCommGroup.finite_of_fg_isAddTorsion _ htor
  refine Finite.of_injective (β := k.range) (fun y => ⟨y.1, ?_⟩) ?_
  · exact (kummerPicHom_eq_zero_iff (Ω := Ω) S n hnS y.1).1 y.2
  · intro y z h
    simp only at h
    exact Subtype.ext (Subtype.mk.inj h)


include hnS in
theorem finite_cohomology_two_rootsOfUnity_of_finite
    (hfin : {y : cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 2 | n • y = 0}.Finite) :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 2) := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  let f := (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 2).hom.toAddMonoidHom
  refine (AddMonoidHom.finite_iff_finite_ker_range f).2 ⟨?_, ?_⟩
  · have : Finite (cohomology (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ 1) :=
      Finite.of_injective _ (h1SUnitsToSPic_injective (Ω := Ω) S)
    let d := (δ hK 1 2 rfl).hom.toAddMonoidHom
    have : Finite d.range := Set.finite_coe_iff.2 (Set.finite_range d)
    refine Finite.of_injective (β := d.range) (fun y => ⟨y.1, ?_⟩) ?_
    · obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 1 2 rfl) y.1 y.2
      exact ⟨z, hz⟩
    · intro y z h
      simp only at h
      exact Subtype.ext (Subtype.mk.inj h)
  · show Finite (SetLike.coe f.range)
    refine (hfin.subset ?_).to_subtype
    rintro _ ⟨x, rfl⟩
    have h1 := cohomologyMap_g_cohomologyMap_f_apply
      (S := sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n) 2 x
    have hg : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).g 2).hom (f x) =
        n • f x :=
      cohomologyMap_nsmul_id_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n 2 (f x)
    exact hg.symm.trans h1

end General

section Brauer

open GroundTheory.Global FiniteSubfield DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem mem_of_dvd_of_mem {d n : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  obtain ⟨c, hc⟩ := hd
  refine hS v ?_
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hv

theorem eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : n • y = 0) (hy' : sUnitsBrauer K S y = 0) :
    y = 0 := by
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    simpa using hy
  have hℓ : n.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hℓ.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn0 (hn.trans (mul_zero _))
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn
    exact hm (hn ▸ Nat.minFac_dvd n)
  have hmy : m • y = 0 := by
    have ht : n.minFac ^ a • (m • y) = 0 := by rw [smul_smul, ← hn, hy]
    have hb : sUnitsBrauer K S (m • y) = 0 := by rw [map_nsmul, hy', nsmul_zero]
    have hmap : (cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).f 2).hom (m • y) = 0 := by
      rw [sUnitsBrauer_apply] at hb
      have hf := gsBrauerInfl_injective K S (hb.trans (map_zero _).symm)
      exact (cohomologyULiftIntAddEquiv _ 2).injective (hf.trans (map_zero _).symm)
    have hE := sUnitsQuotSequence_shortExact K.1 ℚ̄ S
    obtain ⟨p, hp⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hE 1 2 rfl (m • y) hmap
    have hpt : n.minFac ^ a • p = 0 := by
      obtain ⟨z, hz⟩ := exists_cohomologyMap_g_eq_of_δ_eq_zero hE 1 2 rfl (n.minFac ^ a • p)
        (by
          rw [map_nsmul, hp]
          exact ht)
      have : Subsingleton (cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ 1) :=
        subsingleton_cohomology_one_galUnits
      rw [← hz, Subsingleton.elim z 0, map_zero]
    obtain ⟨ιs⟩ := nonempty_localEmbeddings K
    have : CompactSpace (galUnramifiedOutside K.1 ℚ̄ S) :=
      (galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S).1
    have : TotallyDisconnectedSpace (galUnramifiedOutside K.1 ℚ̄ S) :=
      (galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S).2.2
    have : IsDiscreteRep (picSequence K S ιs).X₁ :=
      inferInstanceAs (IsDiscreteRep (sUnitsQuotSequence K.1 ℚ̄ S).X₃)
    have : IsDiscreteRep (picSequence K S ιs).X₂ :=
      inferInstanceAs (IsDiscreteRep (gsDiv K S ιs ℤ))
    have : IsDiscreteRep (picSequence K S ιs).X₃ :=
      inferInstanceAs (IsDiscreteRep (picInfRep K S ιs))
    have hP : (picSequence K S ιs).ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · apply shortComplex_exact_of_forall_exists
        intro f hf
        obtain ⟨q, hq⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
        exact ⟨q, hq⟩
      · exact (Rep.mono_iff_injective _).2 (sUnitsQuotDiv_injective K S ιs)
      · exact (Rep.epi_iff_surjective _).2 (picQuot_surjective K S ιs)
    have hD : Subsingleton (cohomology (picSequence K S ιs).X₂ 1) :=
      ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_divFunRep_int (gsDecomp K S ιs))
    obtain ⟨q, hq⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hP 0 1 rfl
      (p : cohomology (picSequence K S ιs).X₁ 1) (Subsingleton.elim _ _)
    have hp0 : p = 0 :=
      eq_zero_of_mem_range_δ_of_coprime hP 0 1 rfl ⟨q, hq⟩ n.minFac
        (fun z => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) n.minFac
          (exists_coprime_smul_picInfRep K S ιs n.minFac hℓ
            (mem_of_dvd_of_mem K S (Nat.minFac_dvd _) hS)) 0 z) a hpt
    exact hp.symm.trans ((congrArg (δ hE 1 2 rfl).hom hp0).trans (map_zero _))
  have hlt : m < n := by
    have h2 : 1 < n.minFac ^ a := Nat.one_lt_pow ha hℓ.one_lt
    rw [hn]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) h2
  exact ih m hlt hm0 (mem_of_dvd_of_mem K S ⟨n.minFac ^ a, hn.trans (mul_comm _ _)⟩ hS) y hmy hy'

theorem finite_nsmul_eq_zero_sUnits_two [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}.Finite := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let T : Set QZ := {u | n • u = 0}
  have : Finite T := (AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hn0)).to_subtype
  let t := (brauerLocal ιs).comp (sUnitsBrauer K S)
  have ht : ∀ y : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}, ∀ v : Place K.1,
      placeInv v (t y.1 v) ∈ T := by
    intro y v
    change n • placeInv v (t y.1 v) = 0
    have e : (n • t y.1) v = n • (t y.1 v) := map_nsmul (DFinsupp.evalAddMonoidHom v) n (t y.1)
    rw [← map_nsmul, ← e, ← map_nsmul t, y.2, map_zero, DFinsupp.zero_apply, map_zero]
  let Φ : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0} →
      (InfinitePlace K.1 → T) × (S → T) := fun y =>
    (fun w => ⟨placeInv (.inl w) (t y.1 (.inl w)), ht y _⟩,
      fun w => ⟨placeInv (.inr w.1) (t y.1 (.inr w.1)), ht y _⟩)
  refine Set.finite_coe_iff.1 (Finite.of_injective Φ fun y z h => ?_)
  have htyz : t y.1 = t z.1 := by
    ext v
    rcases v with w | w
    · exact placeInv_injective (.inl w) (congrArg Subtype.val (congrFun (congrArg Prod.fst h) w))
    · by_cases hw : w ∈ S
      · exact placeInv_injective (.inr w)
          (congrArg Subtype.val (congrFun (congrArg Prod.snd h) ⟨w, hw⟩))
      · have hzero (x : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
            t x (.inr w) = 0 := by
          change brauerLocal ιs (sUnitsBrauer K S x) (.inr w) = 0
          rw [sUnitsBrauer_apply, brauerLocal_gsBrauerInfl_inr]
          apply (gsLocalRes_eq_zero_iff S (ιs.fin w) hw _).2
          rw [cohomologyMapAlong_cohomologyMap_apply]
          have hcomp :
              (Rep.resFunctor (decompHomS (w.adicCompletion K.1) S (ιs.fin w))).map
                (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) ≫
                  ordEmbMor S (ιs.fin w) hw = 0 := by
            apply Rep.hom_ext
            apply Representation.IntertwiningMap.ext
            apply LinearMap.ext
            intro a
            change (ordEmbMor S (ιs.fin w) hw).hom
              ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom a) = 0
            rw [sUnitsToUnits_hom_apply, ordEmbMor_hom_apply]
            exact ordEmb_eq_zero_of_mem S (ιs.fin w) hw (Additive.toMul a).2
          rw [hcomp, cohomologyMapAlong, cochainsMapAlong_zero, HomologicalComplex.homologyMap_zero]
          rfl
        exact (hzero y.1).trans (hzero z.1).symm
  have hyz : sUnitsBrauer K S (y.1 - z.1) = 0 := by
    refine brauerLocal_injective ιs ?_
    rw [map_sub, map_sub, map_zero]
    exact sub_eq_zero.2 htyz
  have h0 := eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero K S n hn0 hS (y.1 - z.1)
    (by rw [smul_sub, y.2, z.2, sub_zero]) hyz
  exact Subtype.ext (sub_eq_zero.1 h0)

theorem finite_cohomology_rootsOfUnity [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (r : ℕ)
    (hr : r ≤ 2) :
    Finite (cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) r) := by
  have : NeZero n := ⟨hn0⟩
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  interval_cases r
  · have : Finite (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
    exact finite_cohomology_zero _
  · exact finite_cohomology_one_rootsOfUnity S n hnS
  · exact finite_cohomology_two_rootsOfUnity_of_finite S n hnS
      (finite_nsmul_eq_zero_sUnits_two K S n hn0 hS)

end Brauer

end GroundTheory.ProfCoh
