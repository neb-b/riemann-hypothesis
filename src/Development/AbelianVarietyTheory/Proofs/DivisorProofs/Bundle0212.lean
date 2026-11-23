module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
section
noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise

namespace GlobalTheory.WeilM

theorem eq_zero_of_mul_invariant {X : Type} [TopologicalSpace X] (l : (X → ℂ) →ₗ[ℂ] ℂ) (S : Set (X → ℂ))
    (hS : ∀ f ∈ S, IsLocallyConstant f) (hl : ∀ f ∈ S, ∀ φ ∈ SB X, l (f * φ) = l φ)
    {φ : X → ℂ} (hφ : φ ∈ SB X) (h : ∀ x, φ x ≠ 0 → ∃ f ∈ S, f x ≠ 1) : l φ = 0 := by
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ SB X, U.indicator φ ∈ SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hsupp : IsClopen (Function.support φ) := (hφ.1.isClopen_fiber 0).compl
  have hc : IsCompact (Function.support φ) := by
    have := hφ.2
    rwa [HasCompactSupport, tsupport, hsupp.isClosed.closure_eq] at this
  have key : ∃ U : Set X, IsClopen U ∧ Function.support φ ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0 := by
    refine hc.induction_on (p := fun s => ∃ U : Set X, IsClopen U ∧ s ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, le_rfl, fun φ' _ h0 => ?_⟩
      rw [Set.subset_empty_iff, Function.support_eq_empty_iff] at h0
      rw [h0, map_zero]
    · rintro s t hst ⟨U, hU, htU, h'⟩
      exact ⟨U, hU, hst.trans htU, h'⟩
    · rintro s t ⟨U, hU, hsU, h1⟩ ⟨V, hV, htV, h2⟩
      refine ⟨U ∪ V, hU.union hV, Set.union_subset_union hsU htV, fun φ' hφ' hs => ?_⟩
      rw [← Set.indicator_self_add_compl U φ', map_add (f := _), h1 _ (hind U hU _ hφ') Set.support_indicator_subset,
        h2 _ (hind _ hU.compl _ hφ'), add_zero]
      rw [Set.support_indicator]
      rintro x ⟨hx, hx'⟩
      exact (hs hx').resolve_left hx
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := h x hx
      have hU := (hS f hf).isClopen_fiber (f x)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hU.isOpen.mem_nhds rfl), _, hU, le_rfl, fun φ' hφ' hs => ?_⟩
      have h1 : f * φ' = f x • φ' := by
        funext y
        by_cases hy : φ' y = 0
        · simp [hy]
        · have : f y = f x := hs hy
          simp [this]
      have h2 := hl f hf φ' hφ'
      rw [h1, map_smul, smul_eq_mul] at h2
      have h3 : (f x - 1) * l φ' = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hfx)
  obtain ⟨U, -, hU, h'⟩ := key
  exact h' φ hφ hU

theorem eq_one_of_forall_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerTwoNormLowerBound.main
  | exact _root_.GlobalTheory.PowerTwoNormLowerBound.main
  | (apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerTwoNormLowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerTwoNormLowerBound.main ..)

theorem isLocallyConstant_addChar {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V]
    (ψ : AddChar V ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have h0 : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
  have h1 : ∀ x ∈ K, ψ x = 1 := fun x hx => eq_one_of_forall_pow_near fun n => by
    rw [← AddChar.map_nsmul_eq_pow]
    exact hK (nsmul_mem hx n)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' (K : Set V) ∈ 𝓝 x :=
    (K.isOpen.preimage (by fun_prop)).mem_nhds (by simp)
  filter_upwards [this] with z hz
  have h2 : z = x + (-x + z) := by abel
  rw [h2, AddChar.map_add_eq_mul, h1 _ hz, mul_one]

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarch_field : NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hU
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩,
      SplitWeil.isOpen_cball s⟩, hs⟩

theorem nonarch_pi (κ : Type) [Fintype κ] : NonarchimedeanAddGroup (κ → F) where
  is_nonarchimedean U hU := by
    haveI := nonarch_field F
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := F) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup F),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

section Cov

variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by
  haveI := SplitWeil.secondCountable F
  haveI := SplitWeil.t2Space F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hM : M.det ≠ 0 := hu ▸ u.ne_zero
  revert u
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD u hu
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [det_diagonal] at hD hu
    have A : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = ∏ i, Units.mk0 (D i) (A i) := Units.ext (by simp [hu])
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => (Units.mk0 (D i) (A i))⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := Units.mk0 (D i) (A i))).symm
    rw [this, Measure.pi_pi, hu', map_prod, ENNReal.ofNNReal_finsetProd, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro t u hu
    have hu' : u = 1 := Units.ext (by simp [hu])
    rw [hu', map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    cases t with | mk t_i t_j t_hij t_c =>
    simp [transvection, add_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]
  · intro A B hA hB IHA IHB u hu
    have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := Units.ext (by simp [hu])
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [hu', map_mul, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _), ← Measure.map_smul,
      IHB _ rfl, IHA _ rfl]
    exact (hm A).aemeasurable

theorem integral_comp_mulVec (g : GL κ F) (f : (κ → F) → ℂ) :
    ((distribHaarChar F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
      ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ : κ => ν) = ∫ x, f x ∂(Measure.pi fun _ : κ => ν) := by
  haveI := SplitWeil.secondCountable F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  let e : (κ → F) ≃ᵐ (κ → F) :=
    { toFun := g.val.mulVec, invFun := (g⁻¹).val.mulVec
      left_inv := fun x => by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun x => by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      measurable_toFun := hm _, measurable_invFun := hm _ }
  conv_rhs => rw [← smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl, integral_smul_measure]
  rw [show g.val.mulVec = e from rfl, integral_map_equiv]
  simp

end Cov

end GlobalTheory.WeilM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNormalSchemePullbackSpMapOfAlgebra
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteInt
section
namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := _root_.GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes B
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine _root_.GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom B _ φ n hinj hn hmul M ?_
  refine _root_.GlobalTheory.pic_pi_isOfFinOrder _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact _root_.GlobalTheory.pic_isOfFinOrder_of_finite_int _ N

end GlobalTheory.PicReducedTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecOfQuasiFiniteOfNormalStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing A] (φ : A →+* B), (∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭)) → φ.FiniteType → LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)) → (∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) → IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  first | exact @GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | exact GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | (intros; apply GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocal
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

theorem isProper_of_represents_of_local_proper : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  intro S Z z r H u hu hloc
  choose W hsW T y π hπ hy hT using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_
  · rw [eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩
  intro s
  set V : H.Opens := u.1 ⁻¹ᵁ W s
  have hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι := by
    change V.ι ≫ u.1 = _
    rw [morphismRestrict_ι]
  obtain ⟨φ, hφ, -⟩ := hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1
  obtain ⟨ψ, hψ, -⟩ := hu (T s) (y s)
  have hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι := by
    rw [← hy s, ← hψ]; rfl
  have hrange : Set.range ψ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change u.1 (ψ t) ∈ W s
    have : u.1 (ψ t) = (W s).ι (π s t) := by
      rw [← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]
    rw [this]
    exact ((π s) t).2
  let ψ' : T s ⟶ V := IsOpenImmersion.lift V.ι ψ hrange
  have hψ' : ψ' ≫ V.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have h1 : ψ' ≫ φ = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hT s (T s) (y s) (π s) (hy s)
    have e1 : HPt.map (ψ' ≫ φ) (y s) = y s := by
      rw [HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]
    have e2 : HPt.map (𝟙 (T s)) (y s) = y s := HPt.map_id _
    exact (hc _ e1).trans (hc _ e2).symm
  have h2 : φ ≫ ψ' = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hu V (HPt.map V.ι u)
    have e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u := by
      rw [Category.assoc, hψ', HPt.map_comp, hψ, hφ]
    have e2 := (hc _ e1).trans (hc _ rfl).symm
    rw [← cancel_mono V.ι, e2, Category.id_comp]
  have hiso : IsIso φ := ⟨⟨ψ', h2, h1⟩⟩
  have hcomp : φ ≫ π s = u.1 ∣_ W s := by
    rw [← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]
    rfl
  rw [← hcomp]
  haveI := hπ s
  infer_instance

end GlobalTheory.HilbGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfForallIsPushoutApp
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.PushoutSquare

theorem isPullback_of_forall_isPushout_app :
    ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  intro X Y S S' j p y q hS hS' hj w H
  let φ : X ⟶ pullback y q := pullback.lift j p w
  have hφ1 : φ ≫ pullback.fst y q = j := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd y q = p := pullback.lift_snd _ _ _
  suffices hiso : IsIso φ by
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2
  have hPb : IsPullback (pullback.fst y q) (pullback.snd y q) y q := IsPullback.of_hasPullback y q
  haveI : IsAffineHom q := inferInstance
  haveI : IsAffineHom (pullback.fst y q) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hPb.flip inferInstance
  let U : Y.affineOpens → (pullback y q).Opens := fun V => pullback.fst y q ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    show ⨆ V : Y.affineOpens, pullback.fst y q ⁻¹ᵁ (V : Y.Opens) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  show MorphismProperty.isomorphisms Scheme φ
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre : φ ⁻¹ᵁ U V = j ⁻¹ᵁ V.1 := by
    show φ ⁻¹ᵁ (pullback.fst y q ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1
    rw [← Scheme.Hom.comp_preimage, hφ1]
  have hUa : IsAffineOpen (U V) := V.2.preimage _
  have hSa : IsAffineOpen (φ ⁻¹ᵁ U V) := by rw [hpre]; exact V.2.preimage j
  haveI : IsAffine (U V).toScheme := hUa
  haveI : IsAffine (φ ⁻¹ᵁ U V).toScheme := hSa

  have P1 := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y (pullback y q) S S'
    (pullback.fst y q) (pullback.snd y q) y q hPb hS hS' V.1 V.2
  have P2 := H V.1 V.2
  let c : Γ(pullback y q, U V) ⟶ Γ(X, j ⁻¹ᵁ V.1) := φ.appLE (U V) (j ⁻¹ᵁ V.1) hpre.ge
  have key : ∀ {T : Scheme.{0}} (g j' : X ⟶ T) (hg : g = j') (A : T.Opens) (e : j' ⁻¹ᵁ A ≤ g ⁻¹ᵁ A),
      g.appLE A (j' ⁻¹ᵁ A) e = j'.appLE A (j' ⁻¹ᵁ A) le_rfl := by
    intro T g j' hg A e; subst hg; rfl
  have hc1 : (pullback.fst y q).app V.1 ≫ c = j.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact key _ _ hφ1 _ _
  have hc2 : (pullback.snd y q).appLE ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (fun _ _ => trivial) ≫ c =
      p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
    refine (Scheme.Hom.appLE_comp_appLE φ (pullback.snd y q) ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (j ⁻¹ᵁ V.1)
      (fun _ _ => trivial) hpre.ge).trans ?_
    have e2 : ∀ (e : j ⁻¹ᵁ V.1 ≤ (φ ≫ pullback.snd y q) ⁻¹ᵁ ⊤),
        (φ ≫ pullback.snd y q).appLE ⊤ (j ⁻¹ᵁ V.1) e = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
      intro e
      have gen : ∀ (g : X ⟶ S') (hg : g = p) (e' : j ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤),
          g.appLE ⊤ (j ⁻¹ᵁ V.1) e' = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
        intro g hg e'; subst hg; rfl
      exact gen _ hφ2 e
    exact e2 _
  have hcE : c = (P1.isoIsPushout _ _ P2).hom := by
    apply P1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]; exact hc1
    · rw [IsPushout.inr_isoIsPushout_hom]; exact hc2
  have hcI : IsIso c := by rw [hcE]; infer_instance
  have hTop : IsIso (φ ∣_ U V).appTop := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    refine (Scheme.Hom.appLE_congr φ _ (Scheme.Opens.ι_image_top (U V))
      ((Scheme.Opens.ι_image_top (φ ⁻¹ᵁ U V)).trans hpre) (fun f => IsIso f)).mpr ?_
    exact hcI
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine (φ ∣_ U V))).mpr (inferInstanceAs (IsIso (Spec.map _)))

end GlobalTheory.PushoutSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι), (∀ c : ℂ, IsFam act 0 fun _ _ => c) ∧ (∀ w f g, IsFam act w f → IsFam act w g → (IsFam act w fun i τ => f i τ + g i τ) ∧ IsFam act w fun i τ => f i τ - g i τ) ∧ (∀ w (c : ℂ) f, IsFam act w f → IsFam act w fun i τ => c * f i τ) ∧ (∀ w w' f g, IsFam act w f → IsFam act w' g → IsFam act (w + w') fun i τ => f i τ * g i τ) ∧ (∀ w f (k : ℕ), IsFam act w f → IsFam act (k * w) fun i τ => f i τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act w (f k)) → IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act (w k) (f k)) → IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f, (∀ k γ, φ (act' k γ) = act (φ k) γ) → IsFam act w f → IsFam act' w fun k => f (φ k)) := by
  first | exact @GlobalTheory.QFam.isFam_algebra | exact GlobalTheory.QFam.isFam_algebra | (intros; apply GlobalTheory.QFam.isFam_algebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

variable (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
  [Algebra ℚ B] [IsScalarTower ℚ F B]

theorem cenMap_tmul (q : ℚ_[ℓ]) (f : F) : cenMap ℓ F B (q ⊗ₜ f) = q ⊗ₜ algebraMap F B f := by
  simp [cenMap]

theorem cenMap_mem (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ)
    {a : ℚ_[ℓ] ⊗[ℚ] F} (ha : a ∈ cenOrder ℓ F) : cenMap ℓ F B a ∈ locOrder ℓ Λ := by
  have h : cenOrder ℓ F ≤ (locOrder ℓ Λ).comap ((cenMap ℓ F B).restrictScalars ℤ_[ℓ]) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    show cenMap ℓ F B _ ∈ locOrder ℓ Λ
    rw [cenMap_tmul]
    exact Algebra.subset_adjoin ⟨_, hΛ a, rfl⟩
  exact h ha

theorem cenMap_commute (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) : Commute (cenMap ℓ F B a) y := by
  first
  | exact @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | (apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap ..)

def cenIncl (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    cenOrder ℓ F →ₐ[ℤ_[ℓ]] locOrder ℓ Λ :=
  (((cenMap ℓ F B).restrictScalars ℤ_[ℓ]).comp (cenOrder ℓ F).val).codRestrict (locOrder ℓ Λ)
    (fun a => cenMap_mem ℓ F B Λ hΛ a.2)

theorem coe_cenIncl (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    (cenIncl ℓ F B Λ hΛ a : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B a := rfl

def cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    Algebra (cenOrder ℓ F) (locOrder ℓ Λ) :=
  (cenIncl ℓ F B Λ hΛ).toRingHom.toAlgebra' fun a x => Subtype.ext (cenMap_commute ℓ F B a x)

theorem algebraMap_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    letI := cenAlgebra ℓ F B Λ hΛ
    algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a = cenIncl ℓ F B Λ hΛ a := rfl

theorem isScalarTower_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    letI := cenAlgebra ℓ F B Λ hΛ
    IsScalarTower ℤ_[ℓ] (cenOrder ℓ F) (locOrder ℓ Λ) := by
  letI := cenAlgebra ℓ F B Λ hΛ
  exact IsScalarTower.of_algebraMap_eq fun r => ((cenIncl ℓ F B Λ hΛ).commutes r).symm

end GlobalTheory.LocMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitaryStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_image_standardLattice_unitary : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.selfDual_matLat_stdLat | exact GlobalTheory.LatOrb.selfDual_matLat_stdLat | (intros; apply GlobalTheory.LatOrb.selfDual_matLat_stdLat <;> assumption)
end

