module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_over_subfield_of_le {Ω : Type} [Field Ω] {K L : Subfield Ω} (h : K ≤ L)
    (hK : Module.Finite K Ω) : Module.Finite L Ω := by
  letI : Algebra K L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K L Ω

theorem exists_normal_proj_hasDiv_family (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (J : Type) [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (B : Type) [Finite B] (JJ : B → Type) [∀ b, Finite (JJ b)] (tt : ∀ b, JJ b → Ω)
    (htt : ∀ b, ∃ k, tt b k ≠ 0) :
    ∃ M : RatModel o Ω, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ M.HasDiv t ∧ ∀ b, M.HasDiv (tt b) := by
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (∀ b, JJ b) := Fintype.ofFinite _
  choose q₀ hq₀ using htt
  have hP : (∏ b, tt b (q₀ b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hq₀ b
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨M, hM, hp⟩ := GlobalTheory.ZH.exists_isNm_isProjOver o Ω (ArithBase.inj (o := o) (Ω := Ω))
    (J × ∀ b, JJ b) (fun q => t q.1 * ∏ b, tt b (q.2 b)) ⟨(i₀, q₀), mul_ne_zero hi₀ hP⟩
    (finite_over_subfield_of_le (Subfield.closure_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨i, j, rfl⟩
      exact ⟨(i, q₀), (j, q₀), (mul_div_mul_right _ _ hP).symm⟩))) hfin)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M J t
  have h2 : M.HasDiv t ∧ M.HasDiv (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨i, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).1⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨q, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).2⟩
  exact ⟨M, (GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ _).1 hM, hp, h2.1, (h.2.2 B JJ tt).1 h2.2⟩

theorem exists_admissible_affine_model_dividing_tuple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  intro o Ω _ _ _ _ S J₀ _ t₀ ht₀ hfin
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  haveI : NeZero S.N := ⟨hN⟩
  haveI : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (mul_ne_zero hr hN)⟩
  haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
  haveI : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T =>
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨i₀, hi₀⟩ := ht₀
  obtain ⟨M, hn, hp, hd, hF⟩ := exists_normal_proj_hasDiv_family o Ω (S.Gam × J₀)
    (fun q => S.th q.1 * t₀ q.2) ⟨(x₀, i₀), mul_ne_zero hx₀ hi₀⟩ hfin
    {b : Σ T : AddSubgroup S.Gam, T →+ ZMod S.N // S.FF b.1 b.2 ≠ 0}
    (fun b => S.J × (b.1.1 → ZMod ((S.r * S.N) ^ 2))) (fun b => S.FF b.1.1 b.1.2)
    (fun b => Function.ne_iff.1 b.2)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ S.th
  have hth : M.HasDiv S.th := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨x, ((h.2.1 _ t₀ x i z).1 hi).1⟩
  have ht : M.HasDiv t₀ := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨i, ((h.2.1 _ t₀ x i z).1 hi).2⟩
  have hA : ((fun x : Ω => x⁻¹) '' (Set.range S.th ∪ {x : Ω | ∃ T c k, x = S.FF T c k})).Finite :=
    ((Set.finite_range _).union (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.1).image _
  obtain ⟨U₀, a, -, hne, haff, -, -, hR, hsub⟩ := GlobalTheory.ZH.exists_affineOpen_ringOn_eq_adjoin_inv o Ω M S.R _
    S.fg S.frac hA ⊤ ⟨genericPoint M.Z, trivial⟩
  refine ⟨M, U₀, ⟨⟨hn, hp, hth, hne, fun x hx => ?_, fun x _ => hsub ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩,
    fun T c k _ _ => hsub ⟨_, Or.inr ⟨T, c, k, rfl⟩, rfl⟩⟩, fun T c _ h0 => hF ⟨⟨T, c⟩, h0⟩⟩, haff, ht⟩
  rw [hR]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem natCast_self_residueField_padicAlgCl_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  have : (((p : ℕ) : OO p) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [this, PadicAlgCl.valuation_p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast hp.out.one_lt
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

theorem ker_isMaximal_of_forall_pow_eq_one {A k : Type*} [CommRing A] [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) (φ : A →+* k) :
    (RingHom.ker φ).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨by simp, fun J a hJ ha haJ => ?_⟩
  obtain ⟨n, hn, h⟩ := hk (φ a) ha
  have h1 : 1 - a ^ n ∈ J := hJ (by simp [RingHom.mem_ker, h])
  have h2 : a ^ n ∈ J := J.pow_mem_of_mem haJ n hn
  simpa using J.add_mem h1 h2

theorem isClosed_image_point_of_forall_pow_eq_one {k : Type} [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) {X : Scheme.{0}} [JacobsonSpace X]
    (x : Sp k ⟶ X) (s : Sp k) : IsClosed ({x s} : Set X) := by
  obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing x
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hs : Spec.map φ s ∈ closedPoints (Spec Γ(X, V)) := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ?_
    have := (s : PrimeSpectrum k).isPrime
    have e : (s : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have : (Spec.map φ s : PrimeSpectrum Γ(X, V)).asIdeal = RingHom.ker φ.hom := by
      change Ideal.comap φ.hom (s : PrimeSpectrum k).asIdeal = _
      rw [e]; rfl
    rw [this]
    exact ker_isMaximal_of_forall_pow_eq_one hk φ.hom
  rw [← h] at hs
  rw [Scheme.Hom.comp_apply]
  exact hs

theorem exists_residueField_factor_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}}
    (x : Sp k ⟶ X) (s : Sp k) (z : X) (hz : x s = z) :
    ∃ r : X.residueField z ⟶ CommRingCat.of k, Spec.map r ≫ X.fromSpecResidueField z = x := by
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_integral_point_lifting_residue_point :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens),
      (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime],
        (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧
        (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  intro X _ π _ _ U hU p hp
  obtain ⟨hJ, hfin, -⟩ := jacobson_closedPoints_tools_int X π
  obtain ⟨-, hord, hgal⟩ := _root_.GlobalTheory.ZJ.kb_isAlgClosed_and_conj p
  have hcl : ∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X) :=
    fun x s => isClosed_image_point_of_forall_pow_eq_one hord x s
  refine ⟨fun x => ?_, hcl⟩
  let s : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hlift : ∃ (q : ℕ) (_ : Fact q.Prime) (y : Sp (OO q) ⟶ X),
      y (IsLocalRing.closedPoint (OO q)) = x s ∧ Set.range (gPt q ≫ y) ⊆ U := by
    obtain ⟨q, hq, hqz⟩ := exists_prime_residueField_eq_zero π (hcl x s)
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨K, hK, y, hy, hyU, -⟩ := exists_padic_point_scheme π (hcl x s) hqz U hU
    have hmem (a : PadicAlgCl q) : a ∈ OO q ↔ ‖a‖ ≤ 1 := by
      rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
      rfl
    let j : integralClosure ℤ_[q] K →+* OO q :=
      (K.val.toRingHom.comp (integralClosure ℤ_[q] K).val.toRingHom).codRestrict (OO q)
        fun a => (hmem _).mpr ((mem_integralClosure_padicInt_iff K _).mp a.2)
    haveI : IsLocalHom j := by
      refine ⟨fun a ha => ?_⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : ((a : K) : PadicAlgCl q) * (b : PadicAlgCl q) = 1 :=
        congrArg (fun z : OO q => (z : PadicAlgCl q)) hb
      have ha0 : (a : K) ≠ 0 := by
        intro h
        rw [h] at hb'
        simp at hb'
      have hinv : (a : K)⁻¹ ∈ integralClosure ℤ_[q] K := by
        rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
          ← eq_inv_of_mul_eq_one_right hb']
        exact (hmem _).mp b.2
      exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    refine ⟨q, inferInstance, spMap j ≫ y, ?_, ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
      exact IsLocalRing.comap_closedPoint j
    · rintro _ ⟨t, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      have key : spMap j ((gPt q) t) = genericPoint (Sp (integralClosure ℤ_[q] K)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        apply le_antisymm _ bot_le
        intro a ha
        have ha' : ((a : K) : PadicAlgCl q) ∈ (t : PrimeSpectrum (PadicAlgCl q)).asIdeal := ha
        haveI := (t : PrimeSpectrum (PadicAlgCl q)).isPrime
        rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum (PadicAlgCl q)).asIdeal,
          Ideal.mem_bot] at ha'
        exact Subtype.ext (Subtype.ext ha')
      rw [Scheme.Hom.comp_apply, key]
      exact hyU
  obtain ⟨q, hq, y, hy, hyU⟩ := hlift
  have hfz := hfin _ (hcl x s)
  obtain ⟨r', hr'⟩ := exists_residueField_factor_of_apply_eq x s _ rfl
  have hy' : (rPt q ≫ y) (IsLocalRing.closedPoint (kb q)) = x s := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO q))
  obtain ⟨r, hr⟩ := exists_residueField_factor_of_apply_eq (rPt q ≫ y) _ _ hy'
  obtain rfl : p = q := by
    have h1 : ((p : ℕ) : X.residueField (x s)) = 0 := by
      apply r'.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero p
    have h2 : ((q : ℕ) : X.residueField (x s)) = 0 := by
      apply r.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero q
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hp.out).mpr h1
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hq.out).mpr h2
    exact CharP.eq (X.residueField (x s)) ‹CharP _ p› ‹CharP _ q›
  obtain ⟨σ, hσ⟩ := hgal (X.residueField (x s)) r.hom r'.hom
  refine ⟨spMap σ.toRingHom ≫ y, ?_, ?_⟩
  · let τ : kb p →+* kb p := IsLocalRing.ResidueField.map (σ : OO p →+* OO p)
    have e1 : rPt p ≫ spMap σ.toRingHom = spMap τ ≫ rPt p := by
      refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
      rfl
    have e2 : r ≫ CommRingCat.ofHom τ = r' := by
      ext a
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (r.hom a)
      change τ (r.hom a) = r'.hom a
      rw [← hσ a c hc, ← hc]
      rfl
    rw [← Category.assoc, e1, Category.assoc]
    refine (congrArg (spMap τ ≫ ·) hr.symm).trans (Eq.trans ?_ hr')
    rw [← e2, Spec.map_comp, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    apply hyU
    refine ⟨t, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    congr 1
    have := (t : PrimeSpectrum (PadicAlgCl p)).isPrime
    have e : (t : PrimeSpectrum (PadicAlgCl p)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    apply PrimeSpectrum.ext
    ext a
    change (a : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal ↔
      ((σ a : OO p) : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal
    rw [e]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SpreadLevel

theorem appTop_unitOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (u : Rˣ) (u₀ : Kˣ)
    (h : f u = u₀) : Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn u₀ := by
  apply Units.ext
  have := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [h] at this
  exact this.symm

theorem appTop_injective {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  intro a b hab
  have ha := congrArg (fun q => q.hom a) e
  have hb := congrArg (fun q => q.hom b) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at ha hb
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hf
  exact ha.symm.trans ((congrArg _ hab).trans hb)

theorem linComb_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem stdSymp_cast {g g' : ℕ} (h : g = g') (i j : Fin (2 * g)) (i' j' : Fin (2 * g')) (hi : (i' : ℕ) = i)
    (hj : (j' : ℕ) = j) : stdSymp g' i' j' = stdSymp g i j := by
  subst h
  rw [Fin.ext hi, Fin.ext hj]

end SpreadLevel


open SpreadLevel in
theorem level_of_generic_of_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  intro hL R K _ _ _ _ _ _ P P₀ φ hp hw hg M ze ze₀ hM hze lev₀ y hy hind
  obtain ⟨w, hw⟩ := hw
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hu := appTop_unitOn (algebraMap R K) ze ze₀ hze
  have hΓ : Function.Injective (Units.map (spMap (algebraMap R K)).appTop.hom.toMonoidHom) :=
    Units.map_injective (appTop_injective _ hinj)
  have := P.isAb.comm
  have := P.isAb.proper
  let cs : Fin (2 * P.g) → Fin (2 * P₀.g) := Fin.cast (by rw [hg])
  have hy' : ∀ i, spMap (algebraMap R K) ≫ (y i).left = (lev₀.pt (cs i)).left ≫ φ := fun i => (hy (cs i) i rfl).symm
  let U : Over.mk ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R K)) (by simp)
  have tor : ∀ i, y i ^ M = 1 := fun i => by
    have e : U ≫ y i = pushHom hp (baseOver (Sp K)) (lev₀.pt (cs i)) := Over.OverMorphism.ext (hy' i)
    have e₁ : U ≫ (y i ^ M) = U ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one, e]
      exact (map_pow (pushHom hp _) _ M).symm.trans ((congrArg _ (lev₀.torsion _)).trans (map_one _))
    exact over_points_ext_of_injective _ P.A R K _ hinj _ _ _ (congrArg (fun q => q.left) e₁)
  refine ⟨⟨y, ?_, tor, hind, ?_, ?_⟩, rfl⟩
  · have := lev₀.prim
    rw [← hu] at this
    exact this.of_map_of_injective hΓ
  · intro F _ _ s x hx
    have hF : (M : F) ≠ 0 := by
      have := hM.map (Spec.preimage s).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have hM0 : 1 ≤ M := Nat.pos_of_ne_zero (by rintro rfl; exact hF Nat.cast_zero)
    have hc := (hL.mulN _ P M hM0).2.2.2.2 F s hF
    let Φ : (Fin (2 * P.g) → Fin M) → {x : Over.mk s ⟶ P.A // x ^ M = 1} := fun c =>
      ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)),
        linComb_pow _ _ M fun i => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' h => hind F s c c' (congrArg Subtype.val h)
    have : Finite {x : Over.mk s ⟶ P.A // x ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    have hb := hΦ.bijective_of_nat_card_le (by rw [hc]; simp)
    obtain ⟨c, h⟩ := hb.2 ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val h⟩
  · intro i j
    obtain ⟨c, hc, -⟩ := (hL.weil _ P M (baseOver (Sp R))).1 (y i) (y j) (tor i) (tor j)
    obtain ⟨r, hr, ⟨cu⟩⟩ := PolAV_exists_cubical hL.cube P₀
    have := P₀.isAb.comm
    have h₁ := WeilCube.weilIs_pull (c := cu) hL.globalFns P₀.isAb P.isLB hp w hw (T := baseOver (Sp K))
      (T₀ := baseOver (Sp R)) (spMap (algebraMap R K)) (by simp) (lev₀.torsion (cs i)) (lev₀.torsion (cs j))
      (hy' i) (hy' j) hc
    have h₂ := ((hL.weil _ P₀ M (baseOver (Sp K))).1 _ _ (lev₀.torsion (cs i)) (lev₀.torsion (cs j))).unique h₁
      (lev₀.pairing _ _)
    rw [stdSymp_cast hg i j (cs i) (cs j) rfl rfl, ← hu] at h₂
    have h₃ : c = unitOn ze ^ stdSymp P.g i j := hΓ (h₂.trans (map_zpow _ _ _).symm)
    exact h₃ ▸ hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω)

theorem supI_subset_of_specializes {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ :=
  fun _ hx => ⟨hx.1, fun j => M.O_le_of_specializes h (hx.2 j)⟩

theorem exists_isClosed_supI_eq [JacobsonSpace M.Z] (ξ : M.Z) (W : M.Z.Opens) (hξ : ξ ∈ W) :
    ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hV : IsOpen ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) :=
    W.isOpen.inter ((Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _)
  obtain ⟨x, ⟨⟨hxW, hxI⟩, hxc⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) ∩ closure {ξ})
    ⟨ξ, ⟨hξ, Set.mem_iInter₂.mpr fun _ ha => ha⟩, subset_closure rfl⟩
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hxW, hx, hs, (S.supI_subset_of_specializes M hs).antisymm
    fun a ha => Set.mem_iInter₂.mp hxI a ha⟩

theorem Over₀.supI_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (h : S.Over₀ M U₀)
    {ξ : M.Z} (hξ : ξ ∈ U₀) : S.supI M ξ = {x | S.th x ≠ 0} := by
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun j => ?_⟩⟩
  have h1 : S.th j / S.th x ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]
    exact mul_mem (h.le (S.th_mem j)) (h.th_unit x hx)
  exact (Algebra.mem_iInf.mp (Algebra.mem_iInf.mp h1 ξ) hξ :)

end ThetaSys

theorem isoFree_TT_and_supI_specializes :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) := by
  intro o Ω _ _ _ _ S M U₀ hO ⟨hL, hJ⟩ hT hS
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  refine ⟨fun ξ => ⟨?_, hpp _⟩, fun ξ z h => S.supI_subset_of_specializes M h, fun ξ hξ => ?_,
    fun ξ W hξ => S.exists_isClosed_supI_eq M ξ W hξ⟩
  · obtain ⟨x, -, hx, -, he⟩ := S.exists_isClosed_supI_eq M ξ ⊤ trivial
    obtain ⟨p, hp, y, hy⟩ := (hL U₀ le_rfl hO.ne x hx).1
    obtain ⟨y₀, hy₀, -, ⟨τ⟩⟩ := hT x p y hy
    have h1 : S.HH M ξ = τ.yy.ker := by
      rw [← (hS x p y y₀ τ hy hy₀).2, ThetaSys.HH, ThetaSys.HH, he]
    rw [ThetaSys.TT, h1]
    exact τ.isoFree
  · have h1 : S.perp ⊥ = ⊤ := by
      refine top_unique fun a _ h hh => ?_
      rw [AddSubgroup.mem_bot.mp hh]
      simp [eStd]
    rw [ThetaSys.TT, ThetaSys.HH, hO.supI_eq hξ, S.supp, ← h1, hpp]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormDividingWeightSumEqOfModelPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory

theorem norm_val_FF_eq_of_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) := by
  intro o Ω _ _ _ _ S M U₀ hO h0 h1 _ z p _ y y₀ τ hC hA
  have hT : S.TT M z = S.perp τ.yy.ker := by
    rw [ThetaSys.TT, (h0 z p y y₀ τ hC hA).2]
  obtain ⟨hmem, -, hpp, -⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  rw [hT]
  intro c k α hdiv hα hc
  have hcw : c = τ.wt α := AddMonoidHom.ext fun t => hc t.1 t.2 t.2
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [hA]
    exact hC.norm_val_le_one ((M.O z).algebraMap_mem a)
  have hk : M.val (gPt p ≫ y) (S.FF _ c k) = y₀ ⟨_, hmem _ c k⟩ := (hA ⟨_, hmem _ c k⟩).symm
  refine le_antisymm ?_ ?_
  · rw [hk]
    exact (h1 p y₀ τ hint _ c k (hmem _ c k) τ.isoFree).1 le_rfl
      (τ.isoFree.1.trans (hpp _).le) α hα hc
  · subst hcw
    obtain ⟨k₁, hk₁, he⟩ := τ.eq α hα
    rw [← he, hA]
    let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w := fun w' => by
      have : (gPt p ≫ y) w' ∈ Set.range (gPt p ≫ y) := ⟨w', rfl⟩
      rw [RatModel.range_eq_singleton _ w] at this
      rw [this]
    have hU : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
    have hq := hdiv.2 k₁
    have hmul := RatModel.val_mul hw
      (RatModel.O_le_of_specializes (RatModel.gPt_specializes hC.1 w) hq)
      (RatModel.ringOn_le_O hU (hO.le (hmem _ (τ.wt α) k)))
    rw [div_mul_cancel₀ _ hdiv.1] at hmul
    change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k₁)‖ ≤ _
    rw [hmul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hC.norm_val_le_one hq)

end GlobalTheory
end

