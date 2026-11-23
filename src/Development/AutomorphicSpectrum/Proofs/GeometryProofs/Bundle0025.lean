module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieCarrier

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar (dualMap)

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def epsHom (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') : epsAt x' ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ))) (by
    subst h
    show _ ≫ _ ≫ x = _ ≫ _ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem dualMap_epsMul (φ : R →+* R') (c : R) :
    (dualMap φ).comp (epsMul c) = (epsMul (φ c)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [dualMap, epsMul, mul_comm]

theorem surjective_fst :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) := by
  intro p
  have hn : ∀ m : R, (TrivSqZeroExt.inr m : TrivSqZeroExt R R) ∈ p.asIdeal := fun m =>
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact p.asIdeal.zero_mem)
  have : p.asIdeal.IsPrime := p.isPrime
  refine ⟨⟨Ideal.comap (TrivSqZeroExt.inlHom R R) p.asIdeal, Ideal.IsPrime.comap _⟩, ?_⟩
  change PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom _ = p
  ext y
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
  change TrivSqZeroExt.inl y.fst ∈ p.asIdeal ↔ y ∈ p.asIdeal
  have hy : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
    eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
  rw [hy]
  constructor
  · intro h
    have := p.asIdeal.add_mem h (hn y.snd)
    rwa [sub_add_cancel] at this
  · intro h
    exact p.asIdeal.sub_mem h (hn y.snd)

theorem tan_ext {G : Over S} [GrpObj G] (φ : R →+* R') (hφ : Function.Injective φ)
    (x : Spec (CommRingCat.of R) ⟶ S) (v v' : epsAt x ⟶ G) (hv : IsTanAt G x v) (hv' : IsTanAt G x v')
    (h : Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v'.left) :
    v = v' := by
  apply Over.OverMorphism.ext
  have hinj : Function.Injective ((TrivSqZeroExt.fstHom R R R).toRingHom.prod (dualMap φ)) := by
    intro a b hab
    have h2 : dualMap φ a = dualMap φ b := congrArg Prod.snd hab
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    simp [dualMap, hφ.eq_iff] at h3 h4
    exact TrivSqZeroExt.ext h3 h4
  unfold IsTanAt at hv hv'
  exact GlobalTheory.CompanionTheory.Ar.LieEx.joint_epi _ _ hinj surjective_fst v.left v'.left (hv.trans hv'.symm) h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_fromSpecStalk (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hxW : genPt ξ ∈ W := p.2.mem_open W.isOpen hyW
  have key : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 =
      X.fromSpecStalk (genPt ξ) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hyW, ← hW.fromSpecStalk_eq_fromSpecStalk hxW]
    simp only [IsAffineOpen.fromSpecStalk]
    rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have e1 : Spec.map (CommRingCat.ofHom (genMap ξ p)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) :=
    Spec.map_comp _ _
  rw [e1, Category.assoc]
  exact (congrArg (fun f => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ f) key).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem span_ext {G : Over S} [GrpObj G] (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S)
    (x' : Spec (CommRingCat.of R') ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E : Type} [AddCommGroup E] [Module R' E] (M : LieModel G x' E) (e : E)
    (he : e ∈ Submodule.span φ.range {e | ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left}) :
    ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  suffices H : ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ M.pt e = epsHom φ x x' h ≫ v by
    obtain ⟨v, hv, hev⟩ := H
    exact ⟨v, hv, by rw [hev]; rfl⟩
  induction he using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨v, hv, hav⟩ := ha
    exact ⟨v, hv, Over.OverMorphism.ext hav⟩
  | zero =>
    refine ⟨1, (GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff x G 1).mpr (MonObj.comp_one _), ?_⟩
    rw [MonObj.comp_one]
    have h0 : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h0).symm
  | add a b _ _ ha hb =>
    obtain ⟨v, hv, hva⟩ := ha
    obtain ⟨w, hw, hwb⟩ := hb
    refine ⟨v * w, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv hw ⊢
      rw [MonObj.comp_mul, hv, hw, _root_.mul_one]
    · rw [M.add, hva, hwb, MonObj.comp_mul]
  | smul a b _ hb =>
    obtain ⟨v, hv, hvb⟩ := hb
    obtain ⟨r, hr⟩ := a
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hr
    refine ⟨GlobalTheory.CompanionTheory.Ar.LieEx.hom x (c • LinearMap.id) ≫ v, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv ⊢
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieEx.zsec_hom]
      exact hv
    · apply Over.OverMorphism.ext
      change (M.pt ((φ c) • b)).left = _
      rw [M.smul, hvb]
      have e2 : Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
          Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          dualMap_epsMul]
      change Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left =
        Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) ≫ v.left
      rw [← Category.assoc, e2, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.LieCarrier

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_carrier (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    (∀ e, e ∈ M.lat p ↔ ∃ v, M.Extends p e v) ∧
      (IsCptGen ξ → Smooth G.hom → ∀ e v v', M.Extends p e v → M.Extends p e v' → v = v') := by
  refine ⟨fun e => ⟨fun he => ?_, fun hv => Submodule.subset_span hv⟩, ?_⟩
  · exact LieCarrier.span_ext (genMap ξ p) (X.fromSpecStalk p.1) ξ
      (LieCarrier.genMap_fromSpecStalk p) M e he
  · intro hgen _ e v v' hv hv'
    exact LieCarrier.tan_ext (genMap ξ p) (hgen.inj p) _ v v' hv.1 hv'.1 (hv.2.symm.trans hv'.2)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
section
namespace GlobalTheory.CompanionTheory.Ar.FlagChange

open GlobalTheory.CompanionTheory.Ar

theorem exists_coeff_of_mem_step {L Li : Type} [Field L] [AddCommGroup Li] [Module L Li] {r : ℕ}
    (g : Fin r → Li) (n : ℕ) (x : Li) (hx : x ∈ flagStep L g n) :
    ∃ c : Fin r → L, (∀ k : Fin r, n ≤ (k : ℕ) → c k = 0) ∧ x = ∑ k, c k • g k := by
  unfold flagStep at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination L).1 hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h
    have : k ∈ ({k : Fin r | (k : ℕ) < n} : Set (Fin r)) :=
      hl (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hk)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul L (g i))]

theorem adapted_triangular (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ)
    (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L)
    (_hf : LinearIndependent L f) (hb : LinearIndependent L b)
    (_hv1 : ∀ k, v k k = 1) (_hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (hg : ∀ k, g k = ∑ j, (v * w) j k • f j)
    (hflag : ∀ i : ℕ, flagStep L b i = flagStep L g i) :
    ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧
      (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  have hC : ∀ i : Fin r, ∃ c : Fin r → L,
      (∀ k : Fin r, (i : ℕ) + 1 ≤ (k : ℕ) → c k = 0) ∧ b i = ∑ k, c k • g k := fun i =>
    exists_coeff_of_mem_step g _ _ (by
      rw [← hflag]
      exact Submodule.subset_span ⟨i, by simp, rfl⟩)
  choose C hC0 hCb using hC
  have hgW : ∀ k, g k = ∑ m, w m k • ∑ j, v j m • f j := by
    intro k
    rw [hg k]
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  refine ⟨Matrix.of fun i m => ∑ k, C i k * w m k, fun i => ?_, fun i m him => ?_, fun i => ?_⟩
  · generalize hW : (fun m => ∑ j, v j m • f j) = W at *
    have hW' : ∀ m, ∑ j, v j m • f j = W m := fun m => congrFun hW m
    simp only [hW'] at hgW ⊢
    calc b i = ∑ k, C i k • ∑ m, w m k • W m :=
          (hCb i).trans (Finset.sum_congr rfl fun k _ => by rw [hgW k])
      _ = ∑ m, (∑ k, C i k * w m k) • W m := by
          simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
          exact Finset.sum_comm
      _ = _ := rfl
  · show ∑ k, C i k * w m k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ≤ i
    · rw [hw0 m k (lt_of_le_of_lt hk him), mul_zero]
    · rw [hC0 i k (not_le.1 hk), zero_mul]
  · have hdiag : ∑ k, C i k * w i k = C i i * w i i := by
      refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hw0 i k h, mul_zero]
      · rw [hC0 i k h, zero_mul]
    show ∑ k, C i k * w i k ≠ 0
    rw [hdiag]
    refine mul_ne_zero (fun h0 => ?_) (hwd i)
    have hmem : b i ∈ flagStep L g i := by
      rw [hCb i]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : (k : ℕ) < i
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
      · have hz : C i k = 0 := by
          rcases eq_or_lt_of_le (not_lt.1 hk) with h | h
          · rw [show k = i from Fin.ext h.symm, h0]
          · exact hC0 i k h
        rw [hz, zero_smul]
        exact Submodule.zero_mem _
    rw [← hflag] at hmem
    exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (by simp) hmem

end GlobalTheory.CompanionTheory.Ar.FlagChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFiniteIndex
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulBy (b : 𝓞 L) : (Fin n → L) →+ (Fin n → L) :=
  DistribSMul.toAddMonoidHom _ b

theorem mulBy_apply (b : 𝓞 L) (x : Fin n → L) (i : Fin n) : mulBy b x i = (b : L) * x i := by
  simp [mulBy, Algebra.smul_def]

theorem coe_ne_zero {b : 𝓞 L} (hb : b ≠ 0) : (b : L) ≠ 0 := by
  simpa using hb

theorem mulBy_injective {b : 𝓞 L} (hb : b ≠ 0) :
    Function.Injective (mulBy (L := L) (n := n) b) := by
  intro x y h
  funext i
  have := congrFun h i
  rw [mulBy_apply, mulBy_apply] at this
  exact mul_left_cancel₀ (coe_ne_zero hb) this

noncomputable def incl : (Fin n → 𝓞 L) →+ (Fin n → L) where
  toFun z i := (z i : L)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem incl_injective : Function.Injective (incl (L := L) (n := n)) := by
  intro x y h
  funext i
  have := congrFun h i
  exact RingOfIntegers.coe_injective this

theorem frame_one_eq :
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup =
      (⊤ : AddSubgroup (Fin n → 𝓞 L)).map incl := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, mem_frame_one, AddSubgroup.mem_map, AddSubgroup.mem_top,
    true_and]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, funext fun i => (hz i).symm⟩
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, rfl⟩

theorem relIndex_mulBy_ne_zero {b : 𝓞 L} (hb : b ≠ 0) :
    ((frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy b)).relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  classical
  let I : Ideal (𝓞 L) := Ideal.span {b}
  have hI : I ≠ ⊥ := by simpa [I] using hb
  haveI : Finite (𝓞 L ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let f : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L ⧸ I) :=
    (Ideal.Quotient.mk I).toAddMonoidHom.compLeft (Fin n)
  let m : (Fin n → 𝓞 L) →+ (Fin n → 𝓞 L) := DistribSMul.toAddMonoidHom _ b
  have hk : f.ker ≤ m.range := by
    intro z hz
    have h1 : ∀ i, ∃ c, z i = b * c := fun i => by
      have : (Ideal.Quotient.mk I) (z i) = 0 := congrFun (AddMonoidHom.mem_ker.1 hz) i
      exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this) |>.imp
        fun c hc => by rw [← hc, mul_comm]
    choose c hc using h1
    exact ⟨c, funext fun i => by simp [m, hc i]⟩
  have hf : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  have hm : m.range.index ≠ 0 := fun h => hf (by
    have := AddSubgroup.index_dvd_of_le hk
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this)
  have e : (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy b) =
      m.range.map incl := by
    rw [frame_one_eq]
    ext x
    constructor
    · rintro ⟨_, ⟨z, -, rfl⟩, rfl⟩
      refine ⟨m z, ⟨z, rfl⟩, ?_⟩
      funext i
      simp [m, incl, mulBy_apply]
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨incl z, ⟨z, trivial, rfl⟩, ?_⟩
      funext i
      simp [m, incl, mulBy_apply]
  rw [e, frame_one_eq, AddSubgroup.relIndex_map_map_of_injective _ _ incl_injective,
    AddSubgroup.relIndex_top_right]
  exact hm

theorem exists_clearing (T : FinitePlace L → Matrix (Fin n) (Fin n) L)
    (hS : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) :
    ∃ a : 𝓞 L, a ≠ 0 ∧ ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * T w i j) ≤ 1 ∧ w ((a : L) * (T w)⁻¹ i j) ≤ 1 := by
  classical
  let s : Finset L := hS.toFinset.biUnion fun w =>
    (Finset.univ : Finset (Fin n × Fin n)).biUnion fun p => {T w p.1 p.2, (T w)⁻¹ p.1 p.2}
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 L)) s
  have hint : ∀ x ∈ s, ∀ w : FinitePlace L, w (((b : 𝓞 L) : L) * x) ≤ 1 := by
    intro x hx w
    obtain ⟨r, hr⟩ := hb x hx
    have : ((b : 𝓞 L) : L) * x = (r : L) := by
      have h2 : (b : 𝓞 L) • x = ((b : 𝓞 L) : L) * x := Algebra.smul_def _ _
      rw [← h2, ← hr]
    rw [this]
    exact place_int_le_one w r
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun w i j => ?_⟩
  by_cases hw : UnitAt w (T w)
  · exact ⟨place_mul_le_one w (place_int_le_one w _) (hw.1 i j),
      place_mul_le_one w (place_int_le_one w _) (hw.inv_le_one i j)⟩
  · have hwS : w ∈ hS.toFinset := by simpa using hw
    constructor
    · refine hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w
      simp
    · refine hint _ (Finset.mem_biUnion.2 ⟨w, hwS, Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩⟩) w
      simp

theorem mulBy_frame_le_glued (T : FinitePlace L → Matrix (Fin n) (Fin n) L)
    (hT : ∀ v, (T v).det ≠ 0) {a : 𝓞 L}
    (ha : ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * (T w)⁻¹ i j) ≤ 1) :
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulBy a) ≤ (glued T).toAddSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L) := hx
  obtain hxi := mem_frame_one.1 hx'
  show mulBy a x ∈ glued T
  rw [glued, Submodule.mem_iInf]
  intro w
  refine mem_locAt_frame.2 ⟨((a : L) • (T w)⁻¹) *ᵥ x, fun i => ?_, ?_⟩
  · refine place_sum_le_one w Finset.univ (fun j => ((a : L) • (T w)⁻¹) i j * x j) fun j _ => ?_
    obtain ⟨r, hr⟩ := hxi j
    rw [hr]
    exact place_mul_le_one w (ha w i j) (place_int_le_one w r)
  · have hu : IsUnit (T w).det := IsUnit.mk0 _ (hT w)
    rw [Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    funext i
    simp [mulBy_apply]

theorem mulBy_glued_le_frame (T : FinitePlace L → Matrix (Fin n) (Fin n) L) {a : 𝓞 L}
    (ha : ∀ (w : FinitePlace L) (i j : Fin n), w ((a : L) * T w i j) ≤ 1) :
    (glued T).toAddSubgroup.map (mulBy a) ≤ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ glued T := hx
  show mulBy a x ∈ frame (1 : Matrix (Fin n) (Fin n) L)
  rw [← iInf_locAt_frame_one, Submodule.mem_iInf]
  intro w
  obtain ⟨y, hy, hxy⟩ := mem_locAt_frame.1 ((Submodule.mem_iInf _).1 hx' w)
  refine mem_locAt_frame_one.2 fun i => ?_
  rw [mulBy_apply, hxy, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine place_sum_le_one w Finset.univ _ fun j _ => ?_
  rw [← mul_assoc]
  exact place_mul_le_one w (ha w i j) (hy j)

theorem glued_commensurable (L : Type) [Field L] [NumberField L] (n : ℕ)
    (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (hT : ∀ v, (T v).det ≠ 0)
    (hS : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) :
    (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  obtain ⟨a, ha0, ha⟩ := exists_clearing T hS
  set F := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hF
  set G := (glued T).toAddSubgroup with hG
  have h1 : F.map (mulBy a) ≤ G := mulBy_frame_le_glued T hT fun w i j => (ha w i j).2
  have h2 : G.map (mulBy a) ≤ F := mulBy_glued_le_frame T fun w i j => (ha w i j).1
  have i1 : (F.map (mulBy a)).relIndex F ≠ 0 := relIndex_mulBy_ne_zero ha0
  have hcomp : (F.map (mulBy a)).map (mulBy a) = F.map (mulBy (a * a)) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x i
    simp [mulBy_apply, mul_assoc]
  have i2 : ((F.map (mulBy a)).map (mulBy a)).relIndex F ≠ 0 := by
    rw [hcomp]
    exact relIndex_mulBy_ne_zero (mul_ne_zero ha0 ha0)
  constructor
  · intro h
    have := AddSubgroup.relIndex_dvd_of_le_left F h1
    rw [h] at this
    exact i1 (Nat.eq_zero_of_zero_dvd this)
  · have i3 : ((F.map (mulBy a)).map (mulBy a)).relIndex (G.map (mulBy a)) ≠ 0 :=
      AddSubgroup.relIndex_ne_zero_trans i2 (by
        rw [AddSubgroup.relIndex_eq_one.2 h2]; exact one_ne_zero)
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ha0)] at i3
    intro h
    have := AddSubgroup.relIndex_dvd_of_le_left G (show F.map (mulBy a) ≤ F from ?_)
    · rw [h] at this
      exact i3 (Nat.eq_zero_of_zero_dvd this)
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ frame (1 : Matrix (Fin n) (Fin n) L) := hx
      exact (frame (1 : Matrix (Fin n) (Fin n) L)).smul_mem a hx'

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalEndomorphism
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem hodgeTate_endo : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) :=
  @PositivityTheory.HtPt.Htat.ht_olin

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalMul
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isHT_mul_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') :=
  @PositivityTheory.HtPt.Htat.ht_add

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def LieChart {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
    (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
    (_ : Module.Projective (Localization.Away f) P)
    (m : ∀ (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C f) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C)),
    ∀ (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C f)) (hC' : IsUnit (algebraMap R C' f)) (c : C →ₐ[R] C') (w : P →ₗ[R] C),
      ((m C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m C hC).pt w).left

end GlobalTheory.CompanionTheory.Ar
end
end

