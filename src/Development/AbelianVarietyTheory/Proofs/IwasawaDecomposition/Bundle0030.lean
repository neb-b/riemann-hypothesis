module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem bijective_of_existsUnique_field_point {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) :
    Function.Bijective f := by
  constructor
  · intro x x' hx
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hx
    let p : Sp ((pullback f f).residueField z) ⟶ pullback f f :=
      (pullback f f).fromSpecResidueField z
    have e : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
      (h _ (p ≫ pullback.fst f f ≫ f)).unique (by simp) (by simp [pullback.condition])
    let a : Sp ((pullback f f).residueField z) := IsLocalRing.closedPoint _
    have ha : p a = z := Scheme.fromSpecResidueField_apply z a
    have e' : (p ≫ pullback.fst f f) a = (p ≫ pullback.snd f f) a := by rw [e]
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, hz, hz'] at e'
  · intro t
    obtain ⟨z, hz, -⟩ := h (T.residueField t) (T.fromSpecResidueField t)
    let a : Sp (T.residueField t) := IsLocalRing.closedPoint _
    refine ⟨z a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecResidueField_apply t a

theorem existsUnique_field_point_morphismRestrict {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by
  obtain ⟨z, hz, hu⟩ := h k (w ≫ V.ι)
  have P := (isPullback_morphismRestrict f V).flip
  refine ⟨P.lift z w hz, P.lift_snd _ _ _, fun y hy ↦ ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    apply hu
    show (y ≫ _) ≫ f = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
  · rw [P.lift_snd]; exact hy

theorem isIso_stalkMap_genericPoint_of_lift {S T : Scheme.{0}} (f : S ⟶ T) [IsIntegral S]
    [IsIntegral T] [IsDominant f] (hf : Function.Injective f)
    (z : Spec T.functionField ⟶ S) (hz : z ≫ f = T.fromSpecStalk (genericPoint T)) :
    IsIso (f.stalkMap (genericPoint S)) := by
  have hs : z (IsLocalRing.closedPoint _) = genericPoint S := by
    apply hf
    rw [apply_genericPoint_of_isDominant f]
    refine (Scheme.Hom.comp_apply z f _).symm.trans ?_
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  have hF : IsField (S.presheaf.stalk (z (IsLocalRing.closedPoint _))) := by
    rw [hs]; exact Field.toIsField S.functionField
  rw [← hs]
  have h1 : IsIso (Scheme.stalkClosedPointTo (z ≫ f)) := by
    rw [hz, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 : IsIso (Scheme.stalkClosedPointTo z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · letI := hF.toField
      exact (Scheme.stalkClosedPointTo z).hom.injective
    · intro y
      obtain ⟨x, hx⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 y
      exact ⟨_, hx⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Scheme.stalkClosedPointTo z) h2 h1

theorem isIso_of_isProper_of_existsUnique_field_point_of_isIntegral {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have hb := bijective_of_existsUnique_field_point f h
  have hh : IsHomeomorph f :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨f.continuous, f.isClosedMap, hb⟩
  have : IrreducibleSpace S := hh.homeomorph.symm.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have : IsDominant f := ⟨hb.2.denseRange⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    fun t ↦ (Set.finite_singleton t).preimage hb.1.injOn
  obtain ⟨z, hz, -⟩ := h T.functionField (T.fromSpecStalk (genericPoint T))
  have := isIso_stalkMap_genericPoint_of_lift f hb.1 z hz
  exact isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f fun _ ↦ inferInstance

theorem isIso_of_isProper_of_existsUnique_field_point (S T : Scheme.{0}) (f : S ⟶ T)
    (hf : IsProper f) (hS : IsReduced S) (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T)
    (hN : IsLocallyNoetherian T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hT
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    GlobalTheory.IsNormalScheme.component (@GlobalTheory.IsNormalScheme.iSup_component T _ _)).mpr fun Z ↦ ?_
  exact isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
    (f ∣_ GlobalTheory.IsNormalScheme.component Z) (existsUnique_field_point_morphismRestrict f h _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuation
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem place_unique [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

theorem normSq_eq [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨a, b', ha, hb, ha1, hb1, hab⟩ :=
      (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB
    have hmem : b' ∈ Ideal.span {a} := by
      have : b' ∈ Ideal.span {a} * (I * B) := by
        rw [hab]; exact Ideal.mem_span_singleton_self b'
      exact Ideal.mul_le_left this
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_, ?_⟩
    · have hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [mul_comm, hx]; exact hb1
      have : x - 1 = (a * x - 1) - (a - 1) * x := by ring
      rw [this]
      exact Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)
    · have hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x} := by
        rw [hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
      have ha' : Ideal.span {a} ≠ 0 := by
        rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact ha
      exact (mul_left_cancel₀ ha' hspan).symm
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

theorem lattice_bij (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [Ideal.mul_eq_inf_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
        {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} ≃
        {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}},
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1 * B := by
  classical
  have hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c},
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B := fun I =>
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2
  choose g hg1 hg using hgen
  have hgB : ∀ I, g I ∈ B := fun I => by
    have : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at this
    exact Ideal.mul_le_right this
  have hg0 : ∀ I, g I ≠ 0 := fun I h => by
    have := hg I
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm
  let F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
      {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} →
      {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} := fun p =>
    ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by
      have : (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B := fun p => by
    show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]
  have hinj : Function.Injective F := by
    rintro ⟨I, u⟩ ⟨I', u'⟩ h
    have h1 := hspanF (I, u)
    rw [h, hspanF (I', u')] at h1
    have hII : I = I' := Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)
    subst hII
    have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := congrArg Subtype.val h
    have h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K) := mul_right_cancel₀ (hg0 I) h2
    rw [Subtype.ext (Units.ext h3)]
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hxB, hx1⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hM
      rw [Ideal.eq_top_iff_one]
      have := (Ideal.neg_mem_iff _).2 hx1
      simpa using this
    have hle : Ideal.span {x} ≤ B := (Ideal.span_singleton_le_iff_mem _).2 hxB
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
    have hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = x - (x - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
        (Ideal.mem_sup_right hx1)
    have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      rw [hI] at hxc; exact hxc.of_mul_left_right
    have hIB : Ideal.span {x} = I * B := by rw [hI, mul_comm]
    have hIcls : D.cls I = c :=
      (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩
    let I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} :=
      ⟨I, hIc, hIcls⟩
    have hass : Associated (g I') x := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I', hIB]
    obtain ⟨u, hu⟩ := hass
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [hu]; exact hx1
      have : (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u := by ring
      rw [this]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))
    refine ⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩
    show (u : 𝓞 K) * g I' = x
    rw [mul_comm, hu]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩

end GlobalTheory.Mem.PartialZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ (fun _ => ℝ) 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ (fun _ => ℝ) a.succ
    exact (ih fun a => I a.succ).comp h

theorem smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  intro G _ M _ ι c hc hM hcont
  let V := Fin (Module.finrank ℂ M) → ℂ
  let Φ : M ≃L[ℂ] V := (Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv
  let ρ : ι → ℝ → (M →ₗ[ℂ] M) := fun i t =>
    { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R : ι → ℝ → (V →L[ℂ] V) := fun i t =>
    LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v)) := fun _ _ _ => rfl
  let ev : G → (V →L[ℂ] ℂ) := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hev : ∀ g v, ev g v = (Φ.symm v).1 g := fun _ _ => rfl
  have hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v := by
    intro g i t v
    rw [hev, hRapp, Φ.symm_apply_apply]
    rfl
  have hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w := by
    intro v w h
    apply Φ.symm.injective
    exact Subtype.ext (funext h)
  have hc0 : ∀ i, c i 0 = 1 := by
    intro i
    have := hc i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hR : ∀ i, ContDiff ℝ ∞ (R i) := by
    intro i
    refine GlobalTheory.T.contDiff_of_continuous_oneParameter_hom _ (R i) ?_ ?_ ?_
    · refine continuous_clm_apply.2 fun v => ?_
      simp only [hRapp]
      refine Φ.continuous.comp ?_
      exact Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _
    · refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [hkey, hc0, mul_one]; rfl
    · intro s t
      refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]
  have hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩) := by
    intro f hf g
    rw [hev, Φ.symm_apply_apply]
  refine ⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩
  · have hd : HasDerivAt (R i) (deriv (R i) 0) 0 :=
      ((hR i).differentiable (by simp) 0).hasDerivAt
    have : (fun g => deriv (fun t : ℝ => f (g * c i t)) 0)
        = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1 := by
      funext g
      rw [← hev]
      have h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩)) := by
        funext t
        rw [hkey, ← hf]
      rw [h1]
      let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
      exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv
    rw [this]
    exact Subtype.property _
  · have hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V),
        ev g ((List.ofFn fun a => R (I a) (t a)).prod v)
          = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v := by
      intro k
      induction k with
      | zero => intro I t g v; simp
      | succ k ih =>
        intro I t g v
        simp only [List.ofFn_succ, List.prod_cons]
        rw [ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ),
          mul_assoc]
    have h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod))
        = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩)) := by
      funext t
      rw [hprod, ← hf]
    rw [h1]
    let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
    exact (L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)

end GlobalTheory
end

